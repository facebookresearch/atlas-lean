/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `4a7de6097bb263f2effe26503114c03ea2051591`.

Original formalization by Adam Kiezun, except the FactorizesOver definition
and the moral-graph bridge argument, adapted from MarkovRandomField.lean
by vonbers (@vonbo) and Avocado; ported with attribution.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.MarkovRandomField
public import CSLibExt.MachineLearning.GraphicalModels.BayesianNetwork
public import MathlibExt.Combinatorics.Digraph.PathCover
public import MathlibExt.Combinatorics.SimpleGraph.SeparatorAPI
public import Mathlib.Combinatorics.Digraph.Orientation

/-!
# d-separation is sound for Bayesian network factorizations

Random variables indexed by the vertices of a finite directed acyclic graph `G` (a Mathlib
`Digraph` with MathlibExt's acyclicity (`Digraph.IsAcyclic`); `G.Adj u v` is the edge `u → v`, so `u` is a parent of `v`)
take values in a finite type `α`.

* `FactorizesOverDAG G p`: `p = ∏ v, f v`, where each factor depends only on `v` and its parents
  and is normalized in `v`: `∑ a, f v (update x v a) = 1`. A Bayesian network is the case of
  nonnegative factors (conditional probability tables), when `p` is a probability distribution;
  the results below do not need nonnegativity.
* `Trail G u w`: a trail from `u` to `w`, a sequence of vertices in which consecutive vertices are
  joined by an edge in either direction, i.e. a Mathlib `SimpleGraph.Walk` in the skeleton
  `G.toSimpleGraphInclusive`. A vertex of a trail is a **collider** (`IsCollider`) when
  both of its trail-neighbours are its parents (`→ v ←`). `Trail.IsActive S`: every collider has a
  descendant in `S` (itself included), and every other vertex, endpoints included, is outside
  `S`. `DSeparated G A B S`: no trail from `A` to `B` is active given `S` (Koller and Friedman,
  Section 3.3.1).
* `FactorizesOverDAG.condIndep` (**soundness of d-separation**): if `p` factorizes over `G` and
  `S` d-separates `A` from `B`, then `CondIndep p A B S` (MathlibExt's `FiniteWeight.CondIndep`).
  For a Bayesian network this says that the variables in `A` and in `B` are conditionally
  independent given those in `S`. `BayesNet.condIndep_of_dSeparated_trail` applies it to the joint
  distribution of a `BayesNet` (`BayesianNetwork.lean`), over the DAG `BayesNet.dag` of its parent
  sets.

The proof follows Lauritzen et al. (1990).
* `marginal_eq_prod_of_ancestral`: summing out the vertices outside an ancestral set `W` (one that
  contains the parents of its vertices) leaves `∏ v ∈ W, f v`, since a vertex without children
  appears in one factor only, which sums to `1`.
* That product factorizes over the moral graph `moralGraph G W` (two vertices are adjacent when
  both lie in the family, a vertex and its parents, of some vertex of `W`), so the global Markov
  property (proved here from the factorization, via the moral-graph bridge below) applies to it.
* `separatesAB_moralGraph_of_dSeparated`: if `S` d-separates `A` from `B`, then it separates them
  (MathlibExt's `SeparatesAB`) in the moral graph of the ancestral closure `ancestors G (A ∪ B ∪
  S)`. A walk in the moral graph avoiding `S` is turned into an active trail: an edge between two
  co-parents becomes a collider at their common child, and a collider without a descendant in `S`
  has a descendant in `A ∪ B`, from which the trail is restarted or at which it ends.

Trails may revisit vertices. Restricting to simple trails (`SimpleGraph.Walk.IsPath`) gives the
same d-separation relation (an active trail can be shortened to a simple active trail); that
equivalence is not formalized here, so the theorem assumes d-separation for all trails.

## References

* D. Koller and N. Friedman, *Probabilistic Graphical Models*, MIT Press, 2009, Section 3.3.
* S. L. Lauritzen, A. P. Dawid, B. N. Larsen and H.-G. Leimer, Independence properties of
  directed Markov fields, *Networks* 20 (1990), 491–505.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

open Finset MetaMathlibExt.FiniteWeight MathlibExt.Combinatorics.SimpleGraph.SeparatorAPI
  MathlibExt.Combinatorics.Digraph.PathCoverWanted

universe u

variable {V : Type u} {α : Type*}

/-! ### Trails and d-separation -/

section Trails

variable (G : Digraph V)

/-- A trail in `G` from `u` to `w`: a walk in the skeleton of `G` (Mathlib's
`Digraph.toSimpleGraphInclusive`), so consecutive vertices are joined by an edge in either
direction. Vertices may repeat. -/
abbrev Trail (u w : V) : Type u :=
  G.toSimpleGraphInclusive.Walk u w

/-- A vertex `u` of a trail, with previous vertex `p` and next vertex `n` (`none` at an
endpoint), is a **collider** when both trail-neighbours are parents of `u`. -/
def IsCollider (p : Option V) (u : V) (n : Option V) : Prop :=
  ∃ q ∈ p, ∃ x ∈ n, G.Adj q u ∧ G.Adj x u

variable {G}

/-- The second vertex of a trail, if any. -/
def Trail.next : {u w : V} → Trail G u w → Option V
  | _, _, .nil => none
  | _, _, .cons (v := v) _ _ => some v

/-- `Trail.ActiveFrom S p t`: every vertex of the trail `t` satisfies the activity condition
given `S`, when the vertex before `t` is `p` (`none` if `t` is the whole trail): a collider has a
descendant in `S` (itself included), and every other vertex is outside `S`. -/
def Trail.ActiveFrom (S : Finset V) : Option V → {u w : V} → Trail G u w → Prop
  | _, u, _, .nil => u ∉ S
  | p, u, _, .cons (v := x) _ t =>
      (IsCollider G p u (some x) → ∃ s ∈ S, Relation.ReflTransGen G.Adj u s) ∧
        (¬IsCollider G p u (some x) → u ∉ S) ∧ Trail.ActiveFrom S (some u) t

/-- A trail is **active** given `S`: every collider on it has a descendant in `S`, and every
other vertex (the endpoints included) is outside `S`. -/
def Trail.IsActive (S : Finset V) {u w : V} (t : Trail G u w) : Prop :=
  Trail.ActiveFrom S none t

variable (G) in
/-- `S` **d-separates** `A` from `B` in `G`: no trail from a vertex of `A` to a vertex of `B` is
active given `S`. -/
def DSeparated (A B : Set V) (S : Finset V) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ∀ t : Trail G a b, ¬Trail.IsActive S t

/-- The activity condition on the part of a trail after its first vertex. -/
def Trail.TailActive (S : Finset V) : {u w : V} → Trail G u w → Prop
  | _, _, .nil => True
  | u, _, .cons _ t => Trail.ActiveFrom S (some u) t

theorem Trail.activeFrom_iff {S : Finset V} {p : Option V} {u w : V} (t : Trail G u w) :
    Trail.ActiveFrom S p t ↔
      (IsCollider G p u (Trail.next t) → ∃ s ∈ S, Relation.ReflTransGen G.Adj u s) ∧
        (¬IsCollider G p u (Trail.next t) → u ∉ S) ∧ Trail.TailActive S t := by
  cases t with
  | nil => simp [ActiveFrom, IsCollider, next, TailActive]
  | cons h t => rfl

theorem Trail.isActive_iff {S : Finset V} {u w : V} (t : Trail G u w) :
    Trail.IsActive S t ↔ u ∉ S ∧ Trail.TailActive S t := by
  rw [IsActive, activeFrom_iff]
  simp [IsCollider]

/-- An edge of `G` is an edge of its skeleton. -/
private theorem skeleton_adj (hG : G.IsAcyclic) {u v : V} (h : G.Adj u v ∨ G.Adj v u) :
    G.toSimpleGraphInclusive.Adj u v := by
  rw [Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj]
  refine ⟨fun huv => ?_, h⟩
  subst huv
  exact hG u (.single (h.elim id id))

private theorem not_isCollider_of_adj (hG : G.IsAcyclic) {q u : V} (h : G.Adj u q) (n : Option V) :
    ¬IsCollider G (some q) u n := by
  rintro ⟨q', hq', -, -, hqu, -⟩
  cases Option.mem_some_iff.mp hq'
  exact hG u (.tail (.single h) hqu)

private theorem not_isCollider_of_next {p : Option V} {u : V} {n : Option V}
    (h : ∀ x ∈ n, ¬G.Adj x u) : ¬IsCollider G p u n := by
  rintro ⟨-, -, x, hx, -, hxu⟩
  exact h x hx hxu

/-- Prepending a child of the first vertex keeps the trail active after its new first vertex. -/
private theorem tailActive_cons_child (hG : G.IsAcyclic) {S : Finset V} {d e w : V} (h : G.Adj e d)
    {t : Trail G e w} (he : e ∉ S) (ht : Trail.TailActive S t) :
    Trail.TailActive S (SimpleGraph.Walk.cons (skeleton_adj hG (Or.inr h)) t : Trail G d w) :=
  (Trail.activeFrom_iff t).mpr ⟨fun hc => absurd hc (not_isCollider_of_adj hG h _), fun _ => he, ht⟩

end Trails

/-! ### From moral separation to d-separation -/

section Moral

variable [Fintype V] (G : Digraph V)

open Classical in
/-- The ancestral closure of `X`: the vertices with a descendant in `X` (`X` included). -/
noncomputable def ancestors (X : Set V) : Finset V :=
  univ.filter fun v => ∃ x ∈ X, Relation.ReflTransGen G.Adj v x

/-- The moral graph of `G` on `W`: distinct vertices are adjacent when both lie in the family
(the vertex and its parents) of some vertex of `W`. For an ancestral `W` this is the moral graph
of the subgraph of `G` induced on `W`. -/
def moralGraph (W : Finset V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ c ∈ W, (u = c ∨ G.Adj u c) ∧ (v = c ∨ G.Adj v c)
  symm := ⟨fun _ _ ⟨h, c, hc, hu, hv⟩ => ⟨h.symm, c, hc, hv, hu⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

variable {G}

theorem mem_ancestors {X : Set V} {v : V} :
    v ∈ ancestors G X ↔ ∃ x ∈ X, Relation.ReflTransGen G.Adj v x := by
  simp [ancestors]

theorem parent_mem_ancestors {X : Set V} {u v : V} (h : G.Adj u v) (hv : v ∈ ancestors G X) :
    u ∈ ancestors G X := by
  obtain ⟨x, hx, hvx⟩ := mem_ancestors.mp hv
  exact mem_ancestors.mpr ⟨x, hx, .head h hvx⟩

variable {A B : Set V} {S : Finset V}

/-- The front of a partial trail towards `B`: an active-after-its-first-vertex trail from `v`
to `B`, with `v` outside `S`. -/
private def Front (G : Digraph V) (B : Set V) (S : Finset V) (v : V) : Prop :=
  ∃ b ∈ B, ∃ t : Trail G v b, v ∉ S ∧ Trail.TailActive S t

/-- An active trail from `A` to `B`. -/
private def Connected (G : Digraph V) (A B : Set V) (S : Finset V) : Prop :=
  ∃ a ∈ A, ∃ b ∈ B, ∃ t : Trail G a b, Trail.IsActive S t

omit [Fintype V] in
/-- Going up from a descendant `d` of `c` to `c` and on along a trail from `c`, when `c` has no
descendant in `S`. -/
private theorem front_of_descendant (hG : G.IsAcyclic) {c d w : V}
    (hcd : Relation.ReflTransGen G.Adj c d) (hS : ∀ s ∈ S, ¬Relation.ReflTransGen G.Adj c s)
    (t : Trail G c w) (ht : Trail.TailActive S t) :
    ∃ t' : Trail G d w, d ∉ S ∧ Trail.TailActive S t' := by
  induction hcd with
  | refl => exact ⟨t, fun h => hS c h .refl, ht⟩
  | tail hce hed ih =>
    obtain ⟨t', he, ht'⟩ := ih
    exact ⟨.cons (skeleton_adj hG (Or.inr hed)) t', fun h => hS _ h (hce.tail hed),
      tailActive_cons_child hG hed he ht'⟩

omit [Fintype V] in
/-- Going down from `c` to a descendant `d` with no descendant of `c` in `S`. -/
private theorem down_trail (hG : G.IsAcyclic) {c d : V} (hcd : Relation.ReflTransGen G.Adj c d)
    (hS : ∀ s ∈ S, ¬Relation.ReflTransGen G.Adj c s) :
    ∃ t : Trail G c d, c ∉ S ∧ Trail.TailActive S t ∧ ∀ x ∈ (Trail.next t), ¬G.Adj x c := by
  induction hcd using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨.nil, fun h => hS _ h .refl, trivial, by simp [Trail.next]⟩
  | head hce hed ih =>
    rename_i c e
    obtain ⟨t, he, ht, hn⟩ := ih fun s hs h => hS s hs (.head hce h)
    refine ⟨.cons (skeleton_adj hG (Or.inl hce)) t, fun h => hS _ h .refl, ?_, ?_⟩
    · exact (Trail.activeFrom_iff t).mpr
        ⟨fun hc => absurd hc (not_isCollider_of_next hn), fun _ => he, ht⟩
    · intro x hx hxc
      cases Option.mem_some_iff.mp hx
      exact hG c (.tail (.single hce) hxc)

omit [Fintype V] in
/-- Prepending a parent `u` of the first vertex `v`, restarting at a descendant of `v` in `A`
or `B` when `v` becomes a collider without a descendant in `S`. -/
private theorem front_cons_parent (hG : G.IsAcyclic) {u v b : V}
    (hvW : ∃ d ∈ A ∪ B ∪ (S : Set V), Relation.ReflTransGen G.Adj v d) (h : G.Adj u v)
    (hu : u ∉ S) (hb : b ∈ B) (t : Trail G v b) (ht : Trail.TailActive S t)
    (hv : v ∉ S ∨ IsCollider G (some u) v (Trail.next t)) : Front G B S u ∨ Connected G A B S := by
  by_cases hc : IsCollider G (some u) v (Trail.next t)
  · by_cases hs : ∃ s ∈ S, Relation.ReflTransGen G.Adj v s
    · exact .inl ⟨b, hb, .cons (skeleton_adj hG (Or.inl h)) t, hu,
        (Trail.activeFrom_iff t).mpr ⟨fun _ => hs, fun h' => absurd hc h', ht⟩⟩
    · push Not at hs
      obtain ⟨d, hd, hvd⟩ := hvW
      have hdS : d ∉ (S : Set V) := fun h' => hs d h' hvd
      rcases hd with (hdA | hdB) | hdS'
      · obtain ⟨t', hd', ht'⟩ := front_of_descendant hG hvd hs t ht
        exact .inr ⟨d, hdA, b, hb, t', (Trail.isActive_iff t').mpr ⟨hd', ht'⟩⟩
      · obtain ⟨t', hv', ht', hn⟩ := down_trail hG hvd hs
        exact .inl ⟨d, hdB, .cons (skeleton_adj hG (Or.inl h)) t', hu, (Trail.activeFrom_iff t').mpr
          ⟨fun hc' => absurd hc' (not_isCollider_of_next hn), fun _ => hv', ht'⟩⟩
      · exact absurd hdS' hdS
  · have hv' : v ∉ S := hv.resolve_right hc
    exact .inl ⟨b, hb, .cons (skeleton_adj hG (Or.inl h)) t, hu,
      (Trail.activeFrom_iff t).mpr ⟨fun h' => absurd h' hc, fun _ => hv', ht⟩⟩

/-- A walk in the moral graph of the ancestral closure that avoids `S` and ends in `B` gives a
front at its first vertex or an active trail from `A` to `B`. -/
private theorem front_of_walk (hG : G.IsAcyclic) {v b : V} (hb : b ∈ B)
    (p : (moralGraph G (ancestors G (A ∪ B ∪ (S : Set V)))).Walk v b)
    (hp : ∀ x ∈ p.support, x ∉ S) : Front G B S v ∨ Connected G A B S := by
  induction p with
  | nil => exact .inl ⟨_, hb, .nil, hp _ (by simp), trivial⟩
  | @cons u v' w hadj p ih =>
    have hu : u ∉ S := hp u (by simp)
    rcases ih hb fun x hx => hp x (by simp [hx]) with
      ⟨b', hb', t, hv', ht⟩ | hconn
    · obtain ⟨hne, c, hcW, hu', hv''⟩ := hadj
      have hcW' := mem_ancestors.mp hcW
      rcases hu' with rfl | huc
      · rcases hv'' with rfl | hvc
        · exact absurd rfl hne
        · exact .inl ⟨b', hb', .cons (skeleton_adj hG (Or.inr hvc)) t, hu,
            tailActive_cons_child hG hvc hv' ht⟩
      · rcases hv'' with rfl | hvc
        · exact front_cons_parent hG hcW' huc hu hb' t ht (.inl hv')
        · exact front_cons_parent hG hcW' huc hu hb' (.cons (skeleton_adj hG (Or.inr hvc)) t)
            (tailActive_cons_child hG hvc hv' ht)
            (.inr ⟨u, rfl, v', rfl, huc, hvc⟩)
    · exact .inr hconn

/-- **d-separation implies moral separation**: if `S` d-separates `A` from `B`, then `S`
separates `A` from `B` in the moral graph of the ancestral closure of `A ∪ B ∪ S`. -/
theorem separatesAB_moralGraph_of_dSeparated (hG : G.IsAcyclic) (h : DSeparated G A B S) :
    SeparatesAB (moralGraph G (ancestors G (A ∪ B ∪ (S : Set V)))) A B S := by
  intro a b ha hb p
  by_contra hp
  push Not at hp
  rcases front_of_walk hG hb p hp with ⟨b', hb', t, ha', ht⟩ | ⟨a', ha', b', hb', t, ht⟩
  · exact h a ha b' hb' t ((Trail.isActive_iff t).mpr ⟨ha', ht⟩)
  · exact h a' ha' b' hb' t ht

end Moral

/-! ### Bayesian network factorizations -/

section Factorization

variable [Fintype V] [DecidableEq V] [Fintype α] {G : Digraph V}

variable (G) in
/-- `p` **factorizes over the DAG** `G`: `p = ∏ v, f v`, where each factor depends only on `v`
and its parents and is normalized in `v`. (A Bayesian network is the case of nonnegative
factors, the conditional probability tables.) -/
def FactorizesOverDAG (p : (V → α) → ℝ) : Prop :=
  ∃ f : V → (V → α) → ℝ, (∀ v, DependsOn (f v) (insert v {u | G.Adj u v})) ∧
    (∀ v x, ∑ a, f v (Function.update x v a) = 1) ∧ p = ∏ v, f v

/-- `p` **factorizes over the cliques of** `G`: it is a finite product of real factors, each
depending only on the variables of a clique of `G`. This is the factorization predicate of
`MarkovRandomField.lean` in formal-math, adapted here because the Atlas development there now
uses Gibbs factorizations instead; the results below do not need nonnegativity. -/
def FactorizesOver [Fintype V] [DecidableEq V] [Fintype α] (G : SimpleGraph V)
    (p : (V → α) → ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (C : ι → Set V) (ψ : ι → (V → α) → ℝ),
    (∀ i, G.IsClique (C i)) ∧ (∀ i, DependsOn (ψ i) (C i)) ∧ p = ∏ i, ψ i

/-- A product of factors, each depending only on variables in `P`, depends only on `P`. -/
private theorem dependsOn_prod {ι : Type*} (s : Finset ι) {ψ : ι → (V → α) → ℝ}
    {C : ι → Set V} {P : Set V} (hψ : ∀ i, DependsOn (ψ i) (C i)) (hC : ∀ i ∈ s, C i ⊆ P) :
    DependsOn (∏ i ∈ s, ψ i) P := by
  intro x y hxy
  simp only [Finset.prod_apply]
  exact prod_congr rfl fun i hi => hψ i fun v hv => hxy v (hC i hi hv)

/-- Walk-hitting separation in finset form implies set-form separation. -/
private theorem separatesAB_to_separatedBy {G : SimpleGraph V} {A B : Set V} {X : Finset V}
    (h : SeparatesAB G A B X) : G.SeparatedBy A B (↑X : Set V) := by
  intro a b ha hb w
  obtain ⟨u, hu, huX⟩ := h a b ha hb w
  exact ⟨u, Finset.mem_coe.mpr huX, hu⟩

/-- **Global Markov property for clique factorizations**: if `p` factorizes over the cliques of
`G`, then separation in `G` implies conditional independence. The proof splits the factors
into those inside `P` and the rest, following the `GlobalMarkov` argument in
`MarkovRandomField.lean`. -/
private theorem factorizesOver_globalMarkov {G : SimpleGraph V} {p : (V → α) → ℝ}
    [Fintype V] [DecidableEq V] [Fintype α] (hp : FactorizesOver G p) :
    GlobalMarkov G p := by
  classical
  obtain ⟨ι, _, C, ψ, hC, hψ, rfl⟩ := hp
  intro A B S hsep
  let R : Set V := {v | ∃ a ∈ A, ∃ w : G.Walk a v, ∀ u ∈ w.support, u ∉ S}
  have hRS' : ∀ v ∈ R, v ∉ S := fun v ⟨_, _, w, hw⟩ => hw v w.end_mem_support
  have hclique : ∀ i, (∃ c ∈ C i, c ∈ R) → C i ⊆ R ∪ S := by
    rintro i ⟨c, hc, a, ha, w, hw⟩ c' hc'
    by_cases hc'S : c' ∈ S
    · exact Or.inr hc'S
    left
    by_cases hcc' : c = c'
    · exact hcc' ▸ ⟨a, ha, w, hw⟩
    refine ⟨a, ha, w.concat (hC i hc hc' hcc'), fun u hu => ?_⟩
    rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hu
    rcases hu with hu | rfl
    · exact hw u hu
    · exact hc'S
  set P : Set V := R ∪ S
  set Q : Set V := Rᶜ
  have hPQ : ∀ v, v ∈ P ∨ v ∈ Q := fun v => by
    by_cases hv : v ∈ R
    · exact Or.inl (Or.inl hv)
    · exact Or.inr hv
  have hS : P ∩ Q = S := by
    ext v
    simp only [P, Q, Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff]
    constructor
    · rintro ⟨h | h, hR⟩
      · exact absurd h hR
      · exact h
    · exact fun h => ⟨Or.inr h, fun hR => hRS' v hR h⟩
  have hsplit : (∏ i, ψ i) = (∏ i ∈ univ.filter (fun i => C i ⊆ P), ψ i) *
      ∏ i ∈ univ.filter (fun i => ¬C i ⊆ P), ψ i :=
    (prod_filter_mul_prod_filter_not univ _ _).symm
  have hf : DependsOn (∏ i ∈ univ.filter (fun i => C i ⊆ P), ψ i) P :=
    dependsOn_prod _ hψ fun i hi => (mem_filter.mp hi).2
  have hg : DependsOn (∏ i ∈ univ.filter (fun i => ¬C i ⊆ P), ψ i) Q := by
    refine dependsOn_prod _ hψ fun i hi c hc hcR => ?_
    exact (mem_filter.mp hi).2 (hclique i ⟨c, hc, hcR⟩)
  have hA : ∀ v ∈ A \ S, v ∉ Q := fun v ⟨hvA, hvS⟩ => by
    simp only [Q, Set.mem_compl_iff, not_not]
    refine ⟨v, hvA, SimpleGraph.Walk.nil, fun u hu => ?_⟩
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hu
    exact hu ▸ hvS
  have hB : ∀ v ∈ B \ S, v ∉ P := by
    rintro v ⟨hvB, hvS⟩ (⟨a, ha, w, hw⟩ | hv)
    · obtain ⟨u, huS, hu⟩ := hsep ha hvB w
      exact hw u hu huS
    · exact hvS hv
  have h := condIndep_of_dependsOn hf hg hPQ hA hB
  rw [hS, ← hsplit] at h
  exact condIndep_of_sdiff h


open Classical in
/-- Summing the factors of an ancestral set `T` over the vertices of `T` outside a smaller
ancestral set `W` leaves the factors of `W`. -/
private theorem sum_prod_of_ancestral (hG : G.IsAcyclic) {f : V → (V → α) → ℝ}
    (hf : ∀ v, DependsOn (f v) (insert v {u | G.Adj u v}))
    (hnorm : ∀ v x, ∑ a, f v (Function.update x v a) = 1) :
    ∀ (n : ℕ) (T W : Finset V), (T \ W).card = n → W ⊆ T →
      (∀ v ∈ W, ∀ u, G.Adj u v → u ∈ W) → (∀ v ∈ T, ∀ u, G.Adj u v → u ∈ T) → ∀ x : V → α,
      ∑ y ∈ univ.filter (fun y : V → α => ∀ v, v ∈ W ∨ v ∉ T → y v = x v), ∏ v ∈ T, f v y =
        ∏ v ∈ W, f v x := by
  intro n
  induction n with
  | zero =>
    intro T W hn hWT _ _ x
    have hTW : T = W := le_antisymm (sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp hn)) hWT
    subst hTW
    rw [sum_eq_single_of_mem x (by simp)]
    intro y hy hyx
    exact absurd (funext fun v => (mem_filter.mp hy).2 v (by tauto)) hyx
  | succ n ih =>
    intro T W hn hWT hW hT x
    -- a vertex of `T \ W` without children in `T`
    have hwf : WellFounded fun a b : V => Relation.TransGen G.Adj b a := by
      have : IsTrans V fun a b : V => Relation.TransGen G.Adj b a :=
        ⟨fun _ _ _ h₁ h₂ => h₂.trans h₁⟩
      have : Std.Irrefl fun a b : V => Relation.TransGen G.Adj b a := ⟨fun a h => hG a h⟩
      exact Finite.wellFounded_of_trans_of_irrefl _
    obtain ⟨u, huTW, hmin⟩ := hwf.has_min (↑(T \ W) : Set V)
      (nonempty_of_ne_empty (by rintro h; simp [h] at hn)).to_set
    have huT : u ∈ T := (mem_sdiff.mp huTW).1
    have huW : u ∉ W := (mem_sdiff.mp huTW).2
    have hchild : ∀ c ∈ T, ¬G.Adj u c := fun c hc huc => by
      by_cases hcW : c ∈ W
      · exact huW (hW c hcW u huc)
      · exact hmin c (mem_sdiff.mpr ⟨hc, hcW⟩) (.single huc)
    set T' := T.erase u
    have key := ih T' W (by rw [erase_sdiff_comm, card_erase_of_mem huTW, hn]; rfl)
      (fun v hv => mem_erase.mpr ⟨fun h => huW (h ▸ hv), hWT hv⟩) hW
      (fun v hv w hwv => mem_erase.mpr ⟨fun h => hchild v (mem_of_mem_erase hv) (h ▸ hwv),
        hT v (mem_of_mem_erase hv) w hwv⟩) x
    rw [← key]
    -- the factors other than `f u` do not involve `u`
    have hR : ∀ (z : V → α) (a : α), ∏ v ∈ T', f v (Function.update z u a) = ∏ v ∈ T', f v z :=
      fun z a => prod_congr rfl fun v hv => hf v fun i hi => by
        have hiu : i ≠ u := by
          rintro rfl
          rcases hi with hi | hi
          · exact (ne_of_mem_erase hv) hi.symm
          · exact hchild v (mem_of_mem_erase hv) hi
        exact Function.update_of_ne hiu a z
    have hsplit : ∀ y : V → α, ∏ v ∈ T, f v y = f u y * ∏ v ∈ T', f v y := fun y =>
      (mul_prod_erase T (fun v => f v y) huT).symm
    simp_rw [hsplit]
    calc ∑ y ∈ univ.filter (fun y : V → α => ∀ v, v ∈ W ∨ v ∉ T → y v = x v),
          f u y * ∏ v ∈ T', f v y
        = ∑ p ∈ (univ.filter fun z : V → α => ∀ v, v ∈ W ∨ v ∉ T' → z v = x v) ×ˢ
            (univ : Finset α), f u (Function.update p.1 u p.2) *
              ∏ v ∈ T', f v (Function.update p.1 u p.2) := by
          refine sum_nbij' (fun y => (Function.update y u (x u), y u))
            (fun p => Function.update p.1 u p.2) ?_ ?_ ?_ ?_ ?_
          · intro y hy
            simp only [mem_filter, mem_univ, true_and] at hy
            simp only [mem_product, mem_filter, mem_univ, true_and, and_true]
            intro v hv
            by_cases hvu : v = u
            · subst hvu
              simp
            · rw [Function.update_of_ne hvu]
              exact hy v (hv.imp_right fun h h' => h (mem_erase.mpr ⟨hvu, h'⟩))
          · intro p hp
            simp only [mem_product, mem_filter, mem_univ, true_and, and_true] at hp
            simp only [mem_filter, mem_univ, true_and]
            intro v hv
            by_cases hvu : v = u
            · subst hvu
              rcases hv with hv | hv
              · exact absurd hv huW
              · exact absurd huT hv
            · rw [Function.update_of_ne hvu]
              exact hp v (hv.imp_right fun h h' => h (mem_of_mem_erase h'))
          · intro y _
            simp
          · intro p hp
            simp only [mem_product, mem_filter, mem_univ, true_and, and_true] at hp
            have hpu : p.1 u = x u := hp u (Or.inr (fun h => (ne_of_mem_erase h) rfl))
            ext
            · simp [← hpu]
            · simp
          · intro y _
            simp
      _ = ∑ z ∈ univ.filter (fun z : V → α => ∀ v, v ∈ W ∨ v ∉ T' → z v = x v),
            ∏ v ∈ T', f v z := by
          rw [sum_product]
          refine sum_congr rfl fun z _ => ?_
          simp_rw [hR z, ← sum_mul, hnorm u z, one_mul]

/-- **Summing out the vertices outside an ancestral set**: the `W`-marginal of a factorization
over a DAG is the product of the factors of `W`. -/
theorem marginal_eq_prod_of_ancestral (hG : G.IsAcyclic) {f : V → (V → α) → ℝ}
    (hf : ∀ v, DependsOn (f v) (insert v {u | G.Adj u v}))
    (hnorm : ∀ v x, ∑ a, f v (Function.update x v a) = 1) {W : Finset V}
    (hW : ∀ v ∈ W, ∀ u, G.Adj u v → u ∈ W) :
    marginal (∏ v, f v) W = ∏ v ∈ W, f v := by
  classical
  funext x
  have h := sum_prod_of_ancestral hG hf hnorm _ univ W rfl (subset_univ W) hW
    (fun _ _ _ _ => mem_univ _) x
  simp only [mem_univ, not_true_eq_false, or_false] at h
  simp only [marginal, Finset.prod_apply, mem_coe, ← h]

/-- The product of the factors of `W` factorizes over the moral graph of `W`. -/
theorem factorizesOver_moralGraph (f : V → (V → α) → ℝ)
    (hf : ∀ v, DependsOn (f v) (insert v {u | G.Adj u v})) (W : Finset V) :
    FactorizesOver (moralGraph G W) (∏ v ∈ W, f v) := by
  refine ⟨Fin W.card, inferInstance, fun i => insert (W.equivFin.symm i : V) {u | G.Adj u
    (W.equivFin.symm i)}, fun i => f (W.equivFin.symm i), fun i => ?_, fun i => hf _, ?_⟩
  · intro u hu w hw huw
    exact ⟨huw, _, (W.equivFin.symm i).2, hu, hw⟩
  · funext x
    simp only [Finset.prod_apply]
    rw [← prod_coe_sort W]
    exact Fintype.prod_equiv W.equivFin _ _ fun v => by simp

/-- **Soundness of d-separation**: if `p` factorizes over the DAG `G` and `S` d-separates `A`
from `B`, then the variables in `A` and in `B` are conditionally independent given those in
`S`. -/
theorem FactorizesOverDAG.condIndep (hG : G.IsAcyclic) {p : (V → α) → ℝ}
    (hp : FactorizesOverDAG G p) {A B : Set V} {S : Finset V} (h : DSeparated G A B S) :
    CondIndep p A B S := by
  obtain ⟨f, hf, hnorm, rfl⟩ := hp
  set W := ancestors G (A ∪ B ∪ (S : Set V))
  have hW : ∀ v ∈ W, ∀ u, G.Adj u v → u ∈ W := fun v hv u huv => parent_mem_ancestors huv hv
  have hsub : ∀ X ⊆ A ∪ B ∪ (S : Set V), X ⊆ W := fun X hX v hv =>
    mem_ancestors.mpr ⟨v, hX hv, .refl⟩
  have hq := factorizesOver_globalMarkov (factorizesOver_moralGraph f hf W) A B (↑S : Set V)
    (separatesAB_to_separatedBy (separatesAB_moralGraph_of_dSeparated hG h))
  rw [← marginal_eq_prod_of_ancestral hG hf hnorm hW] at hq
  exact (condIndep_marginal_iff (hsub A (fun v hv => Or.inl (Or.inl hv)))
    (hsub B (fun v hv => Or.inl (Or.inr hv))) (hsub S (fun v hv => Or.inr hv))).mp hq

end Factorization

/-! ### The Bayesian networks of `BayesianNetwork.lean` -/

namespace BayesNet

variable [Nonempty α] {n : ℕ}

/-- The DAG of a Bayesian network: `j → k` when `j` is a parent of `k`. -/
def dag (b : BayesNet α n) : Digraph (Fin n) where
  Adj j k := ∃ h : (j : ℕ) < k, (⟨j, h⟩ : Fin k) ∈ b.pa k

omit [Nonempty α] in
theorem isAcyclic_dag (b : BayesNet α n) : (b.dag).IsAcyclic := by
  intro x hx
  have : ∀ a c, Relation.TransGen b.dag.Adj a c → a < c := fun a c h => by
    induction h with
    | single h => exact h.1
    | tail _ h ih => exact ih.trans h.1
  exact lt_irrefl x (this x x hx)

/-- The joint distribution of a Bayesian network factorizes over its DAG, with the conditional
probability tables as factors. -/
theorem factorizesOverDAG_joint [Fintype α] (b : BayesNet α n) :
    FactorizesOverDAG b.dag b.joint := by
  refine ⟨fun k x => (b.cpt k fun j => x (Fin.castLE k.2.le j)).weights (x k),
    fun k x y h => ?_, fun k x => ?_, ?_⟩
  · have hpa : (fun j : b.pa k => x (Fin.castLE k.2.le j)) =
        fun j : b.pa k => y (Fin.castLE k.2.le j) :=
      funext fun j => h _ (Set.mem_insert_of_mem _ ⟨j.1.2, j.2⟩)
    simp only [h k (Set.mem_insert _ _), hpa]
  · have hne : ∀ j : b.pa k, Fin.castLE k.2.le (j : Fin k) ≠ k := fun j h' =>
      absurd (congrArg Fin.val h') (ne_of_lt j.1.2)
    simp only [Function.update_self, Function.update_of_ne (hne _)]
    exact (b.cpt k _).total_of_fintype
  · funext x
    simp only [Finset.prod_apply]
    exact b.joint_eq_prod x

/-- **d-separation is sound for Bayesian networks**: if `S` d-separates `A` from `B` in the DAG of
a Bayesian network, then the variables in `A` and in `B` are conditionally independent given
those in `S` under its joint distribution. -/
theorem condIndep_of_dSeparated_trail [Fintype α] (b : BayesNet α n) {A B : Set (Fin n)}
    {S : Finset (Fin n)} (h : DSeparated b.dag A B S) : CondIndep b.joint A B S :=
  b.factorizesOverDAG_joint.condIndep b.isAcyclic_dag h

end BayesNet

end Cslib.MachineLearning.GraphicalModels
