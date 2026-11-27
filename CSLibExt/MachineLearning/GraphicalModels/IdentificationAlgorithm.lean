/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Adam Kiezun
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.LatentProjection
public import MathlibExt.Probability.FiniteWeight

/-!
# The ID identification recursion

The recursion of the ID algorithm (Shpitser and Pearl, "Identification of
joint interventional distributions in recursive semi-Markovian causal
models", AAAI 2006, Fig. 3, lines 1-7), as a function on finite vertex sets of
an acyclic directed mixed graph: `ADMG.ID` runs `ADMG.idRec` on the whole
vertex set with the observed law, returning either an identifying expression
(`IdExpr`, built from sums, products and conditionals of the observed law) or
the failure pair `(D, D \ X)` of line 5.

## Main definitions

* `IdExpr` and `IdExpr.eval`: the expression language and its evaluation
  against a finite weight.
* `ADMG.induce`, `ADMG.ancIn`, `ADMG.ancCut`, `ADMG.compIn`,
  `ADMG.cComponentsIn`: induced subgraphs, ancestors, ancestors after
  deleting arrows into `X`, and c-components inside a vertex set.
* `ADMG.condChain`: the conditional chain of lines 6 and 7 along an ordering
  `σ`.
* `ADMG.idRec`, `ADMG.ID`: the recursion itself and its top-level entry point.

## Main results

* `ADMG.cComponentsIn_partition`: the c-components of `G[D]` partition `D`.
* `ADMG.line4_guard_iff`, `ADMG.line5_guard_iff`: the line-4 and line-5
  guards as `k ≠ 1` and `C(G) = {G}` statements.
* `ADMG.idRec_invariants`: from a top-level disjoint pair, every recursive
  call keeps its arguments inside the current vertex set and disjoint.

The ordering `σ` is a parameter of the recursion, as in the source, where
`π` is a topological ordering fixed before the algorithm runs: `idRec` is
defined for every ordering, and only for a topological `σ` (directed edges
point forward) does the returned expression have its identifying reading.
Likewise the query sets are meant to be disjoint, as at the top-level calls
in the source; off that domain (overlapping `X`, `Y`, or a non-topological
`σ`) the recursion still returns a value, with no identification meaning:
for example `D \ X = ∅` falls into line 4 with an empty product, a case the
invariants exclude. Topologicity and disjointness are therefore hypotheses
of the results about the recursion (as in `ADMG.idRec_invariants`), not of
its definition. The identifying reading also needs the usual positivity:
every conditional in the returned expression must have a nonzero
denominator at the evaluation point. `IdExpr.eval` uses real division, so
off that domain a conditional with zero denominator evaluates to `0` by
convention (see the `chain2_eval_cond_zero` test), again carrying no
identification meaning.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

/-- Expressions returned by ID: the observed law, sums over variable sets, products, and
conditionals. A variable not bound by an enclosing `sum` keeps the value of the evaluation
point. -/
inductive IdExpr (V : Type*) where
  | obs                                    -- P(v): the observed law at the evaluation point
  | sum (S : Finset V) (e : IdExpr V)      -- Σ_s e: e summed over the values of S
  | one
  | mul (e₁ e₂ : IdExpr V)
  | cond (D A B : Finset V) (e : IdExpr V) -- e(a | b), e read as a law over the variables D

def IdExpr.prodList {V : Type*} (l : List (IdExpr V)) : IdExpr V := l.foldr .mul .one

open MetaMathlibExt in
noncomputable def IdExpr.eval {V α : Type*} [Fintype V] [DecidableEq V] [Fintype α]
    (p : (V → α) → ℝ) : IdExpr V → (V → α) → ℝ
  | .obs => p
  | .sum S e => FiniteWeight.marginal (e.eval p) (↑S)ᶜ
  | .one => fun _ => 1
  | .mul e₁ e₂ => fun x => e₁.eval p x * e₂.eval p x
  | .cond D A B e => fun x =>
      FiniteWeight.marginal (e.eval p) (↑(A ∪ B) ∪ (↑D)ᶜ) x /
        FiniteWeight.marginal (e.eval p) (↑B ∪ (↑D)ᶜ) x

end Cslib.MachineLearning.GraphicalModels

namespace Cslib.MachineLearning.GraphicalModels.ADMG

variable {V : Type*} [Fintype V] [DecidableEq V] (G : ADMG V)
  (σ : V ≃ Fin (Fintype.card V))  -- π, "some topological ordering of nodes in G"; the recursion
  -- is defined for every ordering, and identifies under a topological one (module doc)

/-- `G[D]` on the same vertex type. -/
def induce (D : Set V) : ADMG V where
  dir u w := u ∈ D ∧ w ∈ D ∧ G.dir u w
  bidir := SimpleGraph.fromRel fun u w => u ∈ D ∧ w ∈ D ∧ G.bidir.Adj u w
  acyclic := by
    intro v h
    have hle : (fun u w => u ∈ D ∧ w ∈ D ∧ G.dir u w) ≤ G.dir := fun a b hh => hh.2.2
    exact G.acyclic v ((Relation.TransGen.mono hle) v v h)

open scoped Classical in
/-- `An(Y)` in `G[D]`, reflexive. -/
noncomputable def ancIn (D Y : Finset V) : Finset V :=
  D.filter fun u => ∃ y ∈ Y, Relation.ReflTransGen (G.induce D).dir u y

open scoped Classical in
/-- `An(Y)` in `G[D]_{x̄}`: arrows into `X` deleted (bidirected arcs do not affect ancestry). -/
noncomputable def ancCut (D X Y : Finset V) : Finset V :=
  D.filter fun u => ∃ y ∈ Y,
    Relation.ReflTransGen (fun a b => (G.induce D).dir a b ∧ b ∉ X) u y

open scoped Classical in
/-- The c-component of `v` in `G[D]`, through the merged `ADMG.cComponent`. -/
noncomputable def compIn (D : Finset V) (v : V) : Finset V :=
  D.filter (· ∈ (G.induce D).cComponent v)

/-- `C(G[D])`. -/
noncomputable def cComponentsIn (D : Finset V) : Finset (Finset V) :=
  D.image (G.compIn D)

/-- `Π_{V_i ∈ S} P(v_i | v_π^(i−1))`, predecessors taken inside `D` along `σ`. -/
noncomputable def condChain (D S : Finset V) (P : IdExpr V) : IdExpr V :=
  IdExpr.prodList (S.toList.map fun v => .cond D {v} (D.filter fun u => σ u < σ v) P)

noncomputable def idRec (Y X D : Finset V) (P : IdExpr V) :
    Except (Finset V × Finset V) (IdExpr V) :=
  if X = ∅ then .ok (.sum (D \ Y) P)                                         -- line 1
  else if hA : G.ancIn D Y ≠ D then                                           -- line 2
    idRec Y (X ∩ G.ancIn D Y) (G.ancIn D Y) (.sum (D \ G.ancIn D Y) P)
  else if hW : ((D \ X) \ G.ancCut D X Y).Nonempty then                       -- line 3
    idRec Y (X ∪ (D \ X) \ G.ancCut D X Y) D P
  else if hT : D \ X ∉ G.cComponentsIn (D \ X) then                           -- line 4, k ≠ 1
    do
      let es ← (G.cComponentsIn (D \ X)).toList.attach.mapM
        fun S => idRec S.1 (D \ S.1) D P
      pure (.sum (D \ (Y ∪ X)) (IdExpr.prodList es))
  else if hD : D ∈ G.cComponentsIn D then .error (D, D \ X)                  -- line 5
  else if D \ X ∈ G.cComponentsIn D then                                      -- line 6
    .ok (.sum ((D \ X) \ Y) (condChain σ D (D \ X) P))
  else                                                                         -- line 7
    have hne : (D \ X).Nonempty := by
      have hmem : D \ X ∈ G.cComponentsIn (D \ X) := of_not_not hT
      rw [cComponentsIn, Finset.mem_image] at hmem
      obtain ⟨v, hv, _⟩ := hmem
      exact ⟨v, hv⟩
    let S' := G.compIn D hne.choose
    idRec Y (X ∩ S') S' (condChain σ D S' P)
termination_by (D.card, (D \ X).card)
decreasing_by
  · classical
    apply Prod.Lex.left
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    constructor
    · unfold ancIn
      exact Finset.filter_subset _ _
    · exact hA
  · classical
    apply Prod.Lex.right
    have hWsub : (D \ X) \ G.ancCut D X Y ⊆ D \ X := Finset.sdiff_subset
    have heq : D \ (X ∪ (D \ X) \ G.ancCut D X Y) = (D \ X) \ ((D \ X) \ G.ancCut D X Y) := by
      ext a
      simp only [Finset.mem_sdiff, Finset.mem_union]
      tauto
    rw [heq]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    constructor
    · exact Finset.sdiff_subset
    · intro hcontra
      obtain ⟨w, hw⟩ := hW
      have hwDX : w ∈ D \ X := hWsub hw
      have hwNot : w ∉ (D \ X) \ ((D \ X) \ G.ancCut D X Y) := by
        rw [Finset.mem_sdiff]
        intro h
        exact h.2 hw
      rw [hcontra] at hwNot
      exact absurd hwDX hwNot
  · classical
    apply Prod.Lex.right
    have hSmem : (S : Finset V) ∈ G.cComponentsIn (D \ X) := by
      have hlist : (S : Finset V) ∈ (G.cComponentsIn (D \ X)).toList := S.property
      rwa [Finset.mem_toList] at hlist
    have himg : ∃ v ∈ D \ X, G.compIn (D \ X) v = (S : Finset V) := by
      have h := hSmem
      simp only [cComponentsIn, Finset.mem_image] at h
      exact h
    obtain ⟨v, hv, hveq⟩ := himg
    have hSsub : (S : Finset V) ⊆ D \ X := by
      rw [← hveq]
      unfold compIn
      exact Finset.filter_subset _ _
    have hSne : (S : Finset V) ≠ D \ X := by
      intro hcon
      rw [hcon] at hSmem
      exact hT hSmem
    have hSsubD : (S : Finset V) ⊆ D := hSsub.trans Finset.sdiff_subset
    have heq : D \ (D \ (S : Finset V)) = (S : Finset V) :=
      Finset.sdiff_sdiff_eq_self hSsubD
    rw [heq]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    exact ⟨hSsub, hSne⟩
  · -- line 7: S' = compIn D v ⊂ D since S' ∈ C(G[D]) but D ∉
    classical
    apply Prod.Lex.left
    -- v = hne.choose ∈ D \ X ⊆ D
    have hvDX : hne.choose ∈ D \ X := hne.choose_spec
    have hvD : hne.choose ∈ D := Finset.sdiff_subset hvDX
    -- S' ∈ cComponentsIn D
    have hSmem : G.compIn D hne.choose ∈ G.cComponentsIn D := by
      simp only [cComponentsIn, Finset.mem_image]
      exact ⟨hne.choose, hvD, rfl⟩
    -- S' ⊆ D via filter
    have hSsub : G.compIn D hne.choose ⊆ D := by
      unfold compIn
      exact Finset.filter_subset _ _
    -- S' ≠ D by hD
    have hSne : G.compIn D hne.choose ≠ D := by
      intro hcon
      rw [hcon] at hSmem
      exact hD hSmem
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    exact ⟨hSsub, hSne⟩

/-- `ID(y, x, P, G)` at the top level: the whole vertex set and the observed law. As in the
source, the query is meant to have `X` and `Y` disjoint and `σ` a topological ordering; outside
that domain the returned value carries no identification meaning (module doc). -/
noncomputable def ID (Y X : Finset V) : Except (Finset V × Finset V) (IdExpr V) :=
  G.idRec σ Y X Finset.univ .obs

theorem compIn_subset (D : Finset V) (v : V) : G.compIn D v ⊆ D := by
  classical
  unfold compIn
  exact Finset.filter_subset _ _

theorem compIn_self_mem {D : Finset V} {v : V} (hv : v ∈ D) : v ∈ G.compIn D v := by
  classical
  unfold compIn
  rw [Finset.mem_filter]
  constructor
  · exact hv
  · show v ∈ (G.induce ↑D).cComponent v
    unfold ADMG.cComponent
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr rfl

theorem induce_cComponent_eq_of_mem {D : Finset V} {v w : V}
    (h : w ∈ (G.induce ↑D).cComponent v) :
    (G.induce ↑D).cComponent v = (G.induce ↑D).cComponent w := by
  unfold ADMG.cComponent
  have hmk : (G.induce ↑D).bidir.connectedComponentMk w =
      (G.induce ↑D).bidir.connectedComponentMk v :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp h
  rw [hmk]

theorem compIn_eq_of_mem {D : Finset V} {v w : V}
    (h : w ∈ G.compIn D v) : G.compIn D w = G.compIn D v := by
  classical
  have hwIn : w ∈ (G.induce ↑D).cComponent v := by
    unfold compIn at h
    rw [Finset.mem_filter] at h
    exact h.2
  have hcc := G.induce_cComponent_eq_of_mem hwIn
  unfold compIn
  rw [← hcc]

theorem induce_reachable_mono {S T : Finset V} (hST : S ⊆ T) {u w : V}
    (h : (G.induce ↑S).bidir.Reachable u w) : (G.induce ↑T).bidir.Reachable u w := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h ⊢
  have hle : (G.induce ↑S).bidir.Adj ≤ (G.induce ↑T).bidir.Adj := by
    intro a b hab
    change (SimpleGraph.fromRel (fun x y => x ∈ ↑S ∧ y ∈ ↑S ∧ G.bidir.Adj x y)).Adj a b at hab
    change (SimpleGraph.fromRel (fun x y => x ∈ ↑T ∧ y ∈ ↑T ∧ G.bidir.Adj x y)).Adj a b
    rw [SimpleGraph.fromRel_adj] at hab ⊢
    have hST' : ∀ {x : V}, x ∈ (↑S : Set V) → x ∈ (↑T : Set V) :=
      fun hx => Finset.mem_coe.mpr (hST (Finset.mem_coe.mp hx))
    obtain ⟨hne, h1 | h2⟩ := hab
    · exact ⟨hne, Or.inl ⟨hST' h1.1, hST' h1.2.1, h1.2.2⟩⟩
    · exact ⟨hne, Or.inr ⟨hST' h2.1, hST' h2.2.1, h2.2.2⟩⟩
  exact (Relation.ReflTransGen.mono hle) _ _ h

theorem subset_ancIn {Y D : Finset V} (hYD : Y ⊆ D) : Y ⊆ G.ancIn D Y := by
  classical
  intro y hyY
  unfold ancIn
  rw [Finset.mem_filter]
  exact ⟨hYD hyY, y, hyY, Relation.ReflTransGen.refl⟩

theorem subset_ancCut {Y D X : Finset V} (hYD : Y ⊆ D) : Y ⊆ G.ancCut D X Y := by
  classical
  intro y hyY
  unfold ancCut
  rw [Finset.mem_filter]
  exact ⟨hYD hyY, y, hyY, Relation.ReflTransGen.refl⟩

theorem ancIn_empty (D : Finset V) : G.ancIn D ∅ = ∅ := by
  classical
  unfold ancIn
  simp

/-! ### Faithfulness lemmas (prep section 3.5), statements only -/

/-- F1: `C(G[D])` partitions `D`: nonempty blocks, each `⊆ D`, pairwise disjoint, union `D`. -/
theorem cComponentsIn_partition (D : Finset V) :
    (∀ S ∈ G.cComponentsIn D, S.Nonempty) ∧ (∀ S ∈ G.cComponentsIn D, S ⊆ D) ∧
      (∀ S ∈ G.cComponentsIn D, ∀ T ∈ G.cComponentsIn D, S ≠ T → Disjoint S T) ∧
      (G.cComponentsIn D).biUnion id = D := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro S hS
    simp only [cComponentsIn, Finset.mem_image] at hS
    obtain ⟨v, hvD, rfl⟩ := hS
    exact ⟨v, G.compIn_self_mem hvD⟩
  · intro S hS
    simp only [cComponentsIn, Finset.mem_image] at hS
    obtain ⟨v, hvD, rfl⟩ := hS
    exact G.compIn_subset _ _
  · intro S hS T hT hne
    simp only [cComponentsIn, Finset.mem_image] at hS hT
    obtain ⟨v, hvD, rfl⟩ := hS
    obtain ⟨w, hwD, rfl⟩ := hT
    rw [Finset.disjoint_left]
    intro x hxv hxw
    exact hne ((G.compIn_eq_of_mem hxv).symm.trans (G.compIn_eq_of_mem hxw))
  · ext x
    rw [Finset.mem_biUnion]
    constructor
    · rintro ⟨S, hS, hxS⟩
      have hsub : S ⊆ D := by
        simp only [cComponentsIn, Finset.mem_image] at hS
        obtain ⟨v, hvD, rfl⟩ := hS
        exact G.compIn_subset _ _
      exact hsub hxS
    · intro hxD
      refine ⟨G.compIn D x, ?_, G.compIn_self_mem hxD⟩
      show G.compIn D x ∈ D.image (G.compIn D)
      exact Finset.mem_image.mpr ⟨x, hxD, rfl⟩

/-- F2: for `T ≠ ∅`, `T ∈ C(G[T]) ↔ C(G[T]) = {T}` (at `T = D \ X`: the line-4 guard is
`k ≠ 1`). -/
theorem line4_guard_iff {T : Finset V} (hT : T ≠ ∅) :
    T ∈ G.cComponentsIn T ↔ G.cComponentsIn T = {T} := by
  classical
  constructor
  · intro hmem
    rw [Finset.eq_singleton_iff_unique_mem]
    constructor
    · exact hmem
    · -- every S ∈ image equals T
      simp only [cComponentsIn, Finset.mem_image] at hmem ⊢
      obtain ⟨v, hvT, hveq⟩ := hmem
      intro S hS
      obtain ⟨w, hwT, hweq⟩ := hS
      -- show compIn T w = T
      have hall : G.compIn T w = T := by
        -- w ∈ cComponent v
        have hwIn : w ∈ (G.induce ↑T).cComponent v := by
          have hwComp : w ∈ G.compIn T v := by rw [hveq]; exact hwT
          unfold compIn at hwComp
          rw [Finset.mem_filter] at hwComp
          exact hwComp.2
        have hcc : (G.induce ↑T).cComponent w = (G.induce ↑T).cComponent v := by
          unfold ADMG.cComponent
          have hmk : (G.induce ↑T).bidir.connectedComponentMk w =
              (G.induce ↑T).bidir.connectedComponentMk v :=
            (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hwIn
          rw [hmk]
        have hcomp : G.compIn T w = G.compIn T v := by
          unfold compIn
          rw [hcc]
        rw [hcomp, hveq]
      rw [← hweq]
      exact hall
  · intro h
    rw [h]
    exact Finset.mem_singleton_self T

/-- F3: for `D ≠ ∅`, `D ∈ C(G[D]) ↔ C(G[D]) = {D}` (line 5 is "C(G) = {G}"). -/
theorem line5_guard_iff {D : Finset V} (hD : D ≠ ∅) :
    D ∈ G.cComponentsIn D ↔ G.cComponentsIn D = {D} := by
  classical
  constructor
  · intro hmem
    rw [Finset.eq_singleton_iff_unique_mem]
    constructor
    · exact hmem
    · simp only [cComponentsIn, Finset.mem_image] at hmem ⊢
      obtain ⟨v, hvT, hveq⟩ := hmem
      intro S hS
      obtain ⟨w, hwT, hweq⟩ := hS
      have hall : G.compIn D w = D := by
        have hwIn : w ∈ (G.induce ↑D).cComponent v := by
          have hwComp : w ∈ G.compIn D v := by rw [hveq]; exact hwT
          unfold compIn at hwComp
          rw [Finset.mem_filter] at hwComp
          exact hwComp.2
        have hcc : (G.induce ↑D).cComponent w = (G.induce ↑D).cComponent v := by
          unfold ADMG.cComponent
          have hmk : (G.induce ↑D).bidir.connectedComponentMk w =
              (G.induce ↑D).bidir.connectedComponentMk v :=
            (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hwIn
          rw [hmk]
        have hcomp : G.compIn D w = G.compIn D v := by
          unfold compIn
          rw [hcc]
        rw [hcomp, hveq]
      rw [← hweq]
      exact hall
  · intro h
    rw [h]
    exact Finset.mem_singleton_self D

theorem line7_compIn_eq {D X : Finset V} (h4 : D \ X ∈ G.cComponentsIn (D \ X))
    {s t : V} (hs : s ∈ D \ X) (ht : t ∈ D \ X) : G.compIn D t = G.compIn D s := by
  classical
  have hDXne : D \ X ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨s, hs⟩
  have hsing : G.cComponentsIn (D \ X) = {D \ X} := (G.line4_guard_iff hDXne).mp h4
  have hcomp : G.compIn (D \ X) t = D \ X := by
    have hmem : G.compIn (D \ X) t ∈ G.cComponentsIn (D \ X) := by
      show G.compIn (D \ X) t ∈ (D \ X).image (G.compIn (D \ X))
      exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
    rw [hsing] at hmem
    exact Finset.mem_singleton.mp hmem
  have hsIn : s ∈ (G.induce ↑(D \ X)).cComponent t := by
    have h1 : s ∈ G.compIn (D \ X) t := by
      rw [hcomp]
      exact hs
    unfold compIn at h1
    rw [Finset.mem_filter] at h1
    exact h1.2
  have hreach : (G.induce ↑D).bidir.Reachable t s :=
    G.induce_reachable_mono (S := D \ X) (T := D) Finset.sdiff_subset
      ((G.induce ↑(D \ X)).mem_cComponent_iff.mp hsIn)
  have hsComp : s ∈ G.compIn D t := by
    unfold compIn
    rw [Finset.mem_filter]
    refine ⟨Finset.sdiff_subset hs, ?_⟩
    exact (G.induce ↑D).mem_cComponent_iff.mpr hreach
  exact (G.compIn_eq_of_mem hsComp).symm

theorem line7_compIn_subset {D X : Finset V} (h4 : D \ X ∈ G.cComponentsIn (D \ X))
    {s : V} (hs : s ∈ D \ X) : D \ X ⊆ G.compIn D s := by
  classical
  intro t ht
  have hcon := G.line7_compIn_eq h4 hs ht
  rw [← hcon]
  exact G.compIn_self_mem (Finset.sdiff_subset ht)

/-- F4 (line 7): with the line-4 guard failed and the line-6 guard failed, for `s ∈ D \ X`:
`D \ X ⊆ compIn D s`, `D \ X ≠ compIn D s` (so `S ⊂ S'`), and `compIn D s` does not depend
on `s ∈ D \ X`. -/
theorem line7_component {D X : Finset V} (h4 : D \ X ∈ G.cComponentsIn (D \ X))
    (h6 : D \ X ∉ G.cComponentsIn D) {s : V} (hs : s ∈ D \ X) :
    D \ X ⊆ G.compIn D s ∧ D \ X ≠ G.compIn D s ∧
      ∀ t ∈ D \ X, G.compIn D t = G.compIn D s := by
  classical
  have hcon : ∀ t ∈ D \ X, G.compIn D t = G.compIn D s :=
    fun t ht => G.line7_compIn_eq h4 hs ht
  have hsub : D \ X ⊆ G.compIn D s := G.line7_compIn_subset h4 hs
  have hne : D \ X ≠ G.compIn D s := by
    intro hcon2
    apply h6
    rw [hcon2]
    show G.compIn D s ∈ D.image (G.compIn D)
    exact Finset.mem_image.mpr ⟨s, Finset.sdiff_subset hs, rfl⟩
  exact ⟨hsub, hne, hcon⟩

/-- F5: `X ⊆ D`, `Y ⊆ D`, `Disjoint X Y` pass to the arguments of the recursive calls of
lines 2, 3, 4 and 7 (line 7 for every `s ∈ D \ X`, given the failed line-4 guard), and once
lines 1-2 have failed (`X ≠ ∅`, `An(Y) = D`), `D \ X ≠ ∅`. -/
theorem idRec_invariants {Y X D : Finset V} (hXD : X ⊆ D) (hYD : Y ⊆ D)
    (hXY : Disjoint X Y) :
    (X ∩ G.ancIn D Y ⊆ G.ancIn D Y ∧ Y ⊆ G.ancIn D Y ∧
        Disjoint (X ∩ G.ancIn D Y) Y) ∧
      (X ∪ (D \ X) \ G.ancCut D X Y ⊆ D ∧ Y ⊆ D ∧
        Disjoint (X ∪ (D \ X) \ G.ancCut D X Y) Y) ∧
      (∀ S ∈ G.cComponentsIn (D \ X), D \ S ⊆ D ∧ S ⊆ D ∧ Disjoint (D \ S) S) ∧
      (D \ X ∈ G.cComponentsIn (D \ X) → ∀ s ∈ D \ X,
        X ∩ G.compIn D s ⊆ G.compIn D s ∧ Y ⊆ G.compIn D s ∧
          Disjoint (X ∩ G.compIn D s) Y) ∧
      (X ≠ ∅ → G.ancIn D Y = D → D \ X ≠ ∅) := by
  classical
  have hWY : Disjoint ((D \ X) \ G.ancCut D X Y) Y := by
    rw [Finset.disjoint_left]
    intro w hwW hwY
    rw [Finset.mem_sdiff] at hwW
    exact hwW.2 (G.subset_ancCut hYD hwY)
  refine ⟨⟨Finset.inter_subset_right, G.subset_ancIn hYD,
      Disjoint.mono_left Finset.inter_subset_left hXY⟩,
    ⟨?_, hYD, Finset.disjoint_union_left.mpr ⟨hXY, hWY⟩⟩,
    ?_, ?_, ?_⟩
  · rw [Finset.union_subset_iff]
    exact ⟨hXD, Finset.sdiff_subset.trans Finset.sdiff_subset⟩
  · intro S hS
    have hSDX : S ⊆ D \ X := (G.cComponentsIn_partition (D \ X)).2.1 S hS
    exact ⟨Finset.sdiff_subset, hSDX.trans Finset.sdiff_subset,
      (Finset.disjoint_sdiff (s := S) (t := D)).symm⟩
  · intro h4 s hs
    have hYDX : Y ⊆ D \ X := by
      intro y hyY
      rw [Finset.mem_sdiff]
      refine ⟨hYD hyY, ?_⟩
      intro hxY
      exact Finset.disjoint_left.mp hXY hxY hyY
    exact ⟨Finset.inter_subset_right, hYDX.trans (G.line7_compIn_subset h4 hs),
      Disjoint.mono_left Finset.inter_subset_left hXY⟩
  · intro hX hAnc hW
    have hDX : D ⊆ X := Finset.sdiff_eq_empty_iff_subset.mp hW
    have hYX : Y ⊆ X := hYD.trans hDX
    have hYY : Disjoint Y Y := Disjoint.mono hYX le_rfl hXY
    have hY : Y = ∅ := (Finset.disjoint_self_iff_empty Y).mp hYY
    rw [hY, G.ancIn_empty D] at hAnc
    have hDe : D = ∅ := hAnc.symm
    obtain ⟨x, hxX⟩ := Finset.nonempty_iff_ne_empty.mpr hX
    have hxD : x ∈ D := hXD hxX
    rw [hDe] at hxD
    simp at hxD

end Cslib.MachineLearning.GraphicalModels.ADMG
