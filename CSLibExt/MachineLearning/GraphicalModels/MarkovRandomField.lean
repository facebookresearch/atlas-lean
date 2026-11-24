/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FiniteWeightSemigraphoid
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Markov random fields: Gibbs factorization and the Markov properties

For an undirected graph `G` on a finite type `V` and a real weight `p` on
configurations `V → α` (`α` finite), in the sense of
`MetaMathlibExt.FiniteWeight`:

* `GibbsFactorization G p`: `p` is a finite product of nonnegative potentials,
  one per clique of `G`, each depending only on its clique (the empty clique
  carries global constants such as `1 / Z`);
* `SimpleGraph.SeparatedBy G A B S`: every walk from `A` to `B` meets `S`;
* `GlobalMarkov`, `LocalMarkov`, `PairwiseMarkov`: the three Markov properties.

Main results: Gibbs factorization implies the global Markov property
(`globalMarkov_of_gibbsFactorization`, no positivity needed), global implies
local (`localMarkov_of_globalMarkov`), and local implies pairwise for
nonnegative weights (`pairwiseMarkov_of_localMarkov`). No converse is claimed;
the positive-distribution Hammersley–Clifford direction is out of scope.

## References

* E. P. Xing, 10-708 Probabilistic Graphical Models, Lecture 3: Undirected
  Graphical Models, Carnegie Mellon University (2019).
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

open MetaMathlibExt.FiniteWeight

/-- Graph separation in an undirected graph: every walk from a vertex of `A` to a vertex
of `B` passes through a vertex of `S`. -/
def _root_.SimpleGraph.SeparatedBy {V : Type*} (G : SimpleGraph V) (A B S : Set V) : Prop :=
  ∀ ⦃a b : V⦄, a ∈ A → b ∈ B → ∀ w : G.Walk a b, ∃ v ∈ S, v ∈ w.support

/-- A weight `p` on configurations **factorizes over the cliques** of `G` (Gibbs
factorization): `p` is a finite product of nonnegative potentials `ψ C`, one for each
clique `C` of `G`, where `ψ C` depends only on the variables in `C`. The weight is
unnormalized: the Gibbs normalizing constant `1 / Z` is absorbed into `p`, which does
not change any `CondIndep` statement proved from the factorization below. The family
may include the empty clique; its potential is constant and carries global constants
such as `1 / Z` (see `GibbsFactorization.const_mul`). -/
def GibbsFactorization {V α : Type*} [Fintype V] [DecidableEq V] [Fintype α]
    (G : SimpleGraph V) (p : (V → α) → ℝ) : Prop :=
  ∃ (𝒞 : Finset (Set V)) (ψ : Set V → (V → α) → ℝ),
    (∀ C ∈ 𝒞, G.IsClique C) ∧
    (∀ C ∈ 𝒞, ∀ x, 0 ≤ ψ C x) ∧
    (∀ C ∈ 𝒞, DependsOn (ψ C) C) ∧
    p = fun x => ∏ C ∈ 𝒞, ψ C x

/-- The **global Markov property** of `p` with respect to `G`: whenever `S` separates
`A` from `B` in `G`, the variables in `A` and `B` are conditionally independent given
those in `S`. -/
def GlobalMarkov {V α : Type*} [Fintype V] [DecidableEq V] [Fintype α]
    (G : SimpleGraph V) (p : (V → α) → ℝ) : Prop :=
  ∀ A B S : Set V, G.SeparatedBy A B S → CondIndep p A B S

/-- The **local Markov property**: each variable is conditionally independent of all
variables outside its closed neighborhood, given its neighbors (its Markov blanket). -/
def LocalMarkov {V α : Type*} [Fintype V] [DecidableEq V] [Fintype α]
    (G : SimpleGraph V) (p : (V → α) → ℝ) : Prop :=
  ∀ v : V, CondIndep p {v} ({v} ∪ G.neighborSet v)ᶜ (G.neighborSet v)

/-- The **pairwise Markov property**: any two distinct nonadjacent variables are
conditionally independent given all the others. -/
def PairwiseMarkov {V α : Type*} [Fintype V] [DecidableEq V] [Fintype α]
    (G : SimpleGraph V) (p : (V → α) → ℝ) : Prop :=
  ∀ ⦃a b : V⦄, a ≠ b → ¬ G.Adj a b → CondIndep p {a} {b} ({a, b} : Set V)ᶜ

/-- **Gibbs soundness**: a weight that factorizes over the cliques of `G` satisfies the
global Markov property with respect to `G`. No positivity is needed. -/
theorem globalMarkov_of_gibbsFactorization {V α : Type*} [Fintype V] [DecidableEq V]
    [Fintype α] {G : SimpleGraph V} {p : (V → α) → ℝ}
    (h : GibbsFactorization G p) : GlobalMarkov G p := by
  classical
  obtain ⟨𝒞, ψ, hcl, _hnn, hdep, rfl⟩ := h
  intro A B S hsep
  set P : Set V :=
    S ∪ {v | ∃ a ∈ A \ S, ∃ w : G.Walk a v, ∀ u ∈ w.support, u ∈ S → u = v} with hP
  set Q : Set V := (P \ S)ᶜ with hQ
  have hSP : S ⊆ P := by
    intro v hv
    simp only [hP, Set.mem_union]
    exact Or.inl hv
  have hAP : ∀ v ∈ A \ S, v ∈ P := by
    intro v hv
    simp only [hP, Set.mem_union]
    refine Or.inr ⟨v, hv, (SimpleGraph.Walk.nil : G.Walk v v), ?_⟩
    intro u hu _
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hu
    exact hu
  have hPQ : ∀ v, v ∈ P ∨ v ∈ Q := by
    intro v
    by_cases hv : v ∈ P
    · exact Or.inl hv
    · simp only [hQ, Set.mem_compl_iff, Set.mem_sdiff]
      exact Or.inr (fun hh => hv hh.1)
  have hPQcap : P ∩ Q = S := by
    ext v
    simp only [Set.mem_inter_iff, hQ, Set.mem_compl_iff, Set.mem_sdiff]
    constructor
    · intro hh
      by_cases hs : v ∈ S
      · exact hs
      · exact absurd ⟨hh.1, hs⟩ hh.2
    · intro hs
      exact ⟨hSP hs, fun hh => hh.2 hs⟩
  have hAQ : ∀ v ∈ A \ S, v ∉ Q := by
    intro v hv
    have hvS : v ∉ S := hv.2
    rw [hQ]
    simp only [Set.mem_compl_iff, not_not]
    exact ⟨hAP v hv, hvS⟩
  have hBP : ∀ v ∈ B \ S, v ∉ P := by
    intro v hv
    have hvB : v ∈ B := hv.1
    have hvS : v ∉ S := hv.2
    intro hvP
    simp only [hP, Set.mem_union] at hvP
    cases hvP with
    | inl hs => exact hvS hs
    | inr hex =>
      obtain ⟨a, haA, w, hw⟩ := hex
      have haA' : a ∈ A := haA.1
      obtain ⟨u, huS, humem⟩ := hsep haA' hvB w
      have hueq := hw u humem huS
      subst hueq
      exact hvS huS
  have hclique : ∀ C ∈ 𝒞, C ⊆ P ∨ C ⊆ Q := by
    intro C hC
    by_cases hsub : C ⊆ P
    · exact Or.inl hsub
    · refine Or.inr ?_
      intro t ht
      by_contra htQ
      have htPS : t ∈ P \ S := by
        simp only [hQ, Set.mem_compl_iff, not_not] at htQ
        exact htQ
      obtain ⟨htP, htS⟩ := htPS
      obtain ⟨u, huC, huP⟩ := Set.not_subset.mp hsub
      by_cases heq : u = t
      · subst heq
        exact huP htP
      · have hadj : G.Adj u t := hcl C hC huC ht heq
        simp only [hP, Set.mem_union] at htP
        cases htP with
        | inl hs => exact htS hs
        | inr hex =>
          obtain ⟨a, haA, w, hw⟩ := hex
          have hreach : u ∈ P := by
            simp only [hP, Set.mem_union]
            refine Or.inr ⟨a, haA,
              w.append (SimpleGraph.Walk.cons (G.adj_symm hadj) SimpleGraph.Walk.nil), ?_⟩
            intro m hmem hmS
            simp only [SimpleGraph.Walk.support_append, List.mem_append] at hmem
            cases hmem with
            | inl hmemw =>
              have hmt := hw m hmemw hmS
              subst hmt
              exact absurd hmS htS
            | inr hmemt =>
              rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hmemt
              have hmu : m ∈ ([u] : List V) := hmemt
              exact List.mem_singleton.mp hmu
          exact huP hreach
  have hprod : ∀ (S : Finset (Set V)) (P : Set V),
      (∀ C ∈ S, DependsOn (ψ C) P) → DependsOn (fun x => ∏ C ∈ S, ψ C x) P := by
    intro S P
    refine Finset.induction_on S ?_ ?_
    · intro hS x y _
      simp
    · intro a s ha ih hS
      have haP : DependsOn (ψ a) P := hS a (Finset.mem_insert_self a s)
      have hsP : ∀ C ∈ s, DependsOn (ψ C) P :=
        fun C hC => hS C (Finset.mem_insert_of_mem hC)
      have ihP := ih hsP
      intro x y hxy
      have hax : ψ a x = ψ a y := haP hxy
      have hsx : ∏ C ∈ s, ψ C x = ∏ C ∈ s, ψ C y := ihP hxy
      have e : (fun x => ∏ C ∈ insert a s, ψ C x) = fun x => ψ a x * ∏ C ∈ s, ψ C x := by
        funext x
        exact Finset.prod_insert ha
      rw [e]
      beta_reduce
      rw [hax, hsx]
  set f : (V → α) → ℝ := fun x => ∏ C ∈ 𝒞.filter (· ⊆ P), ψ C x with hf_def
  set g : (V → α) → ℝ := fun x => ∏ C ∈ 𝒞.filter (fun C => ¬ C ⊆ P), ψ C x with hg_def
  have hf : DependsOn f P := by
    simp only [hf_def]
    apply hprod
    intro C hC
    simp only [Finset.mem_filter] at hC
    exact DependsOn.mono hC.2 (hdep C hC.1)
  have hg : DependsOn g Q := by
    simp only [hg_def]
    apply hprod
    intro C hC
    simp only [Finset.mem_filter] at hC
    have hsubQ : C ⊆ Q := (hclique C hC.1).resolve_left hC.2
    exact DependsOn.mono hsubQ (hdep C hC.1)
  have hfg : f * g = fun x => ∏ C ∈ 𝒞, ψ C x := by
    funext x
    simp only [hf_def, hg_def, Pi.mul_apply]
    exact Finset.prod_filter_mul_prod_filter_not 𝒞 (· ⊆ P) (fun C => ψ C x)
  have hci := condIndep_of_dependsOn hf hg hPQ hAQ hBP
  rw [hfg, hPQcap] at hci
  exact condIndep_of_sdiff hci

/-- The global Markov property implies the local Markov property. -/
theorem localMarkov_of_globalMarkov {V α : Type*} [Fintype V] [DecidableEq V]
    [Fintype α] {G : SimpleGraph V} {p : (V → α) → ℝ}
    (h : GlobalMarkov G p) : LocalMarkov G p := by
  intro v
  apply h
  have hstart : ∀ {u b : V} (w' : G.Walk u b), u ∈ w'.support := by
    intro u b w'
    cases w' with
    | nil => simp [SimpleGraph.Walk.support_nil]
    | cons h tail => simp [SimpleGraph.Walk.support_cons]
  intro a b ha hb w
  simp only [Set.mem_singleton_iff] at ha
  subst ha
  cases w with
  | nil =>
    simp at hb
  | cons hadj w' =>
    have hmem := hstart w'
    exact ⟨_, (SimpleGraph.mem_neighborSet G a _).mpr hadj, by
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
      exact Or.inr hmem⟩

/-- For a nonnegative weight, the local Markov property implies the pairwise Markov
property. Nonnegativity is needed here: this step is weak union for finite
conditional independence. -/
theorem pairwiseMarkov_of_localMarkov {V α : Type*} [Fintype V] [DecidableEq V]
    [Fintype α] {G : SimpleGraph V} {p : (V → α) → ℝ} (hp : ∀ x, 0 ≤ p x)
    (h : LocalMarkov G p) : PairwiseMarkov G p := by
  intro a b hab hnab
  have ha := h a
  set R : Set V := ({a} ∪ G.neighborSet a)ᶜ with hR
  have hbR : b ∈ R := by
    simp only [hR, Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff, not_or]
    exact ⟨fun heq => hab heq.symm,
      fun hadj => hnab ((SimpleGraph.mem_neighborSet G a b).mp hadj)⟩
  have hRsplit : R = {b} ∪ (R \ {b}) := by
    ext v
    simp only [Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · intro hv
      by_cases heq : v = b
      · exact Or.inl heq
      · exact Or.inr ⟨hv, heq⟩
    · rintro (heq | ⟨hv, -⟩)
      · rw [heq]
        exact hbR
      · exact hv
  have hdisjR : Disjoint R {a} := by
    refine Set.disjoint_left.mpr ?_
    intro v hvR hva
    simp only [Set.mem_singleton_iff] at hva
    subst hva
    simp [hR] at hvR
  have hsplit : CondIndep p ({b} ∪ (R \ {b})) {a} (G.neighborSet a) := by
    rw [← hRsplit]
    exact ha.symm
  have hdisj : Disjoint ({b} ∪ (R \ {b})) {a} := by
    rw [← hRsplit]
    exact hdisjR
  have hwu := condIndep_weak_union hp hsplit hdisj
  have hcond : G.neighborSet a ∪ (R \ {b}) = ({a, b} : Set V)ᶜ := by
    ext v
    constructor
    · intro hv
      rw [Set.mem_union] at hv
      cases hv with
      | inl hvadj =>
        rw [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
        intro hcon
        cases hcon with
        | inl heq =>
          exact (G.ne_of_adj ((SimpleGraph.mem_neighborSet G a v).mp hvadj)) heq.symm
        | inr heq =>
          rw [heq] at hvadj
          exact hnab ((SimpleGraph.mem_neighborSet G a b).mp hvadj)
      | inr hmem =>
        rw [Set.mem_sdiff, Set.mem_singleton_iff] at hmem
        obtain ⟨hvR, hvn⟩ := hmem
        rw [hR, Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff] at hvR
        rw [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
        intro hcon
        cases hcon with
        | inl heq => exact hvR (Or.inl heq)
        | inr heq => exact hvn heq
    · intro hv
      rw [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      by_cases hvadj : v ∈ G.neighborSet a
      · exact Or.inl hvadj
      · refine Or.inr ⟨?_, ?_⟩
        · rw [hR, Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff]
          intro hcon
          cases hcon with
          | inl heq => exact hv (Or.inl heq)
          | inr heq' => exact hvadj heq'
        · rw [Set.mem_singleton_iff]
          intro heq
          exact hv (Or.inr heq)
  have hfin := hwu.symm
  rw [hcond] at hfin
  exact hfin

/-- A Gibbs weight is nonnegative: it is a product of nonnegative potentials. -/
theorem GibbsFactorization.nonneg {V α : Type*} [Fintype V] [DecidableEq V]
    [Fintype α] {G : SimpleGraph V} {p : (V → α) → ℝ}
    (h : GibbsFactorization G p) : ∀ x, 0 ≤ p x := by
  obtain ⟨𝒞, ψ, _, hnn, _, hp⟩ := h
  intro x
  rw [hp]
  have aux : ∀ s : Finset (Set V), s ⊆ 𝒞 → 0 ≤ ∏ C ∈ s, ψ C x := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _
      simp
    · intro a t ha ih hsub
      rw [Finset.prod_insert ha]
      have haC : a ∈ 𝒞 := hsub (Finset.mem_insert_self a t)
      have htC : t ⊆ 𝒞 := fun c hc => hsub (Finset.mem_insert_of_mem hc)
      exact mul_nonneg (hnn a haC x) (ih htC)
  exact aux 𝒞 fun c hc => hc

/-- A Gibbs weight satisfies the pairwise Markov property. -/
theorem pairwiseMarkov_of_gibbsFactorization {V α : Type*} [Fintype V] [DecidableEq V]
    [Fintype α] {G : SimpleGraph V} {p : (V → α) → ℝ}
    (h : GibbsFactorization G p) : PairwiseMarkov G p := by
  exact pairwiseMarkov_of_localMarkov h.nonneg
    (localMarkov_of_globalMarkov (globalMarkov_of_gibbsFactorization h))


/-- Constant absorption for Gibbs factorizations: multiplying a Gibbs weight by a
nonnegative constant gives a Gibbs weight. The constant is carried by the empty
clique's potential, which also covers the empty clique family. Together with
`globalMarkov_of_gibbsFactorization` this gives the Markov property for the
normalized law `p / ∑ y, p y` whenever the total mass is positive; the zero weight
itself is not a probability law. -/
theorem GibbsFactorization.const_mul {V α : Type*} [Fintype V] [DecidableEq V]
    [Fintype α] {G : SimpleGraph V} {p : (V → α) → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : GibbsFactorization G p) : GibbsFactorization G (fun x => c * p x) := by
  classical
  obtain ⟨𝒞, ψ, hcl, hnn, hdep, hp⟩ := h
  by_cases hmem : ∅ ∈ 𝒞
  · refine ⟨𝒞, Function.update ψ ∅ (fun x => c * ψ ∅ x), ?_, ?_, ?_, ?_⟩
    · intro C hC
      exact hcl C hC
    · intro C hC x
      by_cases hC0 : C = ∅
      · subst hC0
        simp only [Function.update_self]
        exact mul_nonneg hc (hnn ∅ hmem x)
      · have heq : Function.update ψ ∅ (fun x => c * ψ ∅ x) C x = ψ C x := by simp [hC0]
        rw [heq]
        exact hnn C hC x
    · intro C hC
      by_cases hC0 : C = ∅
      · subst hC0
        intro x y _
        have hψ : ψ ∅ x = ψ ∅ y :=
          hdep ∅ hmem (fun v hv => absurd hv (by simp))
        simp [hψ]
      · have heq : Function.update ψ ∅ (fun x => c * ψ ∅ x) C = ψ C := by simp [hC0]
        rw [heq]
        exact hdep C hC
    · funext x
      have h1 : Function.update ψ ∅ (fun x => c * ψ ∅ x) ∅ x = c * ψ ∅ x := by simp
      have h2 : ∀ C ∈ 𝒞.erase ∅, Function.update ψ ∅ (fun x => c * ψ ∅ x) C x = ψ C x := by
        intro C hC
        simp only [Finset.mem_erase] at hC
        simp [hC.1]
      have e1 : ψ ∅ x * ∏ C ∈ 𝒞.erase ∅, ψ C x = ∏ C ∈ 𝒞, ψ C x :=
        Finset.mul_prod_erase 𝒞 (fun C => ψ C x) hmem
      have e2 : Function.update ψ ∅ (fun x => c * ψ ∅ x) ∅ x *
            ∏ C ∈ 𝒞.erase ∅, Function.update ψ ∅ (fun x => c * ψ ∅ x) C x =
          ∏ C ∈ 𝒞, Function.update ψ ∅ (fun x => c * ψ ∅ x) C x :=
        Finset.mul_prod_erase 𝒞
          (fun C => Function.update ψ ∅ (fun x => c * ψ ∅ x) C x) hmem
      simp only [hp]
      rw [← e1, ← e2, h1]
      have hE : ∏ C ∈ 𝒞.erase ∅, ψ C x =
          ∏ C ∈ 𝒞.erase ∅, Function.update ψ ∅ (fun x => c * ψ ∅ x) C x :=
        Finset.prod_congr rfl (fun C hC => (h2 C hC).symm)
      rw [hE]
      ring
  · refine ⟨insert ∅ 𝒞, Function.update ψ ∅ (fun _ => c), ?_, ?_, ?_, ?_⟩
    · intro C hC
      simp only [Finset.mem_insert] at hC
      cases hC with
      | inl hC0 =>
        subst hC0
        exact SimpleGraph.isClique_empty
      | inr hC' => exact hcl C hC'
    · intro C hC x
      simp only [Finset.mem_insert] at hC
      by_cases hC0 : C = ∅
      · subst hC0
        simp only [Function.update_self]
        exact hc
      · have hC' : C ∈ 𝒞 := hC.resolve_left hC0
        have heq : Function.update ψ ∅ (fun _ => c) C x = ψ C x := by simp [hC0]
        rw [heq]
        exact hnn C hC' x
    · intro C hC
      simp only [Finset.mem_insert] at hC
      by_cases hC0 : C = ∅
      · subst hC0
        intro x y _
        simp
      · have hC' : C ∈ 𝒞 := hC.resolve_left hC0
        have heq : Function.update ψ ∅ (fun _ => c) C = ψ C := by simp [hC0]
        rw [heq]
        exact hdep C hC'
    · funext x
      have h1 : Function.update ψ ∅ (fun _ => c) ∅ x = c := by simp
      have h2 : ∀ C ∈ 𝒞, Function.update ψ ∅ (fun _ => c) C x = ψ C x := by
        intro C hC
        by_cases hC0 : C = ∅
        · subst hC0
          exact absurd hC hmem
        · simp [hC0]
      have e1 : ∏ C ∈ insert ∅ 𝒞, Function.update ψ ∅ (fun _ => c) C x =
          Function.update ψ ∅ (fun _ => c) ∅ x *
            ∏ C ∈ 𝒞, Function.update ψ ∅ (fun _ => c) C x :=
        Finset.prod_insert hmem
      simp only [hp]
      rw [e1, h1]
      have hE : ∏ C ∈ 𝒞, Function.update ψ ∅ (fun _ => c) C x = ∏ C ∈ 𝒞, ψ C x :=
        Finset.prod_congr rfl (fun C hC => h2 C hC)
      rw [hE]

/-- The global Markov property restricted to pairwise disjoint triples, the form in
which the source states graph separation. This is a direct restriction of
`GlobalMarkov`; the all-triples form reduces to it through `A \ S` and `B \ S` by
`condIndep_of_sdiff`. -/
theorem GlobalMarkov.condIndep_of_disjoint {V α : Type*} [Fintype V] [DecidableEq V]
    [Fintype α] {G : SimpleGraph V} {p : (V → α) → ℝ} (h : GlobalMarkov G p)
    {A B S : Set V} (_hAB : Disjoint A B) (_hAS : Disjoint A S) (_hBS : Disjoint B S)
    (hsep : G.SeparatedBy A B S) : CondIndep p A B S := by
  exact h _ _ _ hsep

end Cslib.MachineLearning.GraphicalModels
