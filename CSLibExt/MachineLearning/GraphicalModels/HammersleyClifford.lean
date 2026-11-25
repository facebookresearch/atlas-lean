/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.MarkovRandomField
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto

/-!
# Hammersley–Clifford: positive Markov weights factorize over cliques

For a strictly positive finite weight, the pairwise, local, and global Markov
properties from `MarkovRandomField` are each equivalent to Gibbs factorization
over the cliques of the graph. The pairwise-to-Gibbs direction uses the signed
log-potential (Möbius) expansion of `log p`: the interaction potential at a set
`A` vanishes unless `A` is a clique, because for a nonedge inside `A` the
pairwise Markov property gives a cross-ratio identity among the four
restrictions obtained by toggling that pair.

Positivity is essential: `fourCycleWeight`, supported on `1100`, `0010`, and
`0001` over the four-cycle, is pairwise Markov and nonnegative but does not
factorize over cliques.

## References

* E. P. Xing, 10-708 Probabilistic Graphical Models, Lecture 3: Undirected
  Graphical Models, Carnegie Mellon University (2019).
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

open MetaMathlibExt.FiniteWeight

private def restrictFinset {V α : Type*} [DecidableEq V] (x r : V → α) (B : Finset V) :
    V → α :=
  fun v => if v ∈ B then x v else r v

private theorem restrictFinset_univ {V α : Type*} [Fintype V] [DecidableEq V]
    (x r : V → α) : restrictFinset x r Finset.univ = x := by
  funext v
  simp [restrictFinset]

private theorem restrictFinset_congr_set {V α : Type*} [DecidableEq V]
    {x y r : V → α} {A : Set V} {B : Finset V}
    (h : ∀ v ∈ A, x v = y v) (hB : ↑B ⊆ A) :
    restrictFinset x r B = restrictFinset y r B := by
  funext v
  simp only [restrictFinset]
  by_cases hv : v ∈ B
  · simp only [hv, ↓reduceIte]
    exact h v (hB (Finset.mem_coe.mpr hv))
  · simp [hv]

private theorem restrictFinset_congr_finset {V α : Type*} [DecidableEq V]
    {x y r : V → α} {A B : Finset V}
    (h : ∀ v ∈ A, x v = y v) (hB : B ⊆ A) :
    restrictFinset x r B = restrictFinset y r B := by
  funext v
  simp only [restrictFinset]
  by_cases hv : v ∈ B
  · simp only [hv, ↓reduceIte]
    exact h v (hB hv)
  · simp [hv]

private theorem dependsOn_restrictFinset {V α β : Type*} [DecidableEq V]
    {r : V → α} {B : Finset V} {f : (V → α) → β} :
    DependsOn (fun x => f (restrictFinset x r B)) ↑B := by
  intro x y h
  exact congrArg f (restrictFinset_congr_set h subset_rfl)

private theorem marginal_univ_general {V α : Type*} [Fintype V] [DecidableEq V]
    [Fintype α] (p : (V → α) → ℝ) (x : V → α) : marginal p Set.univ x = p x := by
  have h1 : p x = ∑ y ∈ ({x} : Finset (V → α)), p y :=
    (Finset.sum_singleton p x).symm
  simp only [marginal]
  rw [h1]
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    funext v
    exact h v (Set.mem_univ v)
  · intro h
    rw [h]
    intro v _
    rfl

private theorem marginal_pos_of_pos {V α : Type*} [Fintype V] [DecidableEq V]
    [Fintype α] {p : (V → α) → ℝ} (hp : ∀ x, 0 < p x) (U : Set V) (x : V → α) :
    0 < marginal p U x := by
  classical
  simp only [marginal]
  exact Finset.sum_pos (fun y _ => hp y)
    ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, fun v _ => rfl⟩⟩

private theorem cross_ratio_quartet {V α : Type*} [Fintype V] [DecidableEq V]
    [Fintype α] {G : SimpleGraph V} {p : (V → α) → ℝ}
    {a b : V} (hab : a ≠ b) (hnab : ¬ G.Adj a b)
    (hPM : PairwiseMarkov G p) (hp : ∀ x, 0 < p x)
    (B : Finset V) (_haB : a ∉ B) (_hbB : b ∉ B) (x r : V → α) :
    p (restrictFinset x r (insert a (insert b B))) * p (restrictFinset x r B) =
      p (restrictFinset x r (insert a B)) * p (restrictFinset x r (insert b B)) := by
  have hCI := hPM hab hnab
  have eFull : (({a} ∪ {b} ∪ (({a, b} : Set V))ᶜ)) = Set.univ := by
    ext v
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_compl_iff,
      Set.mem_insert_iff, Set.mem_univ, iff_true]
    tauto
  have eA : (({a} ∪ (({a, b} : Set V))ᶜ)) = (({b}ᶜ : Set V)) := by
    ext v
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_compl_iff,
      Set.mem_insert_iff]
    by_cases hva : v = a
    · subst hva
      simp [hab]
    · simp [hva]
  have eB : (({b} ∪ (({a, b} : Set V))ᶜ)) = (({a}ᶜ : Set V)) := by
    ext v
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_compl_iff,
      Set.mem_insert_iff]
    by_cases hvb : v = b
    · subst hvb
      simp [Ne.symm hab]
    · simp [hvb]
  have e0 := hCI (restrictFinset x r B)
  have ea := hCI (restrictFinset x r (insert a B))
  have eb := hCI (restrictFinset x r (insert b B))
  have eab := hCI (restrictFinset x r (insert a (insert b B)))
  rw [eFull, eA, eB, marginal_univ_general] at e0 ea eb eab
  have hMza : marginal p (({a, b} : Set V))ᶜ (restrictFinset x r (insert a B)) =
      marginal p (({a, b} : Set V))ᶜ (restrictFinset x r B) := by
    apply marginal_congr
    intro v hv
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    have hva : v ≠ a := fun hh => hv (Or.inl hh)
    simp [restrictFinset, hva]
  have hMzb : marginal p (({a, b} : Set V))ᶜ (restrictFinset x r (insert b B)) =
      marginal p (({a, b} : Set V))ᶜ (restrictFinset x r B) := by
    apply marginal_congr
    intro v hv
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    have hvb : v ≠ b := fun hh => hv (Or.inr hh)
    simp [restrictFinset, hvb]
  have hMzab : marginal p (({a, b} : Set V))ᶜ
        (restrictFinset x r (insert a (insert b B))) =
      marginal p (({a, b} : Set V))ᶜ (restrictFinset x r B) := by
    apply marginal_congr
    intro v hv
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    have hva : v ≠ a := fun hh => hv (Or.inl hh)
    have hvb : v ≠ b := fun hh => hv (Or.inr hh)
    simp [restrictFinset, hva, hvb]
  have hAza : marginal p (({a} : Set V))ᶜ (restrictFinset x r (insert a B)) =
      marginal p (({a} : Set V))ᶜ (restrictFinset x r B) := by
    apply marginal_congr
    intro v hv
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hv
    simp [restrictFinset, hv]
  have hAzab : marginal p (({a} : Set V))ᶜ
        (restrictFinset x r (insert a (insert b B))) =
      marginal p (({a} : Set V))ᶜ (restrictFinset x r (insert b B)) := by
    apply marginal_congr
    intro v hv
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hv
    simp [restrictFinset, hv]
  have hBzb : marginal p (({b} : Set V))ᶜ (restrictFinset x r (insert b B)) =
      marginal p (({b} : Set V))ᶜ (restrictFinset x r B) := by
    apply marginal_congr
    intro v hv
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hv
    simp [restrictFinset, hv]
  have hBzab : marginal p (({b} : Set V))ᶜ
        (restrictFinset x r (insert a (insert b B))) =
      marginal p (({b} : Set V))ᶜ (restrictFinset x r (insert a B)) := by
    apply marginal_congr
    intro v hv
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hv
    simp only [restrictFinset]
    by_cases hva : v = a
    · subst hva
      simp [hv]
    · simp [hva, hv]
  rw [hMza, hAza] at ea
  rw [hMzb, hBzb] at eb
  rw [hMzab, hBzab, hAzab] at eab
  have hM : marginal p (({a, b} : Set V))ᶜ (restrictFinset x r B) ≠ 0 :=
    ne_of_gt (marginal_pos_of_pos hp _ _)
  have key : (p (restrictFinset x r (insert a (insert b B))) *
        p (restrictFinset x r B)) *
        (marginal p (({a, b} : Set V))ᶜ (restrictFinset x r B) *
          marginal p (({a, b} : Set V))ᶜ (restrictFinset x r B)) =
      (p (restrictFinset x r (insert a B)) *
        p (restrictFinset x r (insert b B))) *
        (marginal p (({a, b} : Set V))ᶜ (restrictFinset x r B) *
          marginal p (({a, b} : Set V))ᶜ (restrictFinset x r B)) := by
    calc (p (restrictFinset x r (insert a (insert b B))) *
          p (restrictFinset x r B)) *
          (marginal p (({a, b} : Set V))ᶜ (restrictFinset x r B) *
            marginal p (({a, b} : Set V))ᶜ (restrictFinset x r B)) =
          (p (restrictFinset x r (insert a (insert b B))) *
            marginal p (({a, b} : Set V))ᶜ (restrictFinset x r B)) *
            (p (restrictFinset x r B) *
              marginal p (({a, b} : Set V))ᶜ (restrictFinset x r B)) := by ring
      _ = (marginal p (({b} : Set V))ᶜ (restrictFinset x r (insert a B)) *
            marginal p (({a} : Set V))ᶜ (restrictFinset x r (insert b B))) *
            (marginal p (({b} : Set V))ᶜ (restrictFinset x r B) *
              marginal p (({a} : Set V))ᶜ (restrictFinset x r B)) := by
          rw [eab, e0]
      _ = (marginal p (({b} : Set V))ᶜ (restrictFinset x r (insert a B)) *
            marginal p (({a} : Set V))ᶜ (restrictFinset x r B)) *
            (marginal p (({b} : Set V))ᶜ (restrictFinset x r B) *
              marginal p (({a} : Set V))ᶜ (restrictFinset x r (insert b B))) := by ring
      _ = (p (restrictFinset x r (insert a B)) *
            marginal p (({a, b} : Set V))ᶜ (restrictFinset x r B)) *
            (p (restrictFinset x r (insert b B)) *
              marginal p (({a, b} : Set V))ᶜ (restrictFinset x r B)) := by
          rw [ea, eb]
      _ = (p (restrictFinset x r (insert a B)) *
            p (restrictFinset x r (insert b B))) *
            (marginal p (({a, b} : Set V))ᶜ (restrictFinset x r B) *
              marginal p (({a, b} : Set V))ᶜ (restrictFinset x r B)) := by ring
  exact mul_right_cancel₀ (mul_ne_zero hM hM) key

/-- Log interaction potential at `A`: the signed subset Möbius sum of `log p`
over `B ⊆ A`, with coordinates outside `B` fixed to the reference `r`. -/
private noncomputable def logPotential {V α : Type*} [Fintype V] [DecidableEq V]
    (p : (V → α) → ℝ) (r : V → α) (A : Finset V) (x : V → α) : ℝ :=
  ∑ B ∈ A.powerset, ((-1 : ℝ) ^ (A.card - B.card)) * Real.log (p (restrictFinset x r B))

/-- The log potential at `A` sees only the coordinates in `A`. -/
private theorem logPotential_congr {V α : Type*} [Fintype V] [DecidableEq V]
    {p : (V → α) → ℝ} {r x y : V → α} {A : Finset V}
    (h : ∀ v ∈ A, x v = y v) :
    logPotential p r A x = logPotential p r A y := by
  simp only [logPotential]
  refine Finset.sum_congr rfl fun B hB => ?_
  have hBA : B ⊆ A := Finset.mem_powerset.mp hB
  have hR : restrictFinset x r B = restrictFinset y r B :=
    restrictFinset_congr_finset h hBA
  rw [hR]

/-- The exponentiated log potential at `A` depends only on `A`. -/
private theorem dependsOn_exp_logPotential {V α : Type*} [Fintype V] [DecidableEq V]
    {p : (V → α) → ℝ} {r : V → α} {A : Finset V} :
    DependsOn (fun x => Real.exp (logPotential p r A x)) ↑A := by
  intro x y h
  apply congrArg Real.exp
  apply logPotential_congr
  intro v hv
  exact h v (Finset.mem_coe.mpr hv)

/-- Finite subset Möbius identity: the alternating sum of `(-1)^|D|` over
subsets `D ⊆ s` is `1` for `s = ∅` and `0` otherwise. -/
private theorem sum_powerset_neg_one_pow_card {V : Type*} [DecidableEq V] (s : Finset V) :
    ∑ D ∈ s.powerset, (-1 : ℝ) ^ D.card = if s = ∅ then 1 else 0 := by
  have h1 : ∑ D ∈ s.powerset, (-1 : ℝ) ^ D.card
      = ∑ k ∈ Finset.range (s.card + 1), (s.card.choose k : ℝ) * (-1 : ℝ) ^ k := by
    rw [Finset.sum_powerset_apply_card (fun k : ℕ => (-1 : ℝ) ^ k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [nsmul_eq_mul]
  have h2 : ((-1 : ℝ) + 1) ^ s.card
      = ∑ k ∈ Finset.range (s.card + 1), (s.card.choose k : ℝ) * (-1 : ℝ) ^ k := by
    rw [add_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [h1, ← h2]
  have h3 : (-1 : ℝ) + 1 = 0 := by norm_num
  rw [h3]
  by_cases hs : s = ∅
  · subst hs
    simp
  · rw [ite_eq_right hs]
    have hne : s.card ≠ 0 := fun h => hs (Finset.card_eq_zero.mp h)
    exact zero_pow hne

/-- Möbius recovery: the log potentials over all `A ⊆ univ` sum to `log (p x)`. -/
private theorem logPotential_sum_powerset {V α : Type*} [Fintype V] [DecidableEq V]
    {p : (V → α) → ℝ} (r x : V → α) :
    ∑ A ∈ Finset.univ.powerset, logPotential p r A x = Real.log (p x) := by
  classical
  simp only [logPotential]
  trans ∑ q ∈ (Finset.univ.powerset).sigma (fun A => A.powerset),
    ((-1 : ℝ) ^ (q.1.card - q.2.card)) * Real.log (p (restrictFinset x r q.2))
  · rw [Finset.sum_sigma]
  · have hbij : (∑ q ∈ (Finset.univ.powerset).sigma (fun A => A.powerset),
          ((-1 : ℝ) ^ (q.1.card - q.2.card)) * Real.log (p (restrictFinset x r q.2)))
        = ∑ q ∈ (Finset.univ.powerset).sigma (fun B => (Finset.univ \ B).powerset),
          ((-1 : ℝ) ^ q.2.card) * Real.log (p (restrictFinset x r q.1)) := by
      refine Finset.sum_nbij'
        (fun q : Sigma (fun _ : Finset V => Finset V) => Sigma.mk q.2 (q.1 \ q.2))
        (fun q : Sigma (fun _ : Finset V => Finset V) => Sigma.mk (q.1 ∪ q.2) q.1)
        ?_ ?_ ?_ ?_ ?_
      · intro q hq
        simp only [Finset.mem_sigma, Finset.mem_powerset] at hq ⊢
        obtain ⟨hA, hB⟩ := hq
        refine ⟨fun v hv => hA (hB hv), ?_⟩
        intro v hv
        simp only [Finset.mem_sdiff] at hv ⊢
        exact ⟨hA hv.1, hv.2⟩
      · intro q hq
        simp only [Finset.mem_sigma, Finset.mem_powerset] at hq ⊢
        obtain ⟨hB, hC⟩ := hq
        refine ⟨Finset.union_subset hB (fun v hv => Finset.sdiff_subset (hC hv)),
          Finset.subset_union_left⟩
      · intro q hq
        simp only [Finset.mem_sigma, Finset.mem_powerset] at hq
        obtain ⟨hA, hB⟩ := hq
        show Sigma.mk (q.2 ∪ (q.1 \ q.2)) q.2 = q
        have e : q.2 ∪ (q.1 \ q.2) = q.1 := by
          rw [Finset.union_comm, Finset.sdiff_union_of_subset hB]
        rw [e]
      · intro q hq
        simp only [Finset.mem_sigma, Finset.mem_powerset] at hq
        obtain ⟨hB, hC⟩ := hq
        show Sigma.mk q.1 ((q.1 ∪ q.2) \ q.1) = q
        have hdisj : Disjoint q.1 q.2 := by
          rw [Finset.disjoint_left]
          intro v hv1 hv2
          have hv := hC hv2
          simp only [Finset.mem_sdiff] at hv
          exact hv.2 hv1
        have e : (q.1 ∪ q.2) \ q.1 = q.2 := Finset.union_sdiff_cancel_left hdisj
        rw [e]
      · intro q hq
        simp only [Finset.mem_sigma, Finset.mem_powerset] at hq
        obtain ⟨hA, hB⟩ := hq
        show ((-1 : ℝ) ^ (q.1.card - q.2.card)) * Real.log (p (restrictFinset x r q.2))
          = ((-1 : ℝ) ^ (q.1 \ q.2).card) * Real.log (p (restrictFinset x r q.2))
        rw [Finset.card_sdiff_of_subset hB]
    rw [hbij]
    trans ∑ B ∈ Finset.univ.powerset, ∑ C ∈ (Finset.univ \ B).powerset,
      ((-1 : ℝ) ^ C.card) * Real.log (p (restrictFinset x r B))
    · rw [Finset.sum_sigma]
    · trans ∑ B ∈ Finset.univ.powerset,
          Real.log (p (restrictFinset x r B)) * (∑ C ∈ (Finset.univ \ B).powerset, (-1 : ℝ) ^ C.card)
      · refine Finset.sum_congr rfl fun B _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun C _ => ?_
        ring
      · simp only [sum_powerset_neg_one_pow_card]
        have hvanish : ∀ B ∈ Finset.univ.powerset, B ≠ Finset.univ →
            Real.log (p (restrictFinset x r B)) * (if Finset.univ \ B = ∅ then (1 : ℝ) else 0)
              = 0 := by
          intro B hB hBne
          have hsub : B ⊆ Finset.univ := Finset.mem_powerset.mp hB
          have hne : Finset.univ \ B ≠ ∅ := by
            intro hcon
            have hsup : Finset.univ ⊆ B := Finset.sdiff_eq_empty_iff_subset.mp hcon
            have hBeq : B = Finset.univ := by
              ext v
              exact ⟨fun _ => Finset.mem_univ v, fun _ => hsup (Finset.mem_univ v)⟩
            exact hBne hBeq
          rw [ite_eq_right hne, mul_zero]
        have hmem : Finset.univ ∈ Finset.univ.powerset :=
          Finset.mem_powerset.mpr (Finset.subset_univ (Finset.univ : Finset V))
        have hself : (Finset.univ : Finset V) \ Finset.univ = ∅ :=
          Finset.sdiff_eq_empty_iff_subset.mpr (fun v hv => hv)
        rw [Finset.sum_eq_single Finset.univ hvanish (fun h => absurd hmem h)]
        rw [ite_eq_left hself, mul_one, restrictFinset_univ]

/-- Product recovery: under strict positivity, the exponentiated log potentials
over all `A ⊆ univ` multiply to `p x`. -/
private theorem prod_exp_logPotential {V α : Type*} [Fintype V] [DecidableEq V]
    {p : (V → α) → ℝ} (hp : ∀ x, 0 < p x) (r x : V → α) :
    ∏ A ∈ Finset.univ.powerset, Real.exp (logPotential p r A x) = p x := by
  rw [← Real.exp_sum, logPotential_sum_powerset]
  exact Real.exp_log (hp x)

/-- Non-clique witness: a finset whose coercion is not a clique contains two
distinct nonadjacent vertices. -/
private theorem not_isClique_witness {V : Type*} (G : SimpleGraph V) (A : Finset V)
    (hA : ¬ G.IsClique (A : Set V)) :
    ∃ a b, a ∈ A ∧ b ∈ A ∧ a ≠ b ∧ ¬ G.Adj a b := by
  simp only [SimpleGraph.IsClique, Set.Pairwise] at hA
  push Not at hA
  obtain ⟨a, haA, b, hbA, hab, hnab⟩ := hA
  exact ⟨a, b, Finset.mem_coe.mp haA, Finset.mem_coe.mp hbA, hab, hnab⟩

/-- Quartet log cancellation: for a nonedge `a, b` and `B` avoiding both, the
four log terms over `B`, `insert a B`, `insert b B`, `insert a (insert b B)`
cancel with signs `+ - - +`. -/
private theorem log_quartet_cancel {V α : Type*} [Fintype V] [DecidableEq V]
    [Fintype α] {G : SimpleGraph V} {p : (V → α) → ℝ}
    {a b : V} (hab : a ≠ b) (hnab : ¬ G.Adj a b)
    (hPM : PairwiseMarkov G p) (hp : ∀ x, 0 < p x)
    (B : Finset V) (haB : a ∉ B) (hbB : b ∉ B) (x r : V → α) :
    Real.log (p (restrictFinset x r (insert a (insert b B)))) +
        Real.log (p (restrictFinset x r B)) =
      Real.log (p (restrictFinset x r (insert a B))) +
        Real.log (p (restrictFinset x r (insert b B))) := by
  have hq := cross_ratio_quartet hab hnab hPM hp B haB hbB x r
  have hp1 : p (restrictFinset x r (insert a (insert b B))) ≠ 0 := ne_of_gt (hp _)
  have hp2 : p (restrictFinset x r B) ≠ 0 := ne_of_gt (hp _)
  have hp3 : p (restrictFinset x r (insert a B)) ≠ 0 := ne_of_gt (hp _)
  have hp4 : p (restrictFinset x r (insert b B)) ≠ 0 := ne_of_gt (hp _)
  rw [← Real.log_mul hp1 hp2, ← Real.log_mul hp3 hp4, hq]

/-- Vanishing on a double insert: for a nonedge `a ≠ b` with both avoiding `B`,
the log potential at `insert a (insert b B)` is zero. Subsets group into
quartets with signs `+ - - +`, each killed by `log_quartet_cancel`. -/
private theorem logPotential_insert_insert_eq_zero {V α : Type*} [Fintype V]
    [DecidableEq V] [Fintype α] {G : SimpleGraph V} {p : (V → α) → ℝ}
    {a b : V} (hab : a ≠ b) (hnab : ¬ G.Adj a b)
    (hPM : PairwiseMarkov G p) (hp : ∀ x, 0 < p x)
    (B : Finset V) (haB : a ∉ B) (hbB : b ∉ B) (r x : V → α) :
    logPotential p r (insert a (insert b B)) x = 0 := by
  have haB' : a ∉ insert b B := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hab, haB⟩
  have hcardA : (insert a (insert b B)).card = B.card + 2 := by
    rw [Finset.card_insert_of_notMem haB', Finset.card_insert_of_notMem hbB]
  simp only [logPotential]
  rw [Finset.sum_powerset_insert haB', Finset.sum_powerset_insert hbB,
    Finset.sum_powerset_insert hbB]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun C hC => ?_
  have hCB : C ⊆ B := Finset.mem_powerset.mp hC
  have haC : a ∉ C := fun h => haB (hCB h)
  have hbC : b ∉ C := fun h => hbB (hCB h)
  have haC' : a ∉ insert b C := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hab, haC⟩
  have hCcard : C.card ≤ B.card := Finset.card_le_card hCB
  rw [hcardA]
  simp only [Finset.card_insert_of_notMem haC', Finset.card_insert_of_notMem hbC,
    Finset.card_insert_of_notMem haC]
  have e0 : B.card + 2 - C.card = (B.card - C.card) + 2 := by omega
  have e1 : B.card + 2 - (C.card + 1) = (B.card - C.card) + 1 := by omega
  have e2 : B.card + 2 - (C.card + 1 + 1) = (B.card - C.card) := by omega
  rw [e0, e1, e2]
  have hs1 : (-1 : ℝ) ^ ((B.card - C.card) + 1) = -(-1 : ℝ) ^ (B.card - C.card) := by
    rw [pow_succ]
    ring
  have hs2 : (-1 : ℝ) ^ ((B.card - C.card) + 2) = (-1 : ℝ) ^ (B.card - C.card) := by
    rw [pow_add, show (-1 : ℝ) ^ 2 = 1 by norm_num, mul_one]
  rw [hs1, hs2]
  have hq := log_quartet_cancel hab hnab hPM hp C haC hbC x r
  have h0 : Real.log (p (restrictFinset x r C)) -
        Real.log (p (restrictFinset x r (insert b C))) -
        Real.log (p (restrictFinset x r (insert a C))) +
        Real.log (p (restrictFinset x r (insert a (insert b C)))) = 0 := by
    linarith
  have hfac : (((-1 : ℝ) ^ (B.card - C.card)) *
          Real.log (p (restrictFinset x r C)) +
        (-((-1 : ℝ) ^ (B.card - C.card))) *
          Real.log (p (restrictFinset x r (insert b C)))) +
      (((-((-1 : ℝ) ^ (B.card - C.card)))) *
          Real.log (p (restrictFinset x r (insert a C))) +
        (((-1 : ℝ) ^ (B.card - C.card))) *
          Real.log (p (restrictFinset x r (insert a (insert b C))))) =
      ((-1 : ℝ) ^ (B.card - C.card)) *
        (Real.log (p (restrictFinset x r C)) -
          Real.log (p (restrictFinset x r (insert b C))) -
          Real.log (p (restrictFinset x r (insert a C))) +
          Real.log (p (restrictFinset x r (insert a (insert b C))))) := by
    ring
  rw [hfac, h0, mul_zero]

/-- Non-clique vanishing: the log potential at a non-clique finset is zero. -/
private theorem logPotential_eq_zero_of_not_isClique {V α : Type*} [Fintype V]
    [DecidableEq V] [Fintype α] {G : SimpleGraph V} {p : (V → α) → ℝ}
    {A : Finset V} (hA : ¬ G.IsClique (A : Set V))
    (hp : ∀ x, 0 < p x) (hPM : PairwiseMarkov G p)
    (r x : V → α) : logPotential p r A x = 0 := by
  obtain ⟨a, b, haA, hbA, hab, hnab⟩ := not_isClique_witness G A hA
  have hbA' : b ∈ A.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, hbA⟩
  have haB : a ∉ (A.erase a).erase b := by simp
  have hbB : b ∉ (A.erase a).erase b := Finset.notMem_erase b _
  have hAeq : A = insert a (insert b ((A.erase a).erase b)) := by
    rw [Finset.insert_erase hbA', Finset.insert_erase haA]
  rw [hAeq]
  exact logPotential_insert_insert_eq_zero hab hnab hPM hp _ haB hbB r x

/-- Clique potential at a set `C`: the exponentiated log potential at the
finset of `C`. On coercions of finsets this recovers `logPotential` at that
finset (`cliquePotential_coe`). -/
private noncomputable def cliquePotential {V α : Type*} [Fintype V] [DecidableEq V]
    (p : (V → α) → ℝ) (r : V → α) (C : Set V) (x : V → α) : ℝ :=
  Real.exp (logPotential p r (Set.toFinite C).toFinset x)

private theorem toFinite_toFinset_coe {V : Type*} [Fintype V] [DecidableEq V]
    (A : Finset V) : (Set.toFinite (A : Set V)).toFinset = A := by
  apply Finset.coe_injective
  rw [Set.Finite.coe_toFinset]

private theorem cliquePotential_coe {V α : Type*} [Fintype V] [DecidableEq V]
    {p : (V → α) → ℝ} {r : V → α} {A : Finset V} :
    cliquePotential p r (A : Set V) = fun x => Real.exp (logPotential p r A x) := by
  funext x
  simp only [cliquePotential, toFinite_toFinset_coe]

/-- **Hammersley–Clifford, pairwise form.** A strictly positive finite weight
satisfying the pairwise Markov property factorizes over the cliques of the
graph. -/
theorem gibbsFactorization_of_pairwiseMarkov_of_pos {V α : Type*} [Fintype V]
    [DecidableEq V] [Fintype α] {G : SimpleGraph V} {p : (V → α) → ℝ}
    (hp : ∀ x, 0 < p x) (h : PairwiseMarkov G p) : GibbsFactorization G p := by
  classical
  by_cases hempty : Nonempty (V → α)
  · obtain ⟨r⟩ := hempty
    refine ⟨(Finset.univ.powerset.filter
      (fun A : Finset V => G.IsClique (A : Set V))).image
      (fun A : Finset V => (A : Set V)), cliquePotential p r, ?_, ?_, ?_, ?_⟩
    · intro C hC
      rw [Finset.mem_image] at hC
      obtain ⟨A, hA, rfl⟩ := hC
      rw [Finset.mem_filter] at hA
      exact hA.2
    · intro C _ x
      exact Real.exp_nonneg _
    · intro C hC
      rw [Finset.mem_image] at hC
      obtain ⟨A, hA, rfl⟩ := hC
      rw [cliquePotential_coe]
      exact dependsOn_exp_logPotential
    · funext x
      have hinj : Set.InjOn (fun A : Finset V => (A : Set V))
          ↑(Finset.univ.powerset.filter
            (fun A : Finset V => G.IsClique (A : Set V))) := by
        intro A _ B _ hAB
        exact Finset.coe_injective hAB
      have hψ : ∀ A : Finset V, cliquePotential p r (A : Set V) x
          = Real.exp (logPotential p r A x) := fun A => by
        simp only [cliquePotential_coe]
      have hsub : ∏ A ∈ Finset.univ.powerset.filter
            (fun A : Finset V => G.IsClique (A : Set V)),
            Real.exp (logPotential p r A x)
          = ∏ A ∈ Finset.univ.powerset, Real.exp (logPotential p r A x) :=
        Finset.prod_subset (Finset.filter_subset _ _) (fun A hA hAnot => by
          have hnot : ¬ G.IsClique (A : Set V) :=
            fun hc => hAnot (Finset.mem_filter.mpr ⟨hA, hc⟩)
          rw [logPotential_eq_zero_of_not_isClique hnot hp h r x, Real.exp_zero])
      calc p x = ∏ A ∈ Finset.univ.powerset, Real.exp (logPotential p r A x) :=
            (prod_exp_logPotential hp r x).symm
        _ = ∏ A ∈ Finset.univ.powerset.filter
              (fun A : Finset V => G.IsClique (A : Set V)),
              Real.exp (logPotential p r A x) := hsub.symm
        _ = ∏ A ∈ Finset.univ.powerset.filter
              (fun A : Finset V => G.IsClique (A : Set V)),
              cliquePotential p r (A : Set V) x :=
            Finset.prod_congr rfl (fun A _ => (hψ A).symm)
        _ = ∏ C ∈ (Finset.univ.powerset.filter
              (fun A : Finset V => G.IsClique (A : Set V))).image
              (fun A : Finset V => (A : Set V)),
              cliquePotential p r C x :=
            (Finset.prod_image (f := fun C => cliquePotential p r C x) hinj).symm
  · refine ⟨∅, fun _ _ => 0, ?_, ?_, ?_, ?_⟩
    · intro C hC
      exact absurd hC (Finset.notMem_empty C)
    · intro C hC
      exact absurd hC (Finset.notMem_empty C)
    · intro C hC
      exact absurd hC (Finset.notMem_empty C)
    · funext x
      exact absurd ⟨x⟩ hempty

/-- **Hammersley–Clifford, global form.** For a strictly positive finite
weight, the global Markov property (the graph is an I-map) implies clique
factorization. -/
theorem gibbsFactorization_of_globalMarkov_of_pos {V α : Type*} [Fintype V]
    [DecidableEq V] [Fintype α] {G : SimpleGraph V} {p : (V → α) → ℝ}
    (hp : ∀ x, 0 < p x) (h : GlobalMarkov G p) : GibbsFactorization G p := by
  exact gibbsFactorization_of_pairwiseMarkov_of_pos hp
    (pairwiseMarkov_of_localMarkov (fun x => le_of_lt (hp x))
      (localMarkov_of_globalMarkov h))

/-- **Hammersley–Clifford, local form.** For a strictly positive finite
weight, the local Markov property implies clique factorization. -/
theorem gibbsFactorization_of_localMarkov_of_pos {V α : Type*} [Fintype V]
    [DecidableEq V] [Fintype α] {G : SimpleGraph V} {p : (V → α) → ℝ}
    (hp : ∀ x, 0 < p x) (h : LocalMarkov G p) : GibbsFactorization G p := by
  exact gibbsFactorization_of_pairwiseMarkov_of_pos hp
    (pairwiseMarkov_of_localMarkov (fun x => le_of_lt (hp x)) h)

/-- For strictly positive finite weights, Gibbs factorization is equivalent to
the global Markov property. The forward direction is Gibbs soundness. -/
theorem gibbsFactorization_iff_globalMarkov_of_pos {V α : Type*} [Fintype V]
    [DecidableEq V] [Fintype α] {G : SimpleGraph V} {p : (V → α) → ℝ}
    (hp : ∀ x, 0 < p x) : GibbsFactorization G p ↔ GlobalMarkov G p := by
  constructor
  · exact globalMarkov_of_gibbsFactorization
  · exact gibbsFactorization_of_globalMarkov_of_pos hp

/-- For strictly positive finite weights, Gibbs factorization is equivalent to
the pairwise Markov property. -/
theorem gibbsFactorization_iff_pairwiseMarkov_of_pos {V α : Type*} [Fintype V]
    [DecidableEq V] [Fintype α] {G : SimpleGraph V} {p : (V → α) → ℝ}
    (hp : ∀ x, 0 < p x) : GibbsFactorization G p ↔ PairwiseMarkov G p := by
  constructor
  · exact pairwiseMarkov_of_gibbsFactorization
  · exact gibbsFactorization_of_pairwiseMarkov_of_pos hp

/-- The four-cycle on `Fin 4`, with edges `0-1-2-3-0`. -/
def fourCycleGraph : SimpleGraph (Fin 4) where
  Adj a b :=
    (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨
    (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) ∨
    (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) ∨
    (a = 3 ∧ b = 0) ∨ (a = 0 ∧ b = 3)
  symm := ⟨by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all⟩
  loopless := ⟨by
    intro a h
    fin_cases a <;> simp_all⟩

/-- A nonnegative Boolean weight on the four-cycle supported on the three
configurations `1100`, `0010`, and `0001` in coordinates `x₀x₁x₂x₃`. It is
pairwise Markov for `fourCycleGraph` but does not factorize over its cliques,
so positivity is essential in Hammersley–Clifford. -/
def fourCycleWeight (x : Fin 4 → Bool) : ℝ :=
  if (x 0 = true ∧ x 1 = true ∧ x 2 = false ∧ x 3 = false) ∨
      (x 0 = false ∧ x 1 = false ∧ x 2 = true ∧ x 3 = false) ∨
      (x 0 = false ∧ x 1 = false ∧ x 2 = false ∧ x 3 = true) then 1 else 0

private def wNat (x : Fin 4 → Bool) : ℕ :=
  if (x 0 = true ∧ x 1 = true ∧ x 2 = false ∧ x 3 = false) ∨
      (x 0 = false ∧ x 1 = false ∧ x 2 = true ∧ x 3 = false) ∨
      (x 0 = false ∧ x 1 = false ∧ x 2 = false ∧ x 3 = true) then 1 else 0

private lemma weight_cast (y : Fin 4 → Bool) :
    fourCycleWeight y = ↑(wNat y) := by
  simp only [fourCycleWeight, wNat]
  split_ifs <;> norm_num

private lemma pair_union_eq (a b : Fin 4) : (({a} ∪ {b} : Set (Fin 4))) = {a, b} := by
  ext v
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]

private lemma full_union_eq (a b : Fin 4) :
    (({a} ∪ {b} ∪ (({a, b} : Set (Fin 4)))ᶜ)) = Set.univ := by
  rw [pair_union_eq]
  exact Set.union_compl_self _

private lemma aside_union_eq (a b : Fin 4) (h : a ≠ b) :
    (({a} ∪ (({a, b} : Set (Fin 4)))ᶜ)) = (({b}ᶜ : Set (Fin 4))) := by
  ext v
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_insert_iff]
  by_cases hva : v = a
  · subst hva
    simp [h]
  · simp [hva]

private lemma bside_union_eq (a b : Fin 4) (h : a ≠ b) :
    (({b} ∪ (({a, b} : Set (Fin 4)))ᶜ)) = (({a}ᶜ : Set (Fin 4))) := by
  ext v
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_insert_iff]
  by_cases hvb : v = b
  · have h' : b ≠ a := Ne.symm h
    subst hvb
    simp [h']
  · simp [hvb]

private lemma update_true_ne_false (x : Fin 4 → Bool) (c : Fin 4) :
    Function.update x c true ≠ Function.update x c false := by
  intro hcon
  have h2 := congrArg (fun y : Fin 4 → Bool => y c) hcon
  simp only [Function.update_self] at h2
  exact absurd h2 (by decide)

private lemma marginal_compl_singleton (x : Fin 4 → Bool) (c : Fin 4) :
    marginal fourCycleWeight (({c} : Set (Fin 4))ᶜ) x
    = fourCycleWeight (Function.update x c true) + fourCycleWeight (Function.update x c false) := by
  have hsum : (∑ y ∈ ({Function.update x c true, Function.update x c false} : Finset (Fin 4 → Bool)),
        fourCycleWeight y)
      = fourCycleWeight (Function.update x c true) + fourCycleWeight (Function.update x c false) := by
    rw [Finset.sum_insert, Finset.sum_singleton]
    simp only [Finset.mem_singleton]
    exact update_true_ne_false x c
  simp only [marginal]
  rw [← hsum]
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro h
    cases hyc : y c
    · right
      funext v
      by_cases hvc : v = c
      · subst hvc
        rw [hyc, Function.update_self]
      · rw [Function.update_of_ne hvc]
        exact h v hvc
    · left
      funext v
      by_cases hvc : v = c
      · subst hvc
        rw [hyc, Function.update_self]
      · rw [Function.update_of_ne hvc]
        exact h v hvc
  · rintro (rfl | rfl) v hv
    · exact Function.update_of_ne hv true x
    · exact Function.update_of_ne hv false x

private lemma mem_compl_pair {c d v : Fin 4} (hvc : v ≠ c) (hvd : v ≠ d) :
    v ∈ (({c, d} : Set (Fin 4))ᶜ) := by
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact fun hh => hh.elim hvc hvd

private lemma update2_mem (x : Fin 4 → Bool) (c d : Fin 4) (u w : Bool) :
    ∀ v ∈ (({c, d} : Set (Fin 4))ᶜ),
      Function.update (Function.update x c u) d w v = x v := by
  intro v hv
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  have hvc : v ≠ c := fun hh => hv (Or.inl hh)
  have hvd : v ≠ d := fun hh => hv (Or.inr hh)
  rw [Function.update_of_ne hvd, Function.update_of_ne hvc]

private lemma eq_update2 (x y : Fin 4 → Bool) (c d : Fin 4)
    (h : ∀ v ∈ (({c, d} : Set (Fin 4))ᶜ), y v = x v) :
    y = Function.update (Function.update x c (y c)) d (y d) := by
  funext v
  by_cases hvd : v = d
  · subst hvd
    rw [Function.update_self]
  · rw [Function.update_of_ne hvd]
    by_cases hvc : v = c
    · subst hvc
      rw [Function.update_self]
    · rw [Function.update_of_ne hvc]
      exact h v (mem_compl_pair hvc hvd)

private lemma update2_ne_of_d (x : Fin 4 → Bool) (c d : Fin 4) (u : Bool) :
    Function.update (Function.update x c u) d true ≠
      Function.update (Function.update x c u) d false := by
  intro hcon
  have h2 := congrArg (fun y : Fin 4 → Bool => y d) hcon
  simp only [Function.update_self] at h2
  exact absurd h2 (by decide)

private lemma update2_ne_of_c (x : Fin 4 → Bool) (c d : Fin 4) (hcd : c ≠ d)
    (w1 w2 : Bool) :
    Function.update (Function.update x c true) d w1 ≠
      Function.update (Function.update x c false) d w2 := by
  intro hcon
  have h2 := congrArg (fun y : Fin 4 → Bool => y c) hcon
  simp only [Function.update_of_ne hcd, Function.update_self] at h2
  exact absurd h2 (by decide)

private lemma marginal_compl_pair (x : Fin 4 → Bool) (c d : Fin 4) (hcd : c ≠ d) :
    marginal fourCycleWeight ((({c, d} : Set (Fin 4)))ᶜ) x
    = fourCycleWeight (Function.update (Function.update x c true) d true)
      + (fourCycleWeight (Function.update (Function.update x c true) d false)
      + (fourCycleWeight (Function.update (Function.update x c false) d true)
      + fourCycleWeight (Function.update (Function.update x c false) d false))) := by
  have hsum : (∑ y ∈ ({Function.update (Function.update x c true) d true,
        Function.update (Function.update x c true) d false,
        Function.update (Function.update x c false) d true,
        Function.update (Function.update x c false) d false} : Finset (Fin 4 → Bool)),
        fourCycleWeight y)
      = fourCycleWeight (Function.update (Function.update x c true) d true)
      + (fourCycleWeight (Function.update (Function.update x c true) d false)
      + (fourCycleWeight (Function.update (Function.update x c false) d true)
      + fourCycleWeight (Function.update (Function.update x c false) d false))) := by
    rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
    · simp only [Finset.mem_singleton]
      exact update2_ne_of_d x c d false
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨?_, ?_⟩
      · exact update2_ne_of_c x c d hcd false true
      · exact update2_ne_of_c x c d hcd false false
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨?_, ?_, ?_⟩
      · exact update2_ne_of_d x c d true
      · exact update2_ne_of_c x c d hcd true true
      · exact update2_ne_of_c x c d hcd true false
  simp only [marginal]
  rw [← hsum]
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro h
    cases hyc : y c <;> cases hyd : y d <;> rw [eq_update2 x y c d h] <;> simp [hyc, hyd]
  · rintro (rfl | rfl | rfl | rfl)
    · exact update2_mem x c d true true
    · exact update2_mem x c d true false
    · exact update2_mem x c d false true
    · exact update2_mem x c d false false

private lemma marginal_univ_eq (x : Fin 4 → Bool) :
    marginal fourCycleWeight Set.univ x = fourCycleWeight x := by
  have h1 : fourCycleWeight x = ∑ y ∈ ({x} : Finset (Fin 4 → Bool)), fourCycleWeight y :=
    (Finset.sum_singleton fourCycleWeight x).symm
  simp only [marginal]
  rw [h1]
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    funext v
    exact h v (Set.mem_univ v)
  · intro h
    rw [h]
    intro v _
    rfl

private lemma pair02 :
    CondIndep fourCycleWeight {0} {2} ((({0, 2} : Set (Fin 4)))ᶜ) := by
  have key : ∀ x : Fin 4 → Bool,
      wNat x * (wNat (Function.update (Function.update x 0 true) 2 true)
        + (wNat (Function.update (Function.update x 0 true) 2 false)
        + (wNat (Function.update (Function.update x 0 false) 2 true)
        + wNat (Function.update (Function.update x 0 false) 2 false))))
      = (wNat (Function.update x 2 true) + wNat (Function.update x 2 false))
        * (wNat (Function.update x 0 true) + wNat (Function.update x 0 false)) := by
    decide
  intro x
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  rw [full_union_eq 0 2, aside_union_eq 0 2 h02, bside_union_eq 0 2 h02]
  rw [marginal_univ_eq, marginal_compl_pair x 0 2 h02, marginal_compl_singleton x 2,
    marginal_compl_singleton x 0]
  simp only [weight_cast]
  simp only [← Nat.cast_add]
  rw [← Nat.cast_mul, ← Nat.cast_mul, key x]

private lemma pair20 :
    CondIndep fourCycleWeight {2} {0} ((({2, 0} : Set (Fin 4)))ᶜ) := by
  have key : ∀ x : Fin 4 → Bool,
      wNat x * (wNat (Function.update (Function.update x 2 true) 0 true)
        + (wNat (Function.update (Function.update x 2 true) 0 false)
        + (wNat (Function.update (Function.update x 2 false) 0 true)
        + wNat (Function.update (Function.update x 2 false) 0 false))))
      = (wNat (Function.update x 0 true) + wNat (Function.update x 0 false))
        * (wNat (Function.update x 2 true) + wNat (Function.update x 2 false)) := by
    decide
  intro x
  have h20 : (2 : Fin 4) ≠ 0 := by decide
  rw [full_union_eq 2 0, aside_union_eq 2 0 h20, bside_union_eq 2 0 h20]
  rw [marginal_univ_eq, marginal_compl_pair x 2 0 h20, marginal_compl_singleton x 0,
    marginal_compl_singleton x 2]
  simp only [weight_cast]
  simp only [← Nat.cast_add]
  rw [← Nat.cast_mul, ← Nat.cast_mul, key x]

private lemma pair13 :
    CondIndep fourCycleWeight {1} {3} ((({1, 3} : Set (Fin 4)))ᶜ) := by
  have key : ∀ x : Fin 4 → Bool,
      wNat x * (wNat (Function.update (Function.update x 1 true) 3 true)
        + (wNat (Function.update (Function.update x 1 true) 3 false)
        + (wNat (Function.update (Function.update x 1 false) 3 true)
        + wNat (Function.update (Function.update x 1 false) 3 false))))
      = (wNat (Function.update x 3 true) + wNat (Function.update x 3 false))
        * (wNat (Function.update x 1 true) + wNat (Function.update x 1 false)) := by
    decide
  intro x
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  rw [full_union_eq 1 3, aside_union_eq 1 3 h13, bside_union_eq 1 3 h13]
  rw [marginal_univ_eq, marginal_compl_pair x 1 3 h13, marginal_compl_singleton x 3,
    marginal_compl_singleton x 1]
  simp only [weight_cast]
  simp only [← Nat.cast_add]
  rw [← Nat.cast_mul, ← Nat.cast_mul, key x]

private lemma pair31 :
    CondIndep fourCycleWeight {3} {1} ((({3, 1} : Set (Fin 4)))ᶜ) := by
  have key : ∀ x : Fin 4 → Bool,
      wNat x * (wNat (Function.update (Function.update x 3 true) 1 true)
        + (wNat (Function.update (Function.update x 3 true) 1 false)
        + (wNat (Function.update (Function.update x 3 false) 1 true)
        + wNat (Function.update (Function.update x 3 false) 1 false))))
      = (wNat (Function.update x 1 true) + wNat (Function.update x 1 false))
        * (wNat (Function.update x 3 true) + wNat (Function.update x 3 false)) := by
    decide
  intro x
  have h31 : (3 : Fin 4) ≠ 1 := by decide
  rw [full_union_eq 3 1, aside_union_eq 3 1 h31, bside_union_eq 3 1 h31]
  rw [marginal_univ_eq, marginal_compl_pair x 3 1 h31, marginal_compl_singleton x 1,
    marginal_compl_singleton x 3]
  simp only [weight_cast]
  simp only [← Nat.cast_add]
  rw [← Nat.cast_mul, ← Nat.cast_mul, key x]

private def x0 : Fin 4 → Bool := fun _ => false
private def s1 : Fin 4 → Bool := ![true, true, false, false]
private def s2 : Fin 4 → Bool := ![false, false, true, false]
private def s3 : Fin 4 → Bool := ![false, false, false, true]

private lemma wx0 : fourCycleWeight x0 = 0 := by
  simp [fourCycleWeight, x0]

private lemma ws1 : fourCycleWeight s1 = 1 := by
  have h : (s1 0 = true ∧ s1 1 = true ∧ s1 2 = false ∧ s1 3 = false) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> decide
  simp only [fourCycleWeight]
  split_ifs with hc
  · rfl
  · exact absurd (Or.inl h) hc

private lemma ws2 : fourCycleWeight s2 = 1 := by
  have h : (s2 0 = false ∧ s2 1 = false ∧ s2 2 = true ∧ s2 3 = false) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> decide
  simp only [fourCycleWeight]
  split_ifs with hc
  · rfl
  · exact absurd (Or.inr (Or.inl h)) hc

private lemma ws3 : fourCycleWeight s3 = 1 := by
  have h : (s3 0 = false ∧ s3 1 = false ∧ s3 2 = false ∧ s3 3 = true) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> decide
  simp only [fourCycleWeight]
  split_ifs with hc
  · rfl
  · exact absurd (Or.inr (Or.inr h)) hc

private lemma hag1 : ∀ v ∈ (({2, 3} : Set (Fin 4))), s1 v = x0 v := by
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  cases hv with
  | inl h => subst h; decide
  | inr h => subst h; decide

private lemma hag2 : ∀ v ∈ (({0, 1, 3} : Set (Fin 4))), s2 v = x0 v := by
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  cases hv with
  | inl h => subst h; decide
  | inr h =>
    cases h with
    | inl h2 => subst h2; decide
    | inr h2 => subst h2; decide

private lemma hag3 : ∀ v ∈ (({0, 1, 2} : Set (Fin 4))), s3 v = x0 v := by
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  cases hv with
  | inl h => subst h; decide
  | inr h =>
    cases h with
    | inl h2 => subst h2; decide
    | inr h2 => subst h2; decide

private lemma hcover (C : Set (Fin 4)) (hC : fourCycleGraph.IsClique C) :
    C ⊆ ({2, 3} : Set (Fin 4)) ∨ C ⊆ ({0, 1, 3} : Set (Fin 4))
      ∨ C ⊆ ({0, 1, 2} : Set (Fin 4)) := by
  by_cases h1 : C ⊆ ({2, 3} : Set (Fin 4))
  · exact Or.inl h1
  · by_cases h2 : C ⊆ ({0, 1, 3} : Set (Fin 4))
    · exact Or.inr (Or.inl h2)
    · by_cases h3 : C ⊆ ({0, 1, 2} : Set (Fin 4))
      · exact Or.inr (Or.inr h3)
      · exfalso
        obtain ⟨c1, hc1C, hc1⟩ := Set.not_subset.mp h1
        obtain ⟨c2, hc2C, hc2⟩ := Set.not_subset.mp h2
        obtain ⟨c3, hc3C, hc3⟩ := Set.not_subset.mp h3
        have hc1' : c1 = 0 ∨ c1 = 1 := by
          fin_cases c1 <;> simp_all
        have hc2' : c2 = 2 := by
          fin_cases c2 <;> simp_all
        have hc3' : c3 = 3 := by
          fin_cases c3 <;> simp_all
        subst hc2'
        subst hc3'
        cases hc1' with
        | inl h10 =>
          subst h10
          have hAdj := hC hc1C hc2C (by decide : (0 : Fin 4) ≠ 2)
          simp [fourCycleGraph] at hAdj
        | inr h11 =>
          subst h11
          have hAdj := hC hc1C hc3C (by decide : (1 : Fin 4) ≠ 3)
          simp [fourCycleGraph] at hAdj

theorem fourCycleWeight_nonneg : ∀ x, 0 ≤ fourCycleWeight x := by
  intro x
  simp only [fourCycleWeight]
  split_ifs <;> norm_num

theorem fourCycleWeight_pairwiseMarkov :
    PairwiseMarkov fourCycleGraph fourCycleWeight := by
  intro a b hab hnab
  fin_cases a <;> fin_cases b
  · exact (hab rfl).elim
  · exact (hnab (by simp [fourCycleGraph])).elim
  · exact pair02
  · exact (hnab (by simp [fourCycleGraph])).elim
  · exact (hnab (by simp [fourCycleGraph])).elim
  · exact (hab rfl).elim
  · exact (hnab (by simp [fourCycleGraph])).elim
  · exact pair13
  · exact pair20
  · exact (hnab (by simp [fourCycleGraph])).elim
  · exact (hab rfl).elim
  · exact (hnab (by simp [fourCycleGraph])).elim
  · exact (hnab (by simp [fourCycleGraph])).elim
  · exact pair31
  · exact (hnab (by simp [fourCycleGraph])).elim
  · exact (hab rfl).elim

theorem fourCycleWeight_not_gibbsFactorization :
    ¬ GibbsFactorization fourCycleGraph fourCycleWeight := by
  rintro ⟨𝒞, ψ, hcl, hnn, hdep, hp⟩
  have hprod0 : ∏ C ∈ 𝒞, ψ C x0 = 0 := by
    have h : fourCycleWeight x0 = ∏ C ∈ 𝒞, ψ C x0 := congrFun hp x0
    rw [wx0] at h
    exact h.symm
  have hex : ∃ C0 ∈ 𝒞, ψ C0 x0 = 0 := by
    by_contra hcon
    have hcon' : ∀ C0 ∈ 𝒞, ψ C0 x0 ≠ 0 := by
      intro C0 hmem hzero
      exact hcon ⟨C0, hmem, hzero⟩
    have hne := Finset.prod_ne_zero_iff.mpr hcon'
    exact hne hprod0
  obtain ⟨C0, hC0mem, hC0zero⟩ := hex
  have hC0clique := hcl C0 hC0mem
  have hC0dep := hdep C0 hC0mem
  rcases hcover C0 hC0clique with hsub | hsub | hsub
  · have hag : ∀ v ∈ C0, s1 v = x0 v := fun v hv => hag1 v (hsub hv)
    have hψ : ψ C0 s1 = ψ C0 x0 := hC0dep hag
    have hψ0 : ψ C0 s1 = 0 := by rw [hψ, hC0zero]
    have hprod1 : ∏ C ∈ 𝒞, ψ C s1 = 0 := Finset.prod_eq_zero hC0mem hψ0
    have h : fourCycleWeight s1 = ∏ C ∈ 𝒞, ψ C s1 := congrFun hp s1
    rw [ws1] at h
    rw [hprod1] at h
    exact one_ne_zero h
  · have hag : ∀ v ∈ C0, s2 v = x0 v := fun v hv => hag2 v (hsub hv)
    have hψ : ψ C0 s2 = ψ C0 x0 := hC0dep hag
    have hψ0 : ψ C0 s2 = 0 := by rw [hψ, hC0zero]
    have hprod1 : ∏ C ∈ 𝒞, ψ C s2 = 0 := Finset.prod_eq_zero hC0mem hψ0
    have h : fourCycleWeight s2 = ∏ C ∈ 𝒞, ψ C s2 := congrFun hp s2
    rw [ws2] at h
    rw [hprod1] at h
    exact one_ne_zero h
  · have hag : ∀ v ∈ C0, s3 v = x0 v := fun v hv => hag3 v (hsub hv)
    have hψ : ψ C0 s3 = ψ C0 x0 := hC0dep hag
    have hψ0 : ψ C0 s3 = 0 := by rw [hψ, hC0zero]
    have hprod1 : ∏ C ∈ 𝒞, ψ C s3 = 0 := Finset.prod_eq_zero hC0mem hψ0
    have h : fourCycleWeight s3 = ∏ C ∈ 𝒞, ψ C s3 := congrFun hp s3
    rw [ws3] at h
    rw [hprod1] at h
    exact one_ne_zero h

theorem fourCycleWeight_not_pos : ¬ ∀ x, 0 < fourCycleWeight x := by
  intro h
  have h0 := h (fun _ => false)
  simp only [fourCycleWeight] at h0
  simp at h0

end Cslib.MachineLearning.GraphicalModels
