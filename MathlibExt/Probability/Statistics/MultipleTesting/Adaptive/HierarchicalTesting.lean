/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Basic

/-!
# Hierarchical testing (Meinshausen): family-wise error control along a tree

Meinshausen (2008) tests the importance of groups of variables arranged in a hierarchy. Variables
are indexed by `Fin m`; each node of the hierarchy is a cluster `C ⊆ Fin m` carrying a hypothesis
`H_C` (in Meinshausen's setting, "no variable in `C` matters", so `H_C` is a true null exactly
when `C` is contained in the set `N` of null variables). The clusters form a *tree*: any two are
either nested or disjoint (`IsLaminar`). The ancestors of a cluster are the clusters of the tree
that strictly contain it; for a nonempty node of the tree, the parent is the smallest of them
(`IsParent`).
(The empty cluster lies below every cluster, so its ancestors need not be nested.)

## The procedure

Each node `C` gets a level `a C`. The hierarchical procedure tests the roots first and descends:
a node is tested only if its parent was rejected, and it is rejected if its p-value is at most its
level. Equivalently (`hierRejections`), `C` is rejected exactly when every cluster of the tree
containing `C` (itself and all its ancestors) has p-value at most its level.
`mem_hierRejections_iff_parent` and `mem_hierRejections_iff_root` show that this is the top-down
"test only if the parent rejected" procedure, and `exists_isParent` that every nonempty node
below a root has a parent.

Meinshausen's level allocation is `a C = α |C| / m` (`meinshausenLevel`): a cluster gets the
share of `α` proportional to its size, so the levels of the children of a node sum to at most the
level of the node, and the levels of pairwise disjoint clusters sum to at most `α`.

## FWER control under arbitrary dependence

Suppose a family-wise error occurs: some true-null node `C` is rejected. Let `D` be a maximal
true-null node containing `C`. Since `C` was rejected, every cluster containing `C` passed its
level, in particular `p D ≤ a D`. Maximal true-null nodes are pairwise disjoint (two nested
distinct ones would contradict maximality), so the union bound gives
`FWER ≤ ∑_{D maximal} a D`, which is at most `α` as soon as the levels of any pairwise
disjoint family of true-null nodes sum to at most `α` (`measure_hier_familywiseError_le`).
For Meinshausen's levels this sum is `α |⋃ D| / m ≤ α |N| / m`
(`measure_meinshausen_familywiseError_le_card`, `measure_meinshausen_familywiseError_le`).

## Conditions, stated explicitly

* **Validity**: the p-value of every true-null node is super-uniform (`IsValidPValue`). Nothing is
  assumed about false-null nodes.
* **Dependence**: none. The proof is a union bound; the p-values of different nodes may be
  arbitrarily dependent.
* **Tree structure**: the clusters form a laminar family. This is used to make the maximal
  true-null nodes pairwise disjoint. The set of true-null nodes is arbitrary in the general theorem
  (it need not be closed under taking sub-clusters).
* **Fixed levels**: the levels `a C` do not depend on the data.

## Main results

* `mem_hierRejections_iff_parent`, `mem_hierRejections_iff_root`, `exists_isParent`: the
  procedure tests a node only if its parent rejected.
* `hierRejections_upward_closed`: a rejected cluster has all its ancestors rejected.
* `measure_hier_familywiseError_le`: FWER control for any level allocation whose sum over
  pairwise disjoint true-null nodes is at most `α`.
* `sum_meinshausenLevel_of_pairwiseDisjoint`, `sum_meinshausenLevel_le_of_subset`: the level
  allocation `α |C| / m` sums correctly over disjoint clusters.
* `measure_meinshausen_familywiseError_le_card`: Meinshausen's procedure has FWER at most
  `α |N| / m` when every true-null node lies inside the null set `N`.
* `measure_meinshausen_familywiseError_le`: Meinshausen's procedure has FWER at most `α`.

## Comparison with Storey-BH

The adaptive Storey-BH procedure (`MultipleTesting.Adaptive.StoreyBH`) controls the *false
discovery rate* and needs independence of each null p-value from the rest. Hierarchical testing
controls the stronger *family-wise error rate* and needs no independence; it gains power over
Bonferroni on the leaves by spending the level `α |C| / m` on coarse clusters first, so large
clusters are tested at nearly the full level `α`.

## Not covered

Meinshausen's construction of cluster p-values from a regression model (multi-sample splitting),
the Shaffer-type improvement that redistributes level from accepted siblings, Goeman–Finos
sequential rejection with level reallocation, and FDR versions of hierarchical testing (Yekutieli)
are not formalized.

## References

* N. Meinshausen, *Hierarchical testing of variable importance*, Biometrika 95 (2008), 265–278.
* J. J. Goeman and L. Finos, *The inheritance procedure: multiple testing of tree-structured
  hypotheses*, Stat. Appl. Genet. Mol. Biol. 11 (2012), Art. 11.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.MultipleTesting

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}

/-- A family of clusters is *laminar* (tree-structured) if any two of its members are nested or
disjoint. -/
def IsLaminar (T : Finset (Finset (Fin m))) : Prop :=
  ∀ A ∈ T, ∀ B ∈ T, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

/-- `D` is the parent of the node `C` in the tree `T`: `C` and `D` are clusters of `T`, `D`
strictly contains `C`, and `D` is contained in every cluster of `T` strictly containing `C`. -/
def IsParent (T : Finset (Finset (Fin m))) (C D : Finset (Fin m)) : Prop :=
  C ∈ T ∧ D ∈ T ∧ C ⊂ D ∧ ∀ E ∈ T, C ⊂ E → D ⊆ E

/-- The clusters rejected by the hierarchical procedure on the tree `T` with levels `a` and
observed p-values `p`: a cluster is rejected when it and every cluster of `T` containing it have
p-value at most their level. -/
noncomputable def hierRejections (T : Finset (Finset (Fin m))) (a p : Finset (Fin m) → ℝ) :
    Finset (Finset (Fin m)) := by
  classical
  exact T.filter fun C => ∀ D ∈ T, C ⊆ D → p D ≤ a D

/-- Meinshausen's level allocation: the cluster `C` is tested at level `α |C| / m`. -/
noncomputable def meinshausenLevel (α : ℝ) (C : Finset (Fin m)) : ℝ :=
  α * C.card / m

/-- Membership in the hierarchical rejection set. -/
theorem mem_hierRejections {T : Finset (Finset (Fin m))} {a p : Finset (Fin m) → ℝ}
    {C : Finset (Fin m)} :
    C ∈ hierRejections T a p ↔ C ∈ T ∧ ∀ D ∈ T, C ⊆ D → p D ≤ a D := by
  classical
  unfold hierRejections
  convert Finset.mem_filter (s := T) (p := fun C => ∀ D ∈ T, C ⊆ D → p D ≤ a D)

/-- The rejected clusters belong to the tree. -/
theorem hierRejections_subset (T : Finset (Finset (Fin m))) (a p : Finset (Fin m) → ℝ) :
    hierRejections T a p ⊆ T :=
  fun _ hC => (mem_hierRejections.mp hC).1

/-- A rejected cluster passed its own level. -/
theorem le_of_mem_hierRejections {T : Finset (Finset (Fin m))} {a p : Finset (Fin m) → ℝ}
    {C : Finset (Fin m)} (hC : C ∈ hierRejections T a p) : p C ≤ a C :=
  (mem_hierRejections.mp hC).2 C (mem_hierRejections.mp hC).1 subset_rfl

/-- **Hierarchical consistency.** If a cluster is rejected, so is every cluster of the tree that
contains it. -/
theorem hierRejections_upward_closed {T : Finset (Finset (Fin m))} {a p : Finset (Fin m) → ℝ}
    {C D : Finset (Fin m)} (hC : C ∈ hierRejections T a p) (hD : D ∈ T) (hCD : C ⊆ D) :
    D ∈ hierRejections T a p :=
  mem_hierRejections.mpr ⟨hD, fun E hE hDE => (mem_hierRejections.mp hC).2 E hE (hCD.trans hDE)⟩

/-- **A node is tested only if its parent rejected.** If `D` is the parent of `C`, then `C` is
rejected exactly when its p-value is at most its level and `D` is rejected. -/
theorem mem_hierRejections_iff_parent {T : Finset (Finset (Fin m))} {a p : Finset (Fin m) → ℝ}
    {C D : Finset (Fin m)} (hpar : IsParent T C D) :
    C ∈ hierRejections T a p ↔ p C ≤ a C ∧ D ∈ hierRejections T a p := by
  obtain ⟨hCT, hD, hCD, hmin⟩ := hpar
  constructor
  · intro hC
    exact ⟨le_of_mem_hierRejections hC, hierRejections_upward_closed hC hD hCD.subset⟩
  · rintro ⟨hpC, hDR⟩
    refine mem_hierRejections.mpr ⟨hCT, fun E hE hCE => ?_⟩
    rcases eq_or_ne C E with rfl | hne
    · exact hpC
    · exact (mem_hierRejections.mp hDR).2 E hE (hmin E hE (Finset.ssubset_iff_subset_ne.mpr
        ⟨hCE, hne⟩))

/-- **Roots are tested unconditionally.** A cluster of the tree with no strict superset in the
tree is rejected exactly when its p-value is at most its level. -/
theorem mem_hierRejections_iff_root {T : Finset (Finset (Fin m))} {a p : Finset (Fin m) → ℝ}
    {C : Finset (Fin m)} (hroot : ∀ E ∈ T, ¬ C ⊂ E) :
    C ∈ hierRejections T a p ↔ C ∈ T ∧ p C ≤ a C := by
  constructor
  · intro hC
    exact ⟨(mem_hierRejections.mp hC).1, le_of_mem_hierRejections hC⟩
  · rintro ⟨hCT, hpC⟩
    refine mem_hierRejections.mpr ⟨hCT, fun E hE hCE => ?_⟩
    rcases eq_or_ne C E with rfl | hne
    · exact hpC
    · exact absurd (Finset.ssubset_iff_subset_ne.mpr ⟨hCE, hne⟩) (hroot E hE)

/-- **Every nonempty node with a strict superset in a tree has a parent**: the smallest
cluster of the tree strictly containing it. -/
theorem exists_isParent {T : Finset (Finset (Fin m))} (hT : IsLaminar T) {C : Finset (Fin m)}
    (hC : C ∈ T) (hne : C.Nonempty) (hsup : ∃ E ∈ T, C ⊂ E) : ∃ D, IsParent T C D := by
  classical
  set S := T.filter fun E => C ⊂ E with hS
  have hSne : S.Nonempty := by
    obtain ⟨E, hE, hCE⟩ := hsup
    exact ⟨E, Finset.mem_filter.mpr ⟨hE, hCE⟩⟩
  obtain ⟨D, hDS, hDmin⟩ := S.exists_min_image Finset.card hSne
  obtain ⟨hD, hCD⟩ := Finset.mem_filter.mp hDS
  refine ⟨D, hC, hD, hCD, fun E hE hCE => ?_⟩
  rcases hT D hD E hE with h | h | h
  · exact h
  · have hcard := hDmin E (Finset.mem_filter.mpr ⟨hE, hCE⟩)
    exact (Finset.eq_of_subset_of_card_le h hcard).symm ▸ subset_rfl
  · obtain ⟨x, hx⟩ := hne
    exact absurd (hCE.subset hx) (Finset.disjoint_left.mp h (hCD.subset hx))

/-! ### FWER control for a general level allocation -/

/-- The maximal elements of a family of clusters. -/
noncomputable def maximalClusters (H : Finset (Finset (Fin m))) : Finset (Finset (Fin m)) := by
  classical
  exact H.filter fun C => ∀ D ∈ H, C ⊆ D → D = C

/-- Every member of a finite family of clusters lies inside a maximal member. -/
theorem exists_maximalClusters_superset {H : Finset (Finset (Fin m))} {C : Finset (Fin m)}
    (hC : C ∈ H) : ∃ D ∈ maximalClusters H, C ⊆ D := by
  classical
  set S := H.filter fun D => C ⊆ D with hS
  have hSne : S.Nonempty := ⟨C, Finset.mem_filter.mpr ⟨hC, subset_rfl⟩⟩
  obtain ⟨D, hDS, hDmax⟩ := S.exists_max_image Finset.card hSne
  obtain ⟨hD, hCD⟩ := Finset.mem_filter.mp hDS
  refine ⟨D, ?_, hCD⟩
  unfold maximalClusters
  refine Finset.mem_filter.mpr ⟨hD, fun E hE hDE => ?_⟩
  exact (Finset.eq_of_subset_of_card_le hDE
    (hDmax E (Finset.mem_filter.mpr ⟨hE, hCD.trans hDE⟩))).symm

/-- The maximal members of a family of clusters form a subfamily. -/
theorem maximalClusters_subset (H : Finset (Finset (Fin m))) : maximalClusters H ⊆ H := by
  classical
  unfold maximalClusters
  exact Finset.filter_subset _ _

/-- In a laminar family, the maximal members of any subfamily are pairwise disjoint. -/
theorem pairwiseDisjoint_maximalClusters {T H : Finset (Finset (Fin m))} (hT : IsLaminar T)
    (hH : H ⊆ T) :
    ((maximalClusters H : Finset (Finset (Fin m))) : Set (Finset (Fin m))).PairwiseDisjoint id := by
  classical
  intro D hD E hE hne
  have hD' : D ∈ maximalClusters H := hD
  have hE' : E ∈ maximalClusters H := hE
  unfold maximalClusters at hD' hE'
  obtain ⟨hDH, hDmax⟩ := Finset.mem_filter.mp hD'
  obtain ⟨hEH, hEmax⟩ := Finset.mem_filter.mp hE'
  rcases hT D (hH hDH) E (hH hEH) with h | h | h
  · exact absurd (hDmax E hEH h).symm hne
  · exact absurd (hEmax D hDH h) hne
  · exact h

/-- **Hierarchical testing controls the FWER under arbitrary dependence.** Let `T` be a tree of
clusters and `H0 ⊆ T` the true-null nodes. Assume every true-null p-value is valid, every
true-null level lies in `[0, 1]`, and the levels of any pairwise disjoint family of true-null
nodes sum to at most `α`. Then the hierarchical procedure rejects some true-null node with
probability at most `α`. No assumption is made on the dependence between p-values.

Source: Meinshausen (2008), Theorem 1, for the level allocation `α |C| / m`. -/
theorem measure_hier_familywiseError_le (μ : Measure Ω) {T : Finset (Finset (Fin m))}
    (hT : IsLaminar T) (a : Finset (Fin m) → ℝ) (p : Finset (Fin m) → Ω → ℝ)
    {H0 : Finset (Finset (Fin m))} (hH0 : H0 ⊆ T) (hnull : ∀ C ∈ H0, IsValidPValue μ (p C))
    (ha : ∀ C ∈ H0, a C ∈ Set.Icc (0 : ℝ) 1) {α : ℝ}
    (hsum : ∀ S ⊆ H0, (S : Set (Finset (Fin m))).PairwiseDisjoint id → ∑ C ∈ S, a C ≤ α) :
    μ {ω | (hierRejections T a (fun C => p C ω) ∩ H0).Nonempty} ≤ ENNReal.ofReal α := by
  set M := maximalClusters H0 with hM
  have hMH : M ⊆ H0 := maximalClusters_subset H0
  have hsub : {ω | (hierRejections T a (fun C => p C ω) ∩ H0).Nonempty} ⊆
      ⋃ D ∈ M, {ω | p D ω ≤ a D} := by
    rintro ω ⟨C, hC⟩
    obtain ⟨hCR, hCH⟩ := Finset.mem_inter.mp hC
    obtain ⟨D, hDM, hCD⟩ := exists_maximalClusters_superset hCH
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    exact ⟨D, hDM, (mem_hierRejections.mp hCR).2 D (hH0 (hMH hDM)) hCD⟩
  calc μ {ω | (hierRejections T a (fun C => p C ω) ∩ H0).Nonempty}
      ≤ μ (⋃ D ∈ M, {ω | p D ω ≤ a D}) := measure_mono hsub
    _ ≤ ∑ D ∈ M, μ {ω | p D ω ≤ a D} := measure_biUnion_finset_le M _
    _ ≤ ∑ D ∈ M, ENNReal.ofReal (a D) :=
        Finset.sum_le_sum fun D hD => hnull D (hMH hD) (a D) (ha D (hMH hD))
    _ = ENNReal.ofReal (∑ D ∈ M, a D) :=
        (ENNReal.ofReal_sum_of_nonneg fun D hD => (ha D (hMH hD)).1).symm
    _ ≤ ENNReal.ofReal α :=
        ENNReal.ofReal_le_ofReal (hsum M hMH (pairwiseDisjoint_maximalClusters hT hH0))

/-! ### Meinshausen's level allocation `α |C| / m` -/

/-- The levels `α |C| / m` of pairwise disjoint clusters sum to `α |⋃ C| / m`. -/
theorem sum_meinshausenLevel_of_pairwiseDisjoint (α : ℝ) {S : Finset (Finset (Fin m))}
    (hS : (S : Set (Finset (Fin m))).PairwiseDisjoint id) :
    ∑ C ∈ S, meinshausenLevel α C = meinshausenLevel α (S.biUnion id) := by
  classical
  have hcard : (S.biUnion id).card = ∑ C ∈ S, C.card :=
    Finset.card_biUnion fun x hx y hy hxy => hS hx hy hxy
  simp only [meinshausenLevel, hcard, Nat.cast_sum, Finset.mul_sum, Finset.sum_div]

/-- The levels `α |C| / m` of pairwise disjoint clusters inside `N` sum to at most
`α |N| / m`, for `α ≥ 0`. -/
theorem sum_meinshausenLevel_le_of_subset {α : ℝ} (hα : 0 ≤ α) {S : Finset (Finset (Fin m))}
    (hS : (S : Set (Finset (Fin m))).PairwiseDisjoint id) {N : Finset (Fin m)}
    (hN : ∀ C ∈ S, C ⊆ N) : ∑ C ∈ S, meinshausenLevel α C ≤ α * N.card / m := by
  classical
  rw [sum_meinshausenLevel_of_pairwiseDisjoint α hS, meinshausenLevel]
  have hsub : S.biUnion id ⊆ N := Finset.biUnion_subset.mpr hN
  have hc : ((S.biUnion id).card : ℝ) ≤ N.card := by exact_mod_cast Finset.card_le_card hsub
  gcongr

/-- Meinshausen's levels lie in `[0, 1]` for `α ∈ [0, 1]`. -/
theorem meinshausenLevel_mem_Icc {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) (C : Finset (Fin m)) :
    meinshausenLevel α C ∈ Set.Icc (0 : ℝ) 1 := by
  unfold meinshausenLevel
  refine ⟨by positivity, ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hC : (C.card : ℝ) ≤ m := by
    exact_mod_cast (Finset.card_le_univ C).trans_eq (Fintype.card_fin m)
  rw [div_le_one hm']
  nlinarith

/-- **Meinshausen's hierarchical procedure controls the FWER at `α |N| / m`.** If every
true-null node is contained in the set `N` of null variables and its p-value is valid, the
hierarchical procedure with levels `α |C| / m` (`α ∈ [0, 1]`) rejects some true-null node with
probability at most `α |N| / m`, under arbitrary dependence.

Source: Meinshausen (2008), Theorem 1. -/
theorem measure_meinshausen_familywiseError_le_card (μ : Measure Ω)
    {T : Finset (Finset (Fin m))} (hT : IsLaminar T) (p : Finset (Fin m) → Ω → ℝ)
    {H0 : Finset (Finset (Fin m))} (hH0 : H0 ⊆ T) (hnull : ∀ C ∈ H0, IsValidPValue μ (p C))
    {N : Finset (Fin m)} (hN : ∀ C ∈ H0, C ⊆ N) {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    μ {ω | (hierRejections T (meinshausenLevel α) (fun C => p C ω) ∩ H0).Nonempty} ≤
      ENNReal.ofReal (α * N.card / m) :=
  measure_hier_familywiseError_le μ hT _ p hH0 hnull
    (fun C _ => meinshausenLevel_mem_Icc hα₀ hα₁ C)
    fun _ hS hdisj => sum_meinshausenLevel_le_of_subset hα₀ hdisj fun C hC => hN C (hS hC)

/-- **Meinshausen's hierarchical procedure controls the FWER at `α`.** For any tree of clusters
and any set `H0` of true-null nodes with valid p-values, the hierarchical procedure with levels
`α |C| / m` (`α ∈ [0, 1]`) rejects some true-null node with probability at most `α`, under
arbitrary dependence.

Source: Meinshausen (2008), Theorem 1. -/
theorem measure_meinshausen_familywiseError_le (μ : Measure Ω) {T : Finset (Finset (Fin m))}
    (hT : IsLaminar T) (p : Finset (Fin m) → Ω → ℝ) {H0 : Finset (Finset (Fin m))}
    (hH0 : H0 ⊆ T) (hnull : ∀ C ∈ H0, IsValidPValue μ (p C)) {α : ℝ} (hα₀ : 0 ≤ α)
    (hα₁ : α ≤ 1) :
    μ {ω | (hierRejections T (meinshausenLevel α) (fun C => p C ω) ∩ H0).Nonempty} ≤
      ENNReal.ofReal α := by
  refine (measure_meinshausen_familywiseError_le_card μ hT p hH0 hnull
    (N := Finset.univ) (fun C _ => Finset.subset_univ C) hα₀ hα₁).trans
    (ENNReal.ofReal_le_ofReal ?_)
  rw [Finset.card_univ, Fintype.card_fin]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [hα₀]
  rw [mul_div_assoc, div_self (by exact_mod_cast hm.ne'), mul_one]

end MathlibExt.Probability.Statistics.MultipleTesting
