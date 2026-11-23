/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Phylogenetics.Splits

/-!
# Tests for splits, Robinson–Foulds, ultrametrics, UPGMA and triplets

On four taxa `Fin 4`: compatible and incompatible splits, the four-gamete test and a matrix with
no perfect phylogeny; the two binary hierarchies `((1,2),3)` and `((1,3),2)` seen from taxon
`0`, the trees they give, and their Robinson–Foulds distance `2 = 2 (4 - 3)` (the maximum is
attained), also computed from another taxon; a triplet that one tree displays and the other does
not, compatible and incompatible rooted-triplet systems exercising BUILD, and a quartet. On three
taxa: the discrete metric as a non-vacuity witness for
`IsUltrametric`, its tree-metric and dated-tree witnesses, and one UPGMA step. Boundary cases:
average linkage of an empty cluster (a junk `0`) and bootstrap support with no sites.
-/

@[expose] public section

namespace CSLibExtTest.Bioinformatics.Phylogenetics.Splits

open MathlibExt.Biology.Phylogenetics.UnrootedTreeCount
open Cslib.Bioinformatics.Phylogenetics.Splits

/-! ### Compatibility and four gametes -/

example : Compatible ({0, 1} : Finset (Fin 4)) {0, 1, 2} := by unfold Compatible; decide
example : ¬ Compatible ({0, 1} : Finset (Fin 4)) {0, 2} := by unfold Compatible; decide
-- the side of a split does not matter
example : Compatible ({2, 3} : Finset (Fin 4)) {0, 1, 2} := by unfold Compatible; decide

/-- Character `χ₁`: taxa `0, 1` in state `true`. -/
def χ₁ : Fin 4 → Bool := fun x => decide (x.val < 2)

/-- Character `χ₂`: taxa `0, 2` in state `true`. -/
def χ₂ : Fin 4 → Bool := fun x => decide (x.val % 2 = 0)

example : FourGametes χ₁ χ₂ := by unfold FourGametes χ₁ χ₂; decide
example : ¬ Compatible (charSplit χ₁) (charSplit χ₂) :=
  fun h => (compatible_iff_not_fourGametes χ₁ χ₂).mp h (by unfold FourGametes χ₁ χ₂; decide)

/-- The matrix with columns `χ₁` and `χ₂`. -/
def M₀ : Fin 4 → Fin 2 → Bool := fun x j => if j = 0 then χ₁ x else χ₂ x

/-- The four-gamete test rules out a perfect phylogeny for `M₀`. -/
example : ¬ ∃ T : UnrootedBinaryTree (Fin 4), IsPerfectPhylogeny T M₀ := by
  rw [exists_perfectPhylogeny_iff (by decide)]
  intro h
  exact h 0 1 (by unfold FourGametes M₀ χ₁ χ₂; decide)

/-! ### Two trees on four taxa and their Robinson–Foulds distance -/

/-- The clusters of `((1,2),3)` seen from taxon `0`. -/
def H₁ : Finset (Finset (Fin 4)) := {{1, 2, 3}, {1, 2}, {1}, {2}, {3}}

/-- The clusters of `((1,3),2)` seen from taxon `0`. -/
def H₂ : Finset (Finset (Fin 4)) := {{1, 2, 3}, {1, 3}, {1}, {2}, {3}}

theorem isBinaryHierarchy_H₁ : IsBinaryHierarchy (Finset.univ.erase (0 : Fin 4)) H₁ := by
  unfold IsBinaryHierarchy H₁
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem isBinaryHierarchy_H₂ : IsBinaryHierarchy (Finset.univ.erase (0 : Fin 4)) H₂ := by
  unfold IsBinaryHierarchy H₂
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The tree with the nontrivial split `{1, 2} | {0, 3}`. -/
noncomputable def T₁ : UnrootedBinaryTree (Fin 4) :=
  (exists_clusterSet_eq 0 H₁ isBinaryHierarchy_H₁).choose

/-- The tree with the nontrivial split `{1, 3} | {0, 2}`. -/
noncomputable def T₂ : UnrootedBinaryTree (Fin 4) :=
  (exists_clusterSet_eq 0 H₂ isBinaryHierarchy_H₂).choose

theorem clusterSet_T₁ : clusterSet T₁ 0 = H₁ :=
  (exists_clusterSet_eq 0 H₁ isBinaryHierarchy_H₁).choose_spec

theorem clusterSet_T₂ : clusterSet T₂ 0 = H₂ :=
  (exists_clusterSet_eq 0 H₂ isBinaryHierarchy_H₂).choose_spec

/-- The two trees differ in one nontrivial split each: the distance is `2 = 2 (4 - 3)`, the
maximum allowed by `rfDist_le`. -/
theorem rfDist_T₁_T₂ : rfDist 0 T₁ T₂ = 2 := by
  rw [rfDist, clusterSet_T₁, clusterSet_T₂]; decide

example : rfDist 0 T₁ T₂ = 2 * (Fintype.card (Fin 4) - 3) := by
  rw [rfDist_T₁_T₂]; rfl

/-- So the two trees are not isomorphic. -/
example : ¬ T₁.Iso T₂ := by
  rw [← rfDist_eq_zero_iff 0, rfDist_T₁_T₂]; decide

/-- The split `{1, 2} | {0, 3}` is a split of `T₁`. -/
example : ({1, 2} : Finset (Fin 4)) ∈ splitSet T₁ 0 := by
  rw [splitSet, clusterSet_T₁]; decide

/-- `T₁` displays the triplet `12|3` seen from `0`, `T₂` does not. -/
example : DisplaysTriplet H₁ ⟨1, 2, 3⟩ ∧ ¬ DisplaysTriplet H₂ ⟨1, 2, 3⟩ := by
  unfold DisplaysTriplet H₁ H₂; decide

/-! ### BUILD -/

/-- The compatible triplets `01|2` and `01|3` on four taxa. -/
noncomputable def compatibleTriplets : Finset (Triplet (Fin 4)) :=
  by classical exact { ⟨0, 1, 2⟩, ⟨0, 1, 3⟩ }

/-- BUILD accepts the compatible system: every induced Aho graph has a cut. -/
theorem build_accepts_compatibleTriplets :
    ∃ H, IsBinaryHierarchy (Finset.univ : Finset (Fin 4)) H ∧
      ∀ t ∈ compatibleTriplets, DisplaysTriplet H t := by
  classical
  apply (build_spec (by decide) compatibleTriplets (by
    intro t ht
    simp only [compatibleTriplets, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl <;> decide)).mpr
  intro S' hS' hcard
  fin_cases S' <;> simp_all [HasAhoCut, compatibleTriplets] <;> decide

/-- The three conflicting triplets on the induced taxa `{0, 1, 2}`. -/
noncomputable def incompatibleTriplets : Finset (Triplet (Fin 4)) :=
  by classical exact { ⟨0, 1, 2⟩, ⟨0, 2, 1⟩, ⟨1, 2, 0⟩ }

/-- The Aho graph induced on `{0, 1, 2}` is connected, so it has no cut. -/
theorem incompatibleInducedSubset_has_no_Aho_cut :
    ¬ HasAhoCut incompatibleTriplets ({0, 1, 2} : Finset (Fin 4)) := by
  classical
  simp only [HasAhoCut, incompatibleTriplets]
  rintro ⟨K, hK, hKne, hKcne, hcut⟩
  fin_cases K <;> simp_all [Finset.Nonempty]
  simpa using hK (show (3 : Fin 4) ∈ ({3} : Finset (Fin 4)) by decide)

/-- BUILD rejects the incompatible system because its nontrivial induced subsystem has no cut. -/
theorem build_rejects_incompatibleTriplets :
    ¬ ∃ H, IsBinaryHierarchy (Finset.univ : Finset (Fin 4)) H ∧
      ∀ t ∈ incompatibleTriplets, DisplaysTriplet H t := by
  classical
  rw [build_spec (by decide) incompatibleTriplets]
  · intro h
    exact incompatibleInducedSubset_has_no_Aho_cut (h {0, 1, 2} (by decide) (by decide))
  · intro t ht
    simp only [incompatibleTriplets, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl <;> decide

/-- The quartet `12|30` is displayed by `T₁`. -/
example : DisplaysQuartet T₁ 1 2 3 0 := by
  refine ⟨{1, 2}, ?_, by decide⟩
  rw [← splitSet_eq_edgeSplits T₁ 0, splitSet, clusterSet_T₁]; decide

/-- The split `{0, 3} | {1, 2}` seen from taxon `1` is the same split. -/
example : ({0, 3} : Finset (Fin 4)) ∈ splitSet T₁ 1 := by
  rw [splitSet_eq_splitSet T₁ 1 0, splitSet, clusterSet_T₁]; decide

/-- The distance computed from taxon `3` is the same. -/
example : rfDist 3 T₁ T₂ = 2 := by
  rw [rfDist_eq_rfDist 3 0, rfDist_T₁_T₂]

/-! ### Ultrametrics and UPGMA -/

/-- The discrete metric on three taxa. -/
def d₀ : Fin 3 → Fin 3 → ℝ := fun x y => if x = y then 0 else 1

/-- Non-vacuity witness: the discrete metric is an ultrametric. -/
theorem isUltrametric_d₀ : IsUltrametric d₀ where
  symm x y := by unfold d₀; by_cases h : x = y <;> simp [h, eq_comm]
  self x := by simp [d₀]
  pos x y h := by simp [d₀, h]
  three_point x y z := by
    unfold d₀
    split_ifs <;> simp_all

/-- The discrete metric is a tree metric (a star), via the four-point condition. -/
example : MathlibExt.Biology.Phylogenetics.Buneman.IsTreeMetric d₀ :=
  isUltrametric_d₀.isTreeMetric

/-- The dated star tree: all taxa join at the root at date `1`. -/
example : IsDatedTreeMetric d₀ := by
  refine ⟨{Finset.univ, {0}, {1}, {2}}, fun C => if C.card = 1 then 0 else 1, ?_, ?_, ?_, ?_⟩
  · unfold IsHierarchy
    refine ⟨?_, ?_, ?_, ?_⟩ <;> decide
  · intro x; simp
  · intro C hC D hD hCD
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC hD
    rcases hC with rfl | rfl | rfl | rfl <;> rcases hD with rfl | rfl | rfl | rfl <;>
      first | (exfalso; revert hCD; decide) | simp
  · intro x y
    by_cases hxy : x = y
    · subst hxy
      refine ⟨{x}, by fin_cases x <;> decide, Finset.mem_singleton_self x,
        Finset.mem_singleton_self x, by simp [d₀], ?_⟩
      intro D _ hx _
      exact Finset.singleton_subset_iff.mpr hx
    · refine ⟨Finset.univ, by decide, Finset.mem_univ _, Finset.mem_univ _, by simp [d₀, hxy], ?_⟩
      intro D hD hx hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hD
      rcases hD with rfl | rfl | rfl | rfl
      · exact le_rfl
      all_goals
        simp only [Finset.mem_singleton] at hx hy
        exact absurd (hx.trans hy.symm) hxy

/-- One UPGMA step on `d₀` merges `{0}` and `{1}` at height `1 = d₀ 0 1`. -/
example : UpgmaReaches d₀ (insert ({0} ∪ {1}) (((Finset.univ.image ({·})).erase {0}).erase {1}))
    fun x y => if (x ∈ ({0} : Finset (Fin 3)) ∧ y ∈ ({1} : Finset (Fin 3))) ∨
      (x ∈ ({1} : Finset (Fin 3)) ∧ y ∈ ({0} : Finset (Fin 3))) then avgDist d₀ {0} {1}
      else 0 := by
  refine UpgmaReaches.step UpgmaReaches.init (by decide) (by decide) (by decide) ?_
  intro E hE F hF hEF
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hE
  obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hF
  have hxy : x ≠ y := fun h => hEF (by rw [h])
  simp [avgDist, d₀, hxy]

/-- The average linkage of `{0}` and `{1}` is their distance. -/
example : avgDist d₀ {0} {1} = 1 := by simp [avgDist, d₀]

/-- Boundary: the average linkage of an empty cluster is a junk `0` (division by zero); UPGMA
only uses nonempty blocks. -/
example (D : Finset (Fin 3)) : avgDist d₀ ∅ D = 0 := by simp [avgDist]

/-- Boundary: with no sites there is one (empty) resampling, so the support is `0` or `1`. -/
example (est : (Fin 0 → Fin 4 → Bool) → UnrootedBinaryTree (Fin 4)) (M : Fin 0 → Fin 4 → Bool)
    (A : Finset (Fin 4)) : bootstrapSupport est 0 M A ∈ Set.Icc 0 1 :=
  bootstrapSupport_mem_Icc est 0 M A

/-- A majority split of a constant family is a cluster of its tree. -/
example (A : Finset (Fin 4)) (hA : A ∈ majoritySplits (fun _ : Fin 3 => T₁) 0) :
    A ∈ H₁ := by
  rw [← clusterSet_T₁]
  simp only [majoritySplits, Finset.mem_filter, Finset.mem_univ, true_and] at hA
  by_contra h
  simp [h] at hA

end CSLibExtTest.Bioinformatics.Phylogenetics.Splits
