/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.DirectSumOperators

@[expose] public section

namespace MathlibExtTest.Analysis.InnerProductSpace.DirectSumOperatorsTests

open ContinuousLinearMap Set
open MathlibExt.Analysis.InnerProductSpace.DirectSumOperators

noncomputable section

/-- The scalar operator `algebraMap ℝ _ c` is a unit whenever `c ≠ 0`. -/
private lemma isUnit_algebraMap_of_ne_zero (c : ℝ) (hc : c ≠ 0) :
    IsUnit (algebraMap ℝ (ℝ →L[ℝ] ℝ) c) := by
  refine ⟨⟨algebraMap ℝ _ c, algebraMap ℝ _ c⁻¹, ?_, ?_⟩, rfl⟩
  · rw [← map_mul, mul_inv_cancel₀ hc, map_one]
  · rw [← map_mul, inv_mul_cancel₀ hc, map_one]

/-- The diagonal operator `diag(2, 3)` on `ℝ × ℝ`. -/
private abbrev diag23 : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (algebraMap ℝ (ℝ →L[ℝ] ℝ) 2).prodMap (algebraMap ℝ (ℝ →L[ℝ] ℝ) 3)

/-- `diag(2, 3)` acts componentwise. -/
example : diag23 (1, 2) = (2, 6) := by
  simp [diag23, ContinuousLinearMap.coe_prodMap', Prod.map,
    Algebra.algebraMap_eq_smul_one]
  norm_num

/-- The operator norm of `diag(2, 3)` is `3`. -/
example : ‖diag23‖ = 3 := by
  rw [diag23, norm_prodMap]
  simp [Algebra.algebraMap_eq_smul_one, norm_smul, norm_one]
  norm_num

/-- The spectrum of `diag(2, 3)` contains `2` and `3` but not `4`. -/
example : (2 : ℝ) ∈ spectrum ℝ diag23 ∧ (3 : ℝ) ∈ spectrum ℝ diag23
    ∧ (4 : ℝ) ∉ spectrum ℝ diag23 := by
  rw [diag23, spectrum_prodMap]
  simp [spectrum.scalar_eq]

/-- `4` is in the resolvent set of `diag(2, 3)`. -/
example : (4 : ℝ) ∈ resolventSet ℝ diag23 := by
  rw [diag23, resolventSet_prodMap]
  refine ⟨?_, ?_⟩ <;> rw [spectrum.mem_resolventSet_iff]
  · have h : algebraMap ℝ (ℝ →L[ℝ] ℝ) 4 - algebraMap ℝ (ℝ →L[ℝ] ℝ) 2
        = algebraMap ℝ (ℝ →L[ℝ] ℝ) 2 := by
      rw [← map_sub]
      norm_num
    rw [h]
    exact isUnit_algebraMap_of_ne_zero 2 (by norm_num)
  · have h : algebraMap ℝ (ℝ →L[ℝ] ℝ) 4 - algebraMap ℝ (ℝ →L[ℝ] ℝ) 3
        = algebraMap ℝ (ℝ →L[ℝ] ℝ) 1 := by
      rw [← map_sub]
      norm_num
    rw [h, map_one]
    exact isUnit_one

/-- `diag(2, 3)` is a unit: both diagonal entries are nonzero. -/
example : IsUnit diag23 := by
  rw [diag23, isUnit_prodMap_iff]
  exact ⟨isUnit_algebraMap_of_ne_zero 2 (by norm_num),
    isUnit_algebraMap_of_ne_zero 3 (by norm_num)⟩

/-- A direct sum with a zero summand is not a unit. -/
example : ¬ IsUnit ((0 : ℝ →L[ℝ] ℝ).prodMap
    (algebraMap ℝ (ℝ →L[ℝ] ℝ) 3)) := by
  intro h
  exact not_isUnit_zero ((isUnit_prodMap_iff _ _).mp h).1

/-- The kernel of `id ⊕ id` on `ℝ × ℝ` is trivial, via the kernel product law. -/
example : ((1 : ℝ →L[ℝ] ℝ).prodMap (1 : ℝ →L[ℝ] ℝ)).ker = ⊥ := by
  have h1 : (1 : ℝ →L[ℝ] ℝ).ker = ⊥ := by
    show LinearMap.ker (↑(1 : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ) = ⊥
    rw [LinearMap.ker_eq_bot]
    intro x y h
    simpa using h
  rw [ker_prodMap, h1, Submodule.prod_bot]

/-- The range of `id ⊕ id` on `ℝ × ℝ` is everything. -/
example : ((1 : ℝ →L[ℝ] ℝ).prodMap (1 : ℝ →L[ℝ] ℝ)).range = ⊤ := by
  have h1 : (1 : ℝ →L[ℝ] ℝ).range = ⊤ := by
    show LinearMap.range (↑(1 : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ) = ⊤
    rw [LinearMap.range_eq_top]
    intro y
    exact ⟨y, by simp⟩
  rw [MathlibExt.Analysis.InnerProductSpace.DirectSumOperators.range_prodMap, h1,
    Submodule.prod_top]

/-- `diag(2, 3)` is compact, from compactness of its two summands. -/
example : IsCompactOperator diag23 := by
  rw [diag23, isCompactOperator_prodMap_iff]
  exact ⟨isCompactOperator_of_locallyCompactSpace_dom _,
    isCompactOperator_of_locallyCompactSpace_dom _⟩

/-- Compactness of a direct sum implies compactness of each summand. -/
example (T : ℝ →L[ℝ] ℝ) (S : ℝ →L[ℝ] ℝ) (h : IsCompactOperator (T.prodMap S)) :
    IsCompactOperator T ∧ IsCompactOperator S :=
  (isCompactOperator_prodMap_iff T S).mp h

/-- The direct sum of two identity operators is Fredholm, with index `0`. -/
example : ((ContinuousLinearMap.id ℝ ℝ).prodMap
    (ContinuousLinearMap.id ℝ ℝ)).IsFredholm := by
  rw [isFredholm_prodMap_iff]
  exact ⟨IsFredholm.id, IsFredholm.id⟩

/-- The Fredholm index adds over direct sums: here `0 = 0 + 0`. -/
example : ((ContinuousLinearMap.id ℝ ℝ).prodMap
    (ContinuousLinearMap.id ℝ ℝ)).index = 0 := by
  rw [index_prodMap _ _ IsFredholm.id IsFredholm.id]
  simp

/-- The algebra laws for direct sums, on `ℝ × ℝ`. -/
example : ((2 : ℝ) • (1 : ℝ →L[ℝ] ℝ)).prodMap ((2 : ℝ) • (1 : ℝ →L[ℝ] ℝ))
    = (2 : ℝ) • ((1 : ℝ →L[ℝ] ℝ).prodMap (1 : ℝ →L[ℝ] ℝ)) :=
  prodMap_smul 2 1 1

example : ((ContinuousLinearMap.id ℝ ℝ).prodMap (ContinuousLinearMap.id ℝ ℝ)) ∘L
    ((ContinuousLinearMap.id ℝ ℝ).prodMap (ContinuousLinearMap.id ℝ ℝ))
    = (ContinuousLinearMap.id ℝ ℝ).prodMap (ContinuousLinearMap.id ℝ ℝ) := by
  rw [prodMap_comp]
  simp

section

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Inverse extraction from a direct sum works without completeness assumptions. -/
example (T : E →L[𝕜] E) (S : F →L[𝕜] F) (h : IsUnit (T.prodMap S)) :
    IsUnit T ∧ IsUnit S :=
  (isUnit_prodMap_iff T S).mp h

/-- Units assemble into a direct sum without completeness assumptions. -/
example (T : E →L[𝕜] E) (S : F →L[𝕜] F) (hT : IsUnit T) (hS : IsUnit S) :
    IsUnit (T.prodMap S) :=
  (isUnit_prodMap_iff T S).mpr ⟨hT, hS⟩

/-- Spectrum membership is componentwise for arbitrary normed spaces. -/
example (T : E →L[𝕜] E) (S : F →L[𝕜] F) (z : 𝕜) :
    z ∈ spectrum 𝕜 (T.prodMap S) ↔ z ∈ spectrum 𝕜 T ∨ z ∈ spectrum 𝕜 S := by
  rw [spectrum_prodMap]
  rfl

/-- Resolvent membership is componentwise for arbitrary normed spaces. -/
example (T : E →L[𝕜] E) (S : F →L[𝕜] F) (z : 𝕜) :
    z ∈ resolventSet 𝕜 (T.prodMap S) ↔
      z ∈ resolventSet 𝕜 T ∧ z ∈ resolventSet 𝕜 S := by
  rw [resolventSet_prodMap]
  rfl

end

end

#print axioms norm_prodMap
#print axioms isUnit_prodMap_iff
#print axioms spectrum_prodMap
#print axioms resolventSet_prodMap
#print axioms isCompactOperator_prodMap_iff
#print axioms isFredholm_prodMap_iff
#print axioms index_prodMap

end MathlibExtTest.Analysis.InnerProductSpace.DirectSumOperatorsTests
