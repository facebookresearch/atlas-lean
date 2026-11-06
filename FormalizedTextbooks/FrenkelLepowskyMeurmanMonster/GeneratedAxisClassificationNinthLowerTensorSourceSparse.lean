/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerTensorSourceFast

/-! Zero coefficients retain their exact contribution without evaluating the unused output term. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The complete eight-term middle numerator with its zero summands evaluated directly. -/
def generatedNinthMiddleSparseNumerator (n : Fin 4096) (i : Fin 24) : ℤ :=
  ∑ b : Fin 8, if generatedNinthInputBasisCoefficients i b = 0 then 0 else
    generatedNinthInputBasisCoefficients i b * generatedNinthPauliMiddleInteger b n

/-- Every summand agrees with the original middle numerator, including all zero coefficients. -/
theorem generatedNinth_middle_sparse_numerator_actual (n : Fin 4096) (i : Fin 24) :
    generatedNinthMiddleSparseNumerator n i = generatedNinthMiddleNumerator n i := by
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : generatedNinthInputBasisCoefficients i b = 0
  · simp only [h, ite_true, zero_mul]
  · simp only [h, ite_false]

/-- The complete signed tensor numerator with exact zero-summand evaluation. -/
def generatedNinthLowerTensorSourceSparseInteger (n : Fin 4096) (i : Fin 24) : ℤ :=
  let d : Fin 2048 := ⟨n.val % 2048, Nat.mod_lt _ (by decide)⟩
  let sigma : ℤ := if (generatedTwelfthGolayMaskCache d).testBit i.val then -1 else 1
  let parker := generatedTwelfthGolayPhaseCache d
  (if n.val < 2048 then 4 else -4) * sigma * generatedNinthLowerIncomingCachedCoefficient d i +
    sigma * parker * (generatedNinthMiddleSparseNumerator ⟨d.val, by omega⟩ i -
      generatedNinthMiddleSparseNumerator ⟨d.val + 2048, by omega⟩ i)

/-- Every original spin label and spatial column has exactly the original signed source. -/
theorem generatedNinth_lower_tensor_source_sparse_actual (n : Fin 4096) (i : Fin 24) :
    generatedNinthLowerTensorSourceSparseInteger n i =
      generatedNinthLowerTensorSourceInteger n i := by
  calc
    generatedNinthLowerTensorSourceSparseInteger n i =
        generatedNinthLowerTensorSourceFastInteger n i := by
      simp only [generatedNinthLowerTensorSourceSparseInteger,
        generatedNinthLowerTensorSourceFastInteger, generatedNinth_middle_sparse_numerator_actual]
    _ = generatedNinthLowerTensorSourceInteger n i :=
      generatedNinth_lower_tensor_source_fast_actual n i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
