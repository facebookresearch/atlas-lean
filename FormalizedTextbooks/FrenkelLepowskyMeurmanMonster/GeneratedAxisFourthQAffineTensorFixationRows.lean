/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineTensorReindex
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineTensorFixationColumns
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every original packed coefficient is nonzero. -/
theorem generatedFourthQAffineTensor_scale_ne_zero (k : Fin 28) :
    qSign (generatedFourthQAffineTensorScalePhases k) / Real.sqrt 2 ≠ 0 := by
  have hc : qSign (generatedFourthQAffineTensorScalePhases k) ≠ 0 := by
    intro h
    have hs := qSign_sq (generatedFourthQAffineTensorScalePhases k)
    rw [h, zero_mul] at hs
    exact zero_ne_one hs
  exact div_ne_zero hc (Real.sqrt_ne_zero'.mpr (by norm_num))

/-- Reading an ordinary spatial column gives exactly its nonzero scalar affine state. -/
theorem generatedFourthQAffineTensor_packed_single (j : Fin 16) :
    (fun t => generatedFourthQAffineTensorPacked t (generatedFourthQAffineTensorSingleColumns j)) =
      (qSign (generatedFourthQAffineTensorScalePhases
        (generatedFourthQAffineTensorSingleIndices j)) / Real.sqrt 2) •
      generatedAxisFourthQAffineSpinState generatedAxisFourthQAffineParameterPlane
        (generatedAxisFourthQAffineParameterBases (generatedFourthQAffineTensorFamilyIndex
          (generatedFourthQAffineTensorSingleIndices j)))
        (generatedAxisFourthQAffineParameterCharacters (generatedFourthQAffineTensorFamilyIndex
          (generatedFourthQAffineTensorSingleIndices j))) := by
  funext t
  simp only [generatedFourthQAffineTensorPacked, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, generatedFourthQAffineTensorState]
  have he (k : Fin 28) (c : ℝ) (v : ℝ) :
      c * (if generatedFourthQAffineTensorSingleColumns j = generatedFourthQAffineTensorColumns k
        then v else 0) =
      if generatedFourthQAffineTensorSingleColumns j = generatedFourthQAffineTensorColumns k
        then c * v else 0 := by split_ifs <;> simp
  simp only [he]
  exact generatedFourthQAffineTensor_single_sum _ j

/-- Reading spatial column eight gives the six nonzero scaled, disjoint affine states. -/
theorem generatedFourthQAffineTensor_packed_six :
    (fun t => generatedFourthQAffineTensorPacked t 8) =
      ∑ i : Fin 6,
        (qSign (generatedFourthQAffineTensorScalePhases
          (generatedFourthQAffineTensorSixIndices i)) /
          Real.sqrt 2) •
        generatedAxisFourthQAffineSpinState generatedAxisFourthQAffineParameterPlane
          (generatedAxisFourthQAffineParameterBases (generatedFourthQAffineTensorFamilyIndex
            (generatedFourthQAffineTensorSixIndices i)))
          (generatedAxisFourthQAffineParameterCharacters (generatedFourthQAffineTensorFamilyIndex
            (generatedFourthQAffineTensorSixIndices i))) := by
  funext t
  simp only [generatedFourthQAffineTensorPacked, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, generatedFourthQAffineTensorState]
  have he (k : Fin 28) (c v : ℝ) :
      c * (if (8 : Fin 24) = generatedFourthQAffineTensorColumns k then v else 0) =
      if (8 : Fin 24) = generatedFourthQAffineTensorColumns k then c * v else 0 := by
    split_ifs <;> simp
  simp only [he]
  exact generatedFourthQAffineTensor_six_sum _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
