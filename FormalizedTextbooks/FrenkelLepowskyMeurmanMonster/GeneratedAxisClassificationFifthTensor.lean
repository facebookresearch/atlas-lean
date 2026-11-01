/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthOddCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthShortCoverage
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQTrialityTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthTensor

/-! The exact 64-term original tensor of the literal fifth generated-group axis. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

/-- The actual local middle word has zero original tensor. -/
theorem generatedFifth_middle_tensor_zero :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedFifthLocalFiber)
      (sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0)))).2.2 = 0 := by
  rw [generatedFourth_local_tensor, generatedAxis_triality_octad_family_tensor_zero, map_zero]

/-- The complete original tensor is the 64 verified signed Y dictionary states. -/
theorem generatedFifth_tensor_sum :
    (griessConwayEncode generatedFifthAxis).2.2 =
      ∑ j : Fin 64, qSign (generatedFifthOddCoefficientPhaseData j) •
        trialityYTensor (generatedFifthOddRootOutputData j).1
          (generatedFifthOddRootOutputData j).2 := by
  let x := rhoLocal (localFiberIntoH generatedFifthLocalFiber)
    (sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0))
  let F (y : Fin 2048 × Fin 24) :=
    (griessConwayEncode x).2.1 (Sum.inr (Sum.inr y)) • trialityYTensor y.1 y.2
  rw [generatedFifthAxis_local_expression,
    generatedFourthQ_triality_tensor_sum _ generatedFifth_middle_tensor_zero]
  change (∑ d : Fin 2048, ∑ i : Fin 24, F (d, i)) = _
  rw [← Fintype.sum_prod_type]
  have hout (y : Fin 2048 × Fin 24)
      (hy : y ∉ Finset.univ.image generatedFifthOddRootOutputData) : F y = 0 := by
    have hn : ¬∃ j : Fin 64, generatedFifthOddRootOutputData j = y := by
      simpa only [Finset.mem_image, Finset.mem_univ, true_and] using hy
    have hz : (griessConwayEncode x).2.1 (Sum.inr (Sum.inr y)) = 0 := by
      change (griessConwayEncode (rhoLocal (localFiberIntoH generatedFifthLocalFiber)
        (sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0)))).2.1 _ = 0
      rw [generatedFourth_local_short]
      exact not_ne_iff.mp (fun h => hn ((generatedFifth_odd_middle_nonzero_iff y.1 y.2).mp h))
    simp only [F, hz, zero_smul]
  calc
    _ = ∑ y ∈ Finset.univ.image generatedFifthOddRootOutputData, F y := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro y _ hy
      exact hout y hy
    _ = ∑ j : Fin 64, F (generatedFifthOddRootOutputData j) := by
      rw [Finset.sum_image]
      intro a _ b _ h
      exact generatedFifthOddRootOutputData_injective h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      change (griessConwayEncode x).2.1 (generatedFifthOddRootOutputLabel j) • _ = _
      rw [show (griessConwayEncode x).2.1 (generatedFifthOddRootOutputLabel j) =
        qSign (generatedFifthOddCoefficientPhaseData j) from
          generatedFifth_odd_middle_coefficient j]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
