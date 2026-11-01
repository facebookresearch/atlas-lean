/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiTensorCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftSupport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalForm

/-! Full original support fixation and norm preservation recover every genuine Xi tensor
coordinate. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original corrected Xi fixes the entire actual tensor, including every zero coordinate. -/
theorem generatedSixth_xi_tensor_fixed :
    localTensorRepresentation (generatedSixthCorrectedGenerator 4)
      (griessConwayEncode generatedSixthAxis).2.2 =
        (griessConwayEncode generatedSixthAxis).2.2 := by
  let T := (griessConwayEncode generatedSixthAxis).2.2
  let U := localTensorRepresentation (generatedSixthCorrectedGenerator 4) T
  have hn := localTensorRepresentation_pairing (generatedSixthCorrectedGenerator 4) T T
  have hn' : (∑ p : SpinIndex × Fin 24, U p.1 p.2 ^ 2) =
      ∑ p : SpinIndex × Fin 24, T p.1 p.2 ^ 2 := by
    simpa only [Fintype.sum_prod_type, conwayTensorForm, LinearMap.mk₂_apply, pow_two] using hn
  have hs (p : SpinIndex × Fin 24) (hne : T p.1 p.2 ≠ 0) : U p.1 p.2 = T p.1 p.2 := by
    rcases p with ⟨t, i⟩
    obtain ⟨n, rfl⟩ := golayLabelCoefficients_bijective.surjective t
    have hz : generatedSixthTensorFastExecutable n i ≠ 0 := by
      intro hz
      apply hne
      change (griessConwayEncode generatedSixthAxis).2.2 (golayLabelCoefficients n) i = 0
      rw [generatedSixth_tensor_executable, ← generatedSixth_tensor_fast_executable,
        hz, Int.cast_zero, zero_div]
    change localTensorRepresentation (generatedSixthCorrectedGenerator 4) T
      (golayLabelCoefficients n) i = T (golayLabelCoefficients n) i
    calc
      _ = (generatedSixthXiCachedTensor n i : ℝ) / (512 * Real.sqrt 2) := by
        rw [generatedSixth_xi_cached_tensor, generatedSixth_xi_sparse_fast_numerator]
        exact generatedSixth_xi_sparse_tensor n i
      _ = (generatedSixthTensorExecutable n i : ℝ) / (32 * Real.sqrt 2) := by
        rw [generatedSixth_xi_tensor_integer_supported_fixed n i hz,
          generatedSixth_tensor_fast_executable]
        push_cast
        have hroot : Real.sqrt 2 ≠ 0 := by positivity
        field_simp [hroot]
        ring
      _ = _ := (generatedSixth_tensor_executable n i).symm
  have he := generatedFourth_real_eq_of_norm_support
    (fun p : SpinIndex × Fin 24 => T p.1 p.2) (fun p => U p.1 p.2) hn' hs
  funext t i
  exact congrFun he (t, i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
