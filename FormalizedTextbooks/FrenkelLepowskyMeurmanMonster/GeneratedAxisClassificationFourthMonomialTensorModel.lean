/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialSpinPlanSoundness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialTensorAction

/-! Verified finite matrix plans give compact original tensor-coordinate evaluators. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Typed original quadratic phase of the final explicit spin model. -/
def generatedFourthMonomialModelPhase (k : Fin 4) (t : SpinIndex) : ZMod 2 :=
  monsterMonomialQuadratic (generatedFourthMonomialSpinModel k).phase t

/-- Typed original label pullback of the final explicit spin matrix. -/
def generatedFourthMonomialModelLabel (k : Fin 4) (t : SpinIndex) : SpinIndex :=
  (generatedFourthMonomialSpinModel k).coordinate *ᵥ t

/-- Original tensor action evaluated from a verified full-phase spin matrix plan. -/
theorem generatedFourth_monomial_tensor_model_apply (k : Fin 4)
    (hc : representativeSpinPlanValid generatedFourthMonomialLetterModel
      representativeSpinIdentityModel (generatedFourthMonomialSpinPlan k))
    (T : SpinIndex → Fin 24 → ℝ) (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation (generatedFourthMonomialFiber k) T t i =
      qSign (generatedFourthMonomialModelPhase k t) *
        T (generatedFourthMonomialModelLabel k t)
          ((generatedFourthMonomialPermutation k).val.symm i) := by
  have hs : ∀ (f : SpinSpace) (u : SpinIndex),
      (generatedFourthMonomialFiber k).val.1.val f u =
        qSign (generatedFourthMonomialModelPhase k u) * f (generatedFourthMonomialModelLabel k u) :=
    generatedFourth_monomial_spin_plan_sound k hc
  rw [generatedFourth_local_tensor_columns]
  simp_rw [hs]
  rw [generatedFourth_monomial_spatial]
  change (∑ j : Fin 24,
    (Pi.single j 1 : Fin 24 → ℝ) ((generatedFourthMonomialPermutation k).val.symm i) *
      (qSign (generatedFourthMonomialModelPhase k t) *
        T (generatedFourthMonomialModelLabel k t) j)) = _
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

/-- Compact integer evaluator, including the original correction and full spin polynomial. -/
def generatedFourthMonomialTensorModelNumerator (k : Fin 4) (t : SpinIndex)
    (i : Fin 24) : ℤ :=
  let u := t + spinTranslation (generatedFourthMonomialCorrection k)
  generatedFourthLiftIntSign (spinPhase (generatedFourthMonomialCorrection k) t +
    generatedFourthMonomialModelPhase k u) *
      generatedFourthLiftIntegerTensor (generatedFourthMonomialModelLabel k u)
        ((generatedFourthMonomialPermutation k).val.symm i)

/-- Finite model validity binds the compact numerator to the entire original tensor action. -/
theorem generatedFourth_monomial_tensor_model_coordinate (k : Fin 4)
    (hc : representativeSpinPlanValid generatedFourthMonomialLetterModel
      representativeSpinIdentityModel (generatedFourthMonomialSpinPlan k))
    (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation (generatedFourthMonomialCorrectedFiber k)
      (griessConwayEncode generatedFourthAxis).2.2 t i =
        (generatedFourthMonomialTensorModelNumerator k t i : ℝ) / Real.sqrt 2 := by
  rw [generatedFourthMonomialCorrectedFiber, map_mul, LinearEquiv.mul_apply,
    generatedFourth_lift_q_tensor, generatedFourth_monomial_tensor_model_apply k hc,
    generatedFourth_lift_integer_tensor]
  simp only [generatedFourthMonomialTensorModelNumerator, Int.cast_mul,
    generatedFourth_lift_int_sign_real, qSign_add]
  ring

/-- Compact and expanded evaluators agree once the exact original spin plan is verified. -/
theorem generatedFourth_monomial_tensor_numerators_eq (k : Fin 4)
    (hc : representativeSpinPlanValid generatedFourthMonomialLetterModel
      representativeSpinIdentityModel (generatedFourthMonomialSpinPlan k))
    (t : SpinIndex) (i : Fin 24) :
    generatedFourthMonomialTensorNumerator k t i =
      generatedFourthMonomialTensorModelNumerator k t i := by
  have h := (generatedFourth_monomial_corrected_tensor_coordinate k t i).symm.trans
    (generatedFourth_monomial_tensor_model_coordinate k hc t i)
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have he := (div_left_inj' hs).mp h
  exact_mod_cast he

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
