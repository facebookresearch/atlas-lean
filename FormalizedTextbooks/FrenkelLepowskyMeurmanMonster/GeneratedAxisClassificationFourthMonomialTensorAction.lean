/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialSpinAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMonomialSpatial
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftCorrectedTensor

/-! Exact original tensor coordinates of the four genuine Q-corrected monomial flag words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The ordinary spin-by-coordinate action of each original monomial word. -/
theorem generatedFourth_monomial_tensor_apply (k : Fin 4)
    (T : SpinIndex → Fin 24 → ℝ) (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation (generatedFourthMonomialFiber k) T t i =
      qSign (generatedFourthMonomialWordPull (generatedFourthMonomialWord k) t).1 *
        T (generatedFourthMonomialWordPull (generatedFourthMonomialWord k) t).2
          ((generatedFourthMonomialPermutation k).val.symm i) := by
  rw [generatedFourth_local_tensor_columns]
  simp_rw [generatedFourth_monomial_spin_apply]
  rw [generatedFourth_monomial_spatial]
  change (∑ j : Fin 24,
    (Pi.single j 1 : Fin 24 → ℝ) ((generatedFourthMonomialPermutation k).val.symm i) *
      (qSign (generatedFourthMonomialWordPull (generatedFourthMonomialWord k) t).1 *
        T (generatedFourthMonomialWordPull (generatedFourthMonomialWord k) t).2 j)) = _
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

/-- Exact integer numerator of each original corrected monomial tensor coordinate. -/
def generatedFourthMonomialTensorNumerator (k : Fin 4) (t : SpinIndex) (i : Fin 24) : ℤ :=
  let u := t + spinTranslation (generatedFourthMonomialCorrection k)
  let r := generatedFourthMonomialWordPull (generatedFourthMonomialWord k) u
  generatedFourthLiftIntSign (spinPhase (generatedFourthMonomialCorrection k) t + r.1) *
    generatedFourthLiftIntegerTensor r.2 ((generatedFourthMonomialPermutation k).val.symm i)

/-- The original signed integer numerator is bound to the genuine full tensor action. -/
theorem generatedFourth_monomial_corrected_tensor_coordinate (k : Fin 4)
    (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation (generatedFourthMonomialCorrectedFiber k)
      (griessConwayEncode generatedFourthAxis).2.2 t i =
        (generatedFourthMonomialTensorNumerator k t i : ℝ) / Real.sqrt 2 := by
  rw [generatedFourthMonomialCorrectedFiber, map_mul]
  rw [LinearEquiv.mul_apply]
  rw [generatedFourth_lift_q_tensor, generatedFourth_monomial_tensor_apply,
    generatedFourth_lift_integer_tensor]
  simp only [generatedFourthMonomialTensorNumerator, Int.cast_mul,
    generatedFourth_lift_int_sign_real, qSign_add]
  ring

/-- Exact support matching plus genuine orthogonality certifies the entire original tensor. -/
theorem generatedFourth_monomial_tensor_fixed_of_certificate (k : Fin 4)
    (hc : ∀ j : Fin 28, ∀ s : Fin 4,
      generatedFourthMonomialTensorNumerator k (generatedFourthLiftSupportAddress j s)
        (generatedFourthQAffineTensorColumns j) =
          generatedFourthLiftIntegerTensor (generatedFourthLiftSupportAddress j s)
            (generatedFourthQAffineTensorColumns j)) :
    localTensorRepresentation (generatedFourthMonomialCorrectedFiber k)
      (griessConwayEncode generatedFourthAxis).2.2 =
        (griessConwayEncode generatedFourthAxis).2.2 := by
  classical
  let T := (griessConwayEncode generatedFourthAxis).2.2
  let U := localTensorRepresentation (generatedFourthMonomialCorrectedFiber k) T
  have hn := localTensorRepresentation_pairing (generatedFourthMonomialCorrectedFiber k) T T
  have hn' : (∑ p : SpinIndex × Fin 24, U p.1 p.2 ^ 2) =
      ∑ p : SpinIndex × Fin 24, T p.1 p.2 ^ 2 := by
    simpa only [Fintype.sum_prod_type, conwayTensorForm, LinearMap.mk₂_apply, pow_two] using hn
  have hs : ∀ p : SpinIndex × Fin 24, T p.1 p.2 ≠ 0 → U p.1 p.2 = T p.1 p.2 := by
    intro p hp
    obtain ⟨j, s, hi, ht⟩ := generatedFourth_lift_support_coverage p.1 p.2 hp
    change localTensorRepresentation (generatedFourthMonomialCorrectedFiber k)
      (griessConwayEncode generatedFourthAxis).2.2 p.1 p.2 =
        (griessConwayEncode generatedFourthAxis).2.2 p.1 p.2
    rw [generatedFourth_monomial_corrected_tensor_coordinate, hi, ht, hc,
      generatedFourth_lift_integer_tensor]
  have he := generatedFourth_real_eq_of_norm_support
    (fun p : SpinIndex × Fin 24 => T p.1 p.2) (fun p => U p.1 p.2) hn' hs
  funext t i
  exact congrFun he (t, i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
