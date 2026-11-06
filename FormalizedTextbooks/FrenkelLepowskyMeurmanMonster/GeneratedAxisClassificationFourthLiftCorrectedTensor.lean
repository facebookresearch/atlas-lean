/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftFiniteKernel
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftSupport

/-! The actual Q-corrected tensor formula and soundness of support certificates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The genuine extraspecial tensor action is the original signed coordinate translation. -/
theorem generatedFourth_lift_q_tensor (q : Q) (T : SpinIndex → Fin 24 → ℝ)
    (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation (localFiberIncl q) T t i =
      qSign (spinPhase q t) * T (t + spinTranslation q) i := by
  classical
  rw [generatedFourth_local_tensor_columns]
  change (∑ j : Fin 24, (Pi.single j 1 : Fin 24 → ℝ) i *
    (qSign (spinPhase q t) * T (t + spinTranslation q) j)) = _
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

/-- The sparse corrected numerator equals the actual full tensor action, including central phase. -/
theorem generatedFourth_lift_corrected_tensor_kernel (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation generatedFourthFlagCorrectedLift
      (griessConwayEncode generatedFourthAxis).2.2 t i =
        (generatedFourthLiftSparseCorrectedFast t i : ℝ) / (64 * Real.sqrt 2) := by
  rw [generatedFourthFlagCorrectedLift, map_mul]
  change localTensorRepresentation (localFiberIncl generatedFourthFlagXiCorrection)
    (localTensorRepresentation generatedFourthFlagNormalizedLift
      (griessConwayEncode generatedFourthAxis).2.2) t i = _
  rw [generatedFourth_lift_q_tensor, generatedFourth_lift_tensor_kernel,
    generatedFourth_lift_sparse_tensor_fast]
  simp only [generatedFourthLiftSparseCorrectedFast, Int.cast_mul,
    generatedFourth_lift_int_sign_real]
  ring

/-- Every nonzero original coordinate occurs at an actual signed affine support address. -/
theorem generatedFourth_lift_support_coverage (t : SpinIndex) (i : Fin 24)
    (h : (griessConwayEncode generatedFourthAxis).2.2 t i ≠ 0) :
    ∃ k : Fin 28, ∃ s : Fin 4,
      i = generatedFourthQAffineTensorColumns k ∧ t = generatedFourthLiftSupportAddress k s := by
  classical
  rw [generatedFourth_lift_integer_tensor] at h
  have hn : generatedFourthLiftIntegerTensor t i ≠ 0 := by
    intro hz
    exact h (by simp [hz])
  unfold generatedFourthLiftIntegerTensor at hn
  by_contra hc
  apply hn
  apply Finset.sum_eq_zero
  intro k _
  by_cases hi : i = generatedFourthQAffineTensorColumns k
  · simp only [hi, ite_true]
    have hp : ¬ generatedFourthLiftPlane
        (t + generatedAxisFourthQAffineParameterBases
          (generatedFourthQAffineTensorFamilyIndex k)) := by
      intro hp
      obtain ⟨s, hs⟩ := (generatedFourth_lift_plane_labels _).mp hp
      have ht : t = generatedFourthLiftSupportAddress k s := by
        unfold generatedFourthLiftSupportAddress
        calc
          t = (t + generatedAxisFourthQAffineParameterBases
              (generatedFourthQAffineTensorFamilyIndex k)) +
                generatedAxisFourthQAffineParameterBases
                  (generatedFourthQAffineTensorFamilyIndex k) := by
                  rw [add_assoc, generatedFourth_lift_add_self, add_zero]
          _ = _ := by rw [hs]; exact add_comm _ _
      exact hc ⟨k, s, hi, ht⟩
    simp only [hp, ite_false]
  · simp only [hi, ite_false]

/-- Matching every genuine support address proves equality of the entire actual tensor. -/
theorem generatedFourth_lift_tensor_fixed_of_certificate
    (hc : ∀ k : Fin 28, ∀ s : Fin 4,
      generatedFourthLiftSparseCorrectedFast (generatedFourthLiftSupportAddress k s)
        (generatedFourthQAffineTensorColumns k) =
          64 * generatedFourthLiftIntegerTensor (generatedFourthLiftSupportAddress k s)
            (generatedFourthQAffineTensorColumns k)) :
    localTensorRepresentation generatedFourthFlagCorrectedLift
      (griessConwayEncode generatedFourthAxis).2.2 =
        (griessConwayEncode generatedFourthAxis).2.2 := by
  classical
  let T := (griessConwayEncode generatedFourthAxis).2.2
  let U := localTensorRepresentation generatedFourthFlagCorrectedLift T
  have hn := localTensorRepresentation_pairing generatedFourthFlagCorrectedLift T T
  have hn' : (∑ p : SpinIndex × Fin 24, U p.1 p.2 ^ 2) =
      ∑ p : SpinIndex × Fin 24, T p.1 p.2 ^ 2 := by
    simpa only [Fintype.sum_prod_type, conwayTensorForm, LinearMap.mk₂_apply, pow_two] using hn
  have hs : ∀ p : SpinIndex × Fin 24, T p.1 p.2 ≠ 0 → U p.1 p.2 = T p.1 p.2 := by
    intro p hp
    obtain ⟨k, s, hi, ht⟩ := generatedFourth_lift_support_coverage p.1 p.2 hp
    change localTensorRepresentation generatedFourthFlagCorrectedLift
      (griessConwayEncode generatedFourthAxis).2.2 p.1 p.2 =
        (griessConwayEncode generatedFourthAxis).2.2 p.1 p.2
    rw [generatedFourth_lift_corrected_tensor_kernel, hi, ht, hc,
      generatedFourth_lift_integer_tensor]
    push_cast
    ring
  have he := generatedFourth_real_eq_of_norm_support
    (fun p : SpinIndex × Fin 24 => T p.1 p.2) (fun p => U p.1 p.2) hn' hs
  funext t i
  exact congrFun he (t, i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
