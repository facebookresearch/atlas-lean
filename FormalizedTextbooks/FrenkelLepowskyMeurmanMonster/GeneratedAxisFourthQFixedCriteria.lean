/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalAxisStabilizerPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOddCocode

/-! Full actual Q fixation is determined by supported short phases and physical spin columns. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The genuine Q short action multiplies each original coordinate by its actual phase. -/
theorem generatedFourthQ_short_coordinate (q : Q) (X : GriessShortIndex → ℝ)
    (r : GriessShortIndex) :
    localShortOperator (localFiberIncl q) X r =
      qSign (localShortPhase (localFiberIncl q) r) * X r := by
  have h := localShortOperator_image (localFiberIncl q) X r
  change localShortOperator (localFiberIncl q) X (griessShortPermutation 1 r) = _ at h
  rw [map_one, Equiv.Perm.one_apply] at h
  exact h

/-- Fixing the original short block is exactly vanishing of every supported binary phase. -/
theorem generatedFourthQ_short_fixed_iff (q : Q) (X : GriessShortIndex → ℝ) :
    localShortOperator (localFiberIncl q) X = X ↔
      ∀ r, X r ≠ 0 → localAxisQPhase r q = 1 := by
  constructor
  · intro h r hr
    have he := congrFun h r
    rw [generatedFourthQ_short_coordinate] at he
    have hsign : qSign (localShortPhase (localFiberIncl q) r) = 1 :=
      mul_right_cancel₀ hr (he.trans (one_mul (X r)).symm)
    have hz := (qSign_eq_one_iff _).mp hsign
    rw [localAxisQPhase_eq_short_phase] at hz
    exact Multiplicative.toAdd.injective hz
  · intro h
    ext r
    rw [generatedFourthQ_short_coordinate]
    by_cases hr : X r = 0
    · rw [hr, mul_zero]
    · have hp : localShortPhase (localFiberIncl q) r = 0 := by
        rw [localAxisQPhase_eq_short_phase, h r hr]
        rfl
      rw [hp, qSign_zero, one_mul]

/-- The actual physical Q tensor action fixes exactly its individual original spin columns. -/
theorem generatedFourthQ_tensor_fixed_iff (q : Q) (T : SpinIndex → Fin 24 → ℝ) :
    localTensorRepresentation (localFiberIncl q) T = T ↔
      ∀ j, spinRepresentation q (fun t => T t j) = fun t => T t j := by
  constructor
  · intro h j
    ext t
    have he := congrFun (congrFun h t) j
    rw [localTensorRepresentation_q] at he
    exact he
  · intro h
    ext t j
    rw [localTensorRepresentation_q, h j]

/-- No matrix or tensor sign is dropped in this full-axis extraspecial fixation criterion. -/
theorem generatedFourthQ_full_fixed_iff (q : Q) (x : GriessSpace) :
    rhoLocal (inclQ q) x = x ↔
      (∀ r, (griessConwayEncode x).2.1 r ≠ 0 → localAxisQPhase r q = 1) ∧
      ∀ j, spinRepresentation q (fun t => (griessConwayEncode x).2.2 t j) =
        fun t => (griessConwayEncode x).2.2 t j := by
  constructor
  · intro h
    have hs := congrArg (fun y : GriessSpace => (griessConwayEncode y).2.1) h
    have ht := congrArg (fun y : GriessSpace => (griessConwayEncode y).2.2) h
    change (griessConwayEncode (localGriessRepresentation (localFiberIncl q) x)).2.1 = _ at hs
    change (griessConwayEncode (localGriessRepresentation (localFiberIncl q) x)).2.2 = _ at ht
    rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply] at hs ht
    exact ⟨(generatedFourthQ_short_fixed_iff q _).mp hs,
      (generatedFourthQ_tensor_fixed_iff q _).mp ht⟩
  · rintro ⟨hs, ht⟩
    apply (Function.LeftInverse.injective griessConwayDecode_encode)
    change griessConwayEncode (localGriessRepresentation (localFiberIncl q) x) = _
    rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
    apply Prod.ext
    · change conwayMatrixAction 1 _ = _
      rw [map_one]
      rfl
    · exact Prod.ext ((generatedFourthQ_short_fixed_iff q _).mpr hs)
        ((generatedFourthQ_tensor_fixed_iff q _).mpr ht)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
