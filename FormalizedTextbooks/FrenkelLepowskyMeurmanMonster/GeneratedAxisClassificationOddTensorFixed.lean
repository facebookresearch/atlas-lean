/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddSpinBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOddCocode

/-! Fixation of the actual odd-axis tensor is equivalent to fixation of its
nonzero distinguished Hadamard spin state. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual third first-column representative, without a source class label. -/
noncomputable def generatedOddAxis : GriessSpace :=
  sExtra (conwayShortAxis (Sum.inr (Sum.inr (0, 0))) 0)

/-- The nonzero scalar relating the original axis tensor and its Hadamard state. -/
noncomputable def generatedOddTensorScale : ℝ := -8 / Real.sqrt 2

/-- The original tensor normalization does not vanish. -/
theorem generatedOddTensorScale_ne_zero : generatedOddTensorScale ≠ 0 := by
  exact div_ne_zero (by norm_num) (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))

/-- The actual distinguished odd-axis tensor is a single spatial column of the
original two-point Hadamard state. -/
theorem generatedOddAxis_tensor (t : SpinIndex) (j : Fin 24) :
    (griessConwayEncode generatedOddAxis).2.2 t j =
      generatedOddTensorScale * generatedOddSpinState 0 1 0 t * (if j = 0 then 1 else 0) := by
  rw [generatedOddAxis, generatedAxis_triality_odd_tensor]
  simp only [Pi.smul_apply, smul_eq_mul, qSign_zero, mul_one,
    generatedOddSpin_Y_binding, generatedOddTensorScale]
  ring

/-- The genuine Q tensor action acts on the same distinguished state. -/
theorem generatedOddAxis_Q_tensor (q : Q) (t : SpinIndex) (j : Fin 24) :
    localTensorRepresentation (localFiberIncl q) (griessConwayEncode generatedOddAxis).2.2 t j =
      generatedOddTensorScale * spinRepresentation q (generatedOddSpinState 0 1 0) t *
        (if j = 0 then 1 else 0) := by
  rw [localTensorRepresentation_q]
  change spinOperator q (fun u => (griessConwayEncode generatedOddAxis).2.2 u j) t =
    generatedOddTensorScale * spinOperator q (generatedOddSpinState 0 1 0) t * _
  simp only [spinOperator, LinearMap.coe_mk, AddHom.coe_mk, generatedOddAxis_tensor]
  ring

/-- The actual odd-axis tensor is fixed exactly when its distinguished spin state is fixed. -/
theorem generatedOddAxis_Q_tensor_fixed_iff (q : Q) :
    localTensorRepresentation (localFiberIncl q) (griessConwayEncode generatedOddAxis).2.2 =
      (griessConwayEncode generatedOddAxis).2.2 ↔
        spinRepresentation q (generatedOddSpinState 0 1 0) = generatedOddSpinState 0 1 0 := by
  constructor
  · intro h
    ext t
    have he := congrFun (congrFun h t) (0 : Fin 24)
    rw [generatedOddAxis_Q_tensor, generatedOddAxis_tensor] at he
    simp only [ite_true, mul_one] at he
    exact mul_left_cancel₀ generatedOddTensorScale_ne_zero he
  · intro h
    ext t j
    rw [generatedOddAxis_Q_tensor, generatedOddAxis_tensor, h]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
