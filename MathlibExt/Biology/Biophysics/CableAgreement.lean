/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Basic.Real.Basic

/-!
# Cable parameter agreement

For positive cable parameters, the time and space constants are positive and satisfy the defining relation; a sealed end is the zero-derivative condition.
-/

@[expose] public section

namespace MathlibExt.Biology.Biophysics.CableAgreement

/-- **Cable parameter agreement.** For positive membrane and
axial resistances and membrane capacitance (`rm, ri, cm > 0`), the
cable time constant `tau = rm * cm` is positive and the space
constant `ell = Real.sqrt (rm / ri)` satisfies
`ell ^ 2 * ri = rm`. -/
theorem cable_parameters {rm ri cm : ℝ} (hrm : 0 < rm) (hri : 0 < ri)
    (hcm : 0 < cm) :
    0 < rm * cm ∧ Real.sqrt (rm / ri) ^ 2 * ri = rm ∧
      0 < Real.sqrt (rm / ri) := by
  have hdiv : 0 ≤ rm / ri := le_of_lt (div_pos hrm hri)
  have hsq : Real.sqrt (rm / ri) ^ 2 = rm / ri := Real.sq_sqrt hdiv
  refine ⟨mul_pos hrm hcm, ?_, Real.sqrt_pos.mpr (div_pos hrm hri)⟩
  rw [hsq, div_mul_cancel₀ rm (ne_of_gt hri)]

/-- **Sealed-end boundary in derivative form.** A sealed axial
current at a boundary point is equivalent, for the axial current
`I` with `I x = -c * V' x` and `c ≠ 0`, to the zero spatial
derivative condition `V' x = 0` at that point. -/
theorem sealed_end_iff {c d : ℝ} (hc : c ≠ 0) :
    (-c * d = 0) ↔ d = 0 := by
  have hc' : -c ≠ 0 := neg_ne_zero.mpr hc
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hc'
  · intro h
    rw [h, mul_zero]


end MathlibExt.Biology.Biophysics.CableAgreement
