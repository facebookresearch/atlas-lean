/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastDot24
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsQFastMasks

/-! Exact fast dot products evaluate the original complete central correction.
The triangular rows and all linear coefficients are retained without alteration. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original selected triangular rows, evaluated with exact fast twenty-four-bit dots. -/
def generatedNinthLowerSpinFastQMaskPhase (rows : Fin 24 → ℕ) (v : ℕ) : ℕ :=
  monsterCo1GeometryBinaryMaskSum (List.ofFn (fun i : Fin 24 =>
    if v.testBit i.val then generatedNinthLowerSpinFastDot24 (rows i) v else 0))

/-- The complete phase polynomial and all original linear central coefficients. -/
def generatedNinthLowerSpinFastQMaskCentral (rows : Fin 24 → ℕ) (coeff v : ℕ) : ℕ :=
  Nat.xor (generatedNinthLowerSpinFastQMaskPhase rows v)
    (generatedNinthLowerSpinFastDot24 coeff v)

/-- Every selected row has exactly the original natural-number phase value. -/
theorem generatedNinth_lower_spin_fast_q_mask_phase (rows : Fin 24 → ℕ) (v : ℕ) :
    generatedNinthLowerSpinFastQMaskPhase rows v = generatedAxisGlobalQMaskPhase rows v := by
  unfold generatedNinthLowerSpinFastQMaskPhase generatedAxisGlobalQMaskPhase
  simp_rw [generatedNinth_lower_spin_fast_dot24]

/-- The fast evaluator equals the entire original central value, for arbitrary masks and rows.
It preserves every cocycle and linear correction bit rather than just the binary vector. -/
theorem generatedNinth_lower_spin_fast_q_mask_central
    (rows : Fin 24 → ℕ) (coeff v : ℕ) :
    generatedNinthLowerSpinFastQMaskCentral rows coeff v =
      generatedAxisGlobalQMaskCentral rows coeff v := by
  unfold generatedNinthLowerSpinFastQMaskCentral generatedAxisGlobalQMaskCentral
  rw [generatedNinth_lower_spin_fast_q_mask_phase, generatedNinth_lower_spin_fast_dot24]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
