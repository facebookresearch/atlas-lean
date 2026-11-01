/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsXiCoefficients
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsTensorColumns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.XiSpinLeechCompatibility

/-! Exact denominator-cleared physical coefficients of the genuine local Xi action. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The true physical Xi matrix is one half of its displayed integral numerator. -/
theorem generatedAxisGlobalXi_matrix_entry (i j : Fin 24) :
    co1XiMatrix i j = (co1XiNumerator i j : ℝ) / 2 := by
  change (((co1XiNumerator i j : ℚ) / 2 : ℚ) : ℝ) = _
  norm_num

/-- The actual orthogonal Xi spin factor is exactly the previously proved source operator. -/
theorem generatedAxisGlobalXi_spin_factor (f : SpinSpace) (t : SpinIndex) :
    xiSpinHolomorph.val f t = xiSpinOperator f t := by
  change xiSpinEndHom xiSpinHolomorph f t = _
  rw [xiSpinEndHom_xi]

/-- The actual local Xi output is a sum of sixty-four shifted rows and four physical columns. -/
theorem generatedAxisGlobalXi_tensor_coordinate (T : SpinIndex → Fin 24 → ℝ)
    (t : SpinIndex) (i : Fin 24) :
    16 * localTensorRepresentation xiSpinLocalFiber T t i =
      ∑ a : XiGrayIndex, ∑ j : Fin 24,
        qSign (generatedAxisGlobalXiSpinPhase a t) *
          (co1XiNumerator i j : ℝ) * T (t + xiGrayCode a) j := by
  have hx (j : Fin 24) : xiSpinLocalFiber.val.2.val (Pi.single j 1) i =
      (co1XiNumerator i j : ℝ) / 2 := by
    change (co1XiMatrix *ᵥ Pi.single j 1) i = _
    rw [Matrix.mulVec_single_one]
    exact generatedAxisGlobalXi_matrix_entry i j
  rw [generatedAxisGlobalTensor_local_coordinate]
  simp_rw [hx]
  change 16 * (∑ j : Fin 24, xiSpinHolomorph.val (fun u => T u j) t *
    ((co1XiNumerator i j : ℝ) / 2)) = _
  simp_rw [generatedAxisGlobalXi_spin_factor]
  calc
    _ = ∑ j : Fin 24, (8 * xiSpinOperator (fun u => T u j) t) *
        (co1XiNumerator i j : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ j : Fin 24, (∑ a : XiGrayIndex,
        qSign (generatedAxisGlobalXiSpinPhase a t) * T (t + xiGrayCode a) j) *
          (co1XiNumerator i j : ℝ) := by
      simp_rw [generatedAxisGlobalXiSpin_apply]
    _ = _ := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro j _
      ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
