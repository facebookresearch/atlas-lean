/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.DelayedLogisticHopf
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Tests for the Hopf data of the Hutchinson delayed logistic equation

Concrete parameters `r = 1`, `K = 1`, so `τ_c = π / 2`. Computed from the definitions:
* `∂_z charFun` at `(i, π / 2)` is `1 + (π / 2) i ≠ 0`;
* `rootDelay 1 i = π / 2`, and `rootDelayDeriv 1 = 1 + (π / 2) i`;
* `i` is a root at `τ_c` with real part `0`, so the exclusions in
  `re_neg_of_charFun_criticalDelay` cannot be dropped;
* the direction coefficient `(3π - 2) / 40` lies in `(0.18, 0.19)`;
* the zero-amplitude orbit is the equilibrium, and the amplitude-`1/2` orbit takes different
  values at `θ = 0` and `θ = π`, so it is not constant;
* `τ(0) = τ_c` and `τ(1/2) > τ_c`.
The main theorems are then instantiated at `r = K = 1`.
-/

@[expose] public section

open Real Filter Set
open scoped Topology
open MathlibExt.Biology.Dynamics.DelayedLogistic MathlibExt.Biology.Dynamics.DelayedLogisticHopf

namespace MathlibExtTest.Biology.Dynamics.DelayedLogisticHopf

/-! ### Spectral data at `r = 1`, computed from the definitions -/

/-- `∂_z charFun 1 (π / 2)` at `i` is `1 + (π / 2) i`, which is nonzero (simple root). -/
example : charFunDeriv 1 (π / 2) Complex.I = 1 + ((π / 2 : ℝ) : ℂ) * Complex.I ∧
    charFunDeriv 1 (π / 2) Complex.I ≠ 0 := by
  have h : -(Complex.I * ((π / 2 : ℝ) : ℂ)) = ((-(π / 2) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have hval : charFunDeriv 1 (π / 2) Complex.I = 1 + ((π / 2 : ℝ) : ℂ) * Complex.I := by
    rw [charFunDeriv, h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      cos_neg, sin_neg, cos_pi_div_two, sin_pi_div_two]
    push_cast; ring
  refine ⟨hval, ?_⟩
  rw [hval]
  intro h0
  have := congrArg Complex.re h0
  simp at this

/-- `i` is a root at `τ_c = π / 2` with real part `0`: the strict conclusion of
`re_neg_of_charFun_criticalDelay` fails without excluding `± i r`. -/
example : charFun 1 (π / 2) Complex.I = 0 ∧ Complex.I.re = 0 := by
  have h : -(Complex.I * ((π / 2 : ℝ) : ℂ)) = ((-(π / 2) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  refine ⟨?_, Complex.I_re⟩
  rw [charFun, h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, cos_neg,
    sin_neg, cos_pi_div_two, sin_pi_div_two]
  push_cast; ring

/-- `rootDelay 1 i = π / 2`: the delay at which `i` is a root is the critical delay. -/
example : rootDelay 1 Complex.I = ((π / 2 : ℝ) : ℂ) := by
  simp only [rootDelay, Complex.ofReal_one, div_one, Complex.log_neg_I]
  push_cast
  rw [div_eq_iff Complex.I_ne_zero]
  ring

/-- `rootDelayDeriv 1 = 1 + (π / 2) i`. -/
example : rootDelayDeriv 1 = 1 + ((π / 2 : ℝ) : ℂ) * Complex.I := by
  simp [rootDelayDeriv]

/-- The critical delay at `r = 1`. -/
example : criticalDelay 1 = π / 2 := by norm_num [criticalDelay]

/-! ### Normal-form data, computed from the definitions -/

/-- The direction coefficient `(3π - 2) / 40` is positive, about `0.186`. -/
example : 0.18 < hopfAlpha2 ∧ hopfAlpha2 < 0.19 := by
  unfold hopfAlpha2
  constructor <;> linarith [pi_gt_d2, pi_lt_d2]

/-- At zero amplitude the delay is the critical delay. -/
example : hopfDelay 1 0 = π / 2 := by norm_num [hopfDelay, hopfParam]

/-- At amplitude `1/2` the delay is strictly above `τ_c`. -/
example : π / 2 < hopfDelay 1 (1 / 2) := by
  norm_num [hopfDelay, hopfParam, hopfAlpha2]
  linarith [pi_gt_three]

/-- At zero amplitude the approximate orbit is the equilibrium `v ≡ 0`. -/
example (s : ℝ) : hopfApprox 0 s = 0 := by simp [hopfApprox, hopfProfile]

/-- The amplitude-`1/2` orbit at `θ = 0`. -/
example : hopfApprox (1 / 2) 0 = 1 / 2 + 1 / 20 + 1 / 640 := by
  norm_num [hopfApprox, hopfProfile]

/-- The amplitude-`1/2` orbit is not constant: its values at `θ = 0` and `θ = π` differ. -/
example : hopfApprox (1 / 2) 0 ≠ hopfApprox (1 / 2) (π / hopfFreq (1 / 2)) := by
  have hω : hopfFreq (1 / 2) ≠ 0 := by
    unfold hopfFreq hopfOmega2; linarith [pi_gt_three]
  have hθ : hopfFreq (1 / 2) * (π / hopfFreq (1 / 2)) = π := by field_simp
  have h3c : cos (3 * π) = -1 := by
    rw [show 3 * π = π + 2 * π by ring, cos_add_two_pi, cos_pi]
  have h3s : sin (3 * π) = 0 := by
    rw [show 3 * π = π + 2 * π by ring, sin_add_two_pi, sin_pi]
  simp only [hopfApprox, hθ, mul_zero, hopfProfile, one_mul, cos_zero, sin_zero, cos_pi,
    cos_two_pi, sin_two_pi, h3c, h3s]
  norm_num

/-! ### The main theorems at `r = K = 1` -/

/-- Just above `τ_c` there is a characteristic root with positive real part on the branch. -/
example : ∃ τ, π / 2 < τ ∧ charFun 1 τ (rootBranch one_pos τ) = 0 ∧
    0 < (rootBranch one_pos τ).re := by
  have h := ((eventually_rootBranch_re_pos_right one_pos).and
    (nhdsWithin_le_nhds (eventually_charFun_rootBranch one_pos))).and self_mem_nhdsWithin
  obtain ⟨τ, ⟨hre, hroot⟩, hτ⟩ := h.exists
  refine ⟨τ, ?_, hroot, hre⟩
  simpa [criticalDelay] using hτ

/-- The real part of the crossing speed at `r = 1` is `1 / (1 + (π / 2)²)`. -/
example : (rootDelayDeriv 1)⁻¹.re = 1 / (1 + (π / 2) ^ 2) := by
  simpa using re_inv_rootDelayDeriv one_pos

/-- The `O(ε⁴)` residual bound for Hutchinson's equation at `r = K = 1`. -/
example : ∃ C, ∀ ε t : ℝ, |ε| ≤ 1 →
    |deriv (hopfOrbit 1 1 ε) t -
        1 * hopfOrbit 1 1 ε t * (1 - hopfOrbit 1 1 ε (t - hopfDelay 1 ε) / 1)| ≤ C * ε ^ 4 :=
  exists_hopfOrbit_residual_le one_pos one_ne_zero

end MathlibExtTest.Biology.Dynamics.DelayedLogisticHopf
