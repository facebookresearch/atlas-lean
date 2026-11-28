/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import MathlibExt.Analysis.SpecialFunctions.ParabolicCylinder.Basic

/-!
# Pointwise Gamma products at U(a,0)

For complex s with Γ((s+1)/2) ≠ 0, Gamma duplication gives
Γ(s) U(s-1/2,0)=2^(s/2-1) Γ(s/2).
The condition is satisfied on Re(s)>0. The two-step shift gives
Γ(s+2) U(s+3/2,0)=2^(s/2) Γ(s/2+1) on Re(s)>-2.

These are pointwise identities of the ordinary totalized Gamma product;
the cancellation condition is retained at parameters where Gamma has poles.
The normalization is used in Helfgott, *Major arcs for Goldbach's problem*,
arXiv:1305.2897v4, §3.2.
-/

public section

namespace Complex

/-- For complex s satisfying Γ((s+1)/2) ≠ 0,
Γ(s) U(s-1/2,0)=2^(s/2-1) Γ(s/2).
This is a pointwise Gamma identity with its cancellation hypothesis. -/
theorem Gamma_mul_parabolicCylinderU_zero (s : ℂ)
    (hGamma : Gamma ((s + 1) / 2) ≠ 0) :
    Gamma s * parabolicCylinderU (s - 1 / 2) 0 =
      (2 : ℂ) ^ (s / 2 - 1) * Gamma (s / 2) := by
  have hpow : -(s - 1 / 2) / 2 - 1 / 4 = -s / 2 := by ring
  have harg : (s - 1 / 2) / 2 + 3 / 4 = (s + 1) / 2 := by ring
  have hdup : Gamma (s / 2) * Gamma ((s + 1) / 2) =
      Gamma s * (2 : ℂ) ^ (1 - s) * (Real.sqrt Real.pi : ℂ) := by
    have htwice : 2 * (s / 2) = s := by ring
    have hhalf : s / 2 + 1 / 2 = (s + 1) / 2 := by ring
    simpa only [htwice, hhalf] using Gamma_mul_Gamma_add_half (s / 2)
  have hpower : (2 : ℂ) ^ (s / 2 - 1) * (2 : ℂ) ^ (1 - s) =
      (2 : ℂ) ^ (-s / 2) := by
    rw [← cpow_add _ _ (by norm_num)]
    congr 1
    ring
  rw [parabolicCylinderU_zero, hpow, harg, ← mul_div_assoc]
  apply (div_eq_iff hGamma).mpr
  calc
    Gamma s * ((2 : ℂ) ^ (-s / 2) * (Real.sqrt Real.pi : ℂ)) =
        (2 : ℂ) ^ (-s / 2) * Gamma s * (Real.sqrt Real.pi : ℂ) := by ring
    _ = ((2 : ℂ) ^ (s / 2 - 1) * (2 : ℂ) ^ (1 - s)) *
        Gamma s * (Real.sqrt Real.pi : ℂ) := by rw [hpower]
    _ = (2 : ℂ) ^ (s / 2 - 1) *
        (Gamma s * (2 : ℂ) ^ (1 - s) * (Real.sqrt Real.pi : ℂ)) := by ring
    _ = ((2 : ℂ) ^ (s / 2 - 1) * Gamma (s / 2)) * Gamma ((s + 1) / 2) := by
      rw [← hdup]
      ring

/-- For complex s with Re(s)>0,
Γ(s) U(s-1/2,0)=2^(s/2-1) Γ(s/2). -/
theorem Gamma_mul_parabolicCylinderU_zero_of_re_pos (s : ℂ) (hs : 0 < s.re) :
    Gamma s * parabolicCylinderU (s - 1 / 2) 0 =
      (2 : ℂ) ^ (s / 2 - 1) * Gamma (s / 2) := by
  apply Gamma_mul_parabolicCylinderU_zero
  apply Gamma_ne_zero_of_re_pos
  have hre : ((s + 1) / 2).re = (s.re + 1) / 2 := by simp
  rw [hre]
  linarith

/-- For complex s with Re(s)>-2,
Γ(s+2) U(s+3/2,0)=2^(s/2) Γ(s/2+1). -/
theorem Gamma_mul_parabolicCylinderU_zero_shift_two (s : ℂ) (hs : -2 < s.re) :
    Gamma (s + 2) * parabolicCylinderU (s + 3 / 2) 0 =
      (2 : ℂ) ^ (s / 2) * Gamma (s / 2 + 1) := by
  have hpos : 0 < (s + 2).re := by
    simpa using (show (0 : ℝ) < s.re + 2 by linarith)
  have harg : (s + 2) - 1 / 2 = s + 3 / 2 := by ring
  have hhalf : (s + 2) / 2 = s / 2 + 1 := by ring
  simpa only [harg, hhalf, add_sub_cancel_right] using
    Gamma_mul_parabolicCylinderU_zero_of_re_pos (s + 2) hpos

end Complex
