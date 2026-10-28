/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.Axer
import MathlibExt.NumberTheory.PrimeCounting.MertensFunctionBound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Tests for Axer's theorem
-/

@[expose] public section

open Finset Filter Asymptotics ArithmeticFunction
open scoped ArithmeticFunction.Moebius

-- `β = 0` of the power-sum bound: `∑_{n ≤ K} 1 ≤ K`.
example (K : ℕ) (hK : 1 ≤ K) :
    ∑ n ∈ Icc 1 K, (n : ℝ) ^ (-(0 : ℝ)) ≤ (K : ℝ) ^ ((1 : ℝ) - 0) / (1 - 0) :=
  Real.sum_Icc_rpow_neg_le le_rfl one_pos hK

/-- The hypothesis `M(x) = o(x)` of Axer's theorem is satisfiable: it follows from the
zero-free-region bound for the Mertens function. -/
private theorem mertens_isLittleO_id : (fun x : ℝ => (mertens x : ℝ)) =o[atTop] fun x : ℝ => x := by
  obtain ⟨c, hc, h⟩ := mertens_isBigO_mul_exp_neg_mul_log_rpow
  refine h.trans_isLittleO ?_
  have hg : Tendsto (fun x : ℝ => Real.exp (-c * Real.log x ^ (1 / 10 : ℝ))) atTop (nhds 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    have h1 : Tendsto (fun x : ℝ => Real.log x ^ (1 / 10 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
    rw [show (fun x : ℝ => -c * Real.log x ^ (1 / 10 : ℝ)) =
      fun x => -(c * Real.log x ^ (1 / 10 : ℝ)) by ext; ring]
    exact tendsto_neg_atTop_atBot.comp (h1.const_mul_atTop hc)
  have := ((isLittleO_one_iff ℝ).mpr hg).mul_isBigO (isBigO_refl (fun x : ℝ => x) atTop)
  simpa [mul_comm] using this

-- Instantiating Axer's Möbius estimate with `G ≡ 1`, `β = 0` recovers `M(x) = o(x)`.
example : (fun x : ℝ => ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * (fun _ : ℝ => (1 : ℝ)) (x / n))
    =o[atTop] fun x : ℝ => x :=
  isLittleO_sum_moebius_mul_comp_div le_rfl one_pos
    (by simp only [Real.rpow_zero]; exact isBigO_refl _ _)
    (fun _ => MonotoneOn.boundedVariationOn (f := fun _ : ℝ => (1 : ℝ)) (C := 1)
      (fun _ _ _ _ _ => le_rfl) (fun _ _ => by norm_num))
    mertens_isLittleO_id

-- The bounded-variation closure lemma, for `g = id`.
example (T : ℝ) :
    BoundedVariationOn (fun y : ℝ => ∑ n ∈ Icc 1 ⌊y⌋₊, (y / n)) (Set.Icc 1 T) :=
  boundedVariationOn_sum_comp_div_floor
    (fun T => MonotoneOn.boundedVariationOn (f := fun y : ℝ => y) (C := |T|)
      (fun _ _ _ _ h => h) (fun x hx => by
        rw [abs_of_nonneg (by linarith [hx.1])]
        exact hx.2.trans (le_abs_self T))) T
