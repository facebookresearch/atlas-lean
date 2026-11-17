/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.ChebyshevPsiZeroFree

/-!
# Tests for zero-free half-planes from error terms in `ψ(x)`

The hypothesis of `riemannZeta_ne_zero_of_forall_isBigO_rpow` is satisfiable: Chebyshev's bound
`ψ(x) ≪ x` gives it at `θ = 1`, recovering `ζ(s) ≠ 0` for `Re s > 1`.
-/

@[expose] public section

open Filter Asymptotics

namespace ChebyshevPsiZeroFreeTest

/-- `ψ(x) - x = O(x^{1+ε})` for every `ε > 0`, by Chebyshev's bound. -/
private theorem psi_sub_self_isBigO_rpow_one_add {ε : ℝ} (hε : 0 < ε) :
    (fun x : ℝ => Chebyshev.psi x - x) =O[atTop] (fun x : ℝ => x ^ (1 + ε)) := by
  refine IsBigO.of_bound (Real.log 4 + 5) ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hx0 : 0 ≤ x := by linarith
  have hψ := Chebyshev.psi_le_const_mul_self hx0
  have hψ0 := Chebyshev.psi_nonneg x
  have hxr : x ≤ x ^ (1 + ε) := by
    calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ x ^ (1 + ε) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ (1 + ε)),
    abs_le]
  constructor <;> nlinarith

/-- With `θ = 1` the theorem recovers the classical half-plane `Re s > 1`. -/
example (s : ℂ) (hs : 1 < s.re) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_forall_isBigO_rpow (θ := 1)
    (fun _ hε => psi_sub_self_isBigO_rpow_one_add hε) s hs

/-- The Mellin representation at `s = 2`. -/
example : LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) 2 =
    2 * ∫ t in Set.Ioi (1 : ℝ), ((Chebyshev.psi t : ℝ) : ℂ) * (t : ℂ) ^ (-2 - 1 : ℂ) :=
  LSeries_vonMangoldt_eq_mul_integral_chebyshevPsi (by norm_num)

end ChebyshevPsiZeroFreeTest
