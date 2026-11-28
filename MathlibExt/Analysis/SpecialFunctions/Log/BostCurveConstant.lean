/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The constant in Bost's lower bound for the Faltings height of a curve

Bost's lower bound for the stable Faltings height of a principally polarized abelian variety
of dimension `g` is `h_F(A) ≥ -(g/2) log(2π²)`. A. Javanpeykar, *Polynomial bounds for Arakelov
invariants of Belyi curves*, Algebra Number Theory 8 (2014), Lemma 2.4.4, p. 101, uses it for the
Jacobian of a curve of genus `g` in the weaker form `h_Fal(X) ≥ -log(2π) g`, and notes the
stronger form `-log(√2 π) g`. This file proves the comparison of these constants:

* `Javanpeykar.half_mul_log_two_mul_pi_sq`: `(g/2) log(2π²) = g log(√2 π)`;
* `Javanpeykar.neg_mul_log_two_mul_pi_le_neg_half_mul_log_two_mul_pi_sq`:
  `-g log(2π) ≤ -(g/2) log(2π²)` for `g ≥ 0`.
-/

@[expose] public section

set_option autoImplicit false

namespace Javanpeykar

open Real

/-- **The two forms of Bost's constant.** For every real `g`,
`(g / 2) log(2π²) = g log(√2 π)`.

Source: A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra
Number Theory 8 (2014), Lemma 2.4.4 and its proof, p. 101, which states the bound for a curve
of genus `g` as "the slightly stronger lower bound h_Fal(X) ≥ −log(√2 π)g". -/
theorem half_mul_log_two_mul_pi_sq (g : ℝ) :
    g / 2 * Real.log (2 * π ^ 2) = g * Real.log (Real.sqrt 2 * π) := by
  have hsq : (Real.sqrt 2 * π) ^ 2 = 2 * π ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
  rw [← hsq, Real.log_pow]
  push_cast
  ring

/-- **Bost's constant against `log(2π)`.** For every real `g ≥ 0`,
`-g log(2π) ≤ -(g / 2) log(2π²)`; so a lower bound `-(g/2) log(2π²)` for the Faltings height
implies the lower bound `-g log(2π)`. The proof uses `2π² ≤ (2π)²`.

Source: A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra
Number Theory 8 (2014), Lemma 2.4.4 (Bost), p. 101: "h_Fal(X) ≥ −log(2π)g", with "the slightly
stronger lower bound h_Fal(X) ≥ −log(√2 π)g". -/
theorem neg_mul_log_two_mul_pi_le_neg_half_mul_log_two_mul_pi_sq {g : ℝ} (hg : 0 ≤ g) :
    -g * Real.log (2 * π) ≤ -(g / 2) * Real.log (2 * π ^ 2) := by
  have hpi : 0 < π := Real.pi_pos
  have hle : Real.log (2 * π ^ 2) ≤ Real.log ((2 * π) ^ 2) :=
    Real.log_le_log (by positivity) (by nlinarith)
  rw [Real.log_pow] at hle
  push_cast at hle
  nlinarith

end Javanpeykar
