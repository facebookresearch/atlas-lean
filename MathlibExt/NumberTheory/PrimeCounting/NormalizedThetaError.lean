/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PrimeCounting.LaplaceThetaContinuation

@[expose] public section

/-!
# Normalized theta error: measurability and global bound

## ATLAS source correspondence

This is one input stage for ATLAS NumberTheoryI N324, Theorem 16.13
(Newman's Tauberian theorem). At atlas-lean commit
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`, the exact source statement is
indexed in
[`v1/Atlas/NumberTheoryI/targets.yaml`, lines 2266--2272](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/targets.yaml#L2266-L2272):
a bounded,
piecewise-continuous `f : ℝ≥0 → ℝ` whose Laplace transform extends
holomorphically to `0 ≤ re s` has a convergent improper integral equal to
the continuation at zero. Its Lean statement is
[`Chapter16.thm_16_13_newman_tauberian` in `v1/Atlas/NumberTheoryI/code/PNT.lean`,
lines 1061--1081](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/PNT.lean#L1061-L1081);
the boundedness
hypothesis is represented there by
`∃ M, ∀ t : ℝ, 0 ≤ t → |f t| ≤ M`.

For the prime-number-theorem application, the same source
[defines `H(t) = θ(exp t) * exp(-t) - 1` and proves `H_bounded`, lines
1083--1103](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/PNT.lean#L1083-L1103),
with the witness `M = log 4 + 1`. The declarations here map to
that concrete input as follows:

* `normalizedThetaError` (imported from the preceding N323 stage) is exactly
  the source function `H`.
* `measurable_normalizedThetaError` supplies the measurable regularity needed
  by Mathlib's Bochner/Laplace integration API. It does not assert the source's
  piecewise continuity hypothesis or the generic Newman theorem.
* `abs_normalizedThetaError_le` proves the source estimate using
  `0 ≤ θ(exp t) ≤ (log 4) exp t` and `exp t * exp(-t) = 1`. Its global
  quantifier is a harmless strengthening of this auxiliary estimate: restricting
  it to `0 ≤ t` gives exactly the hypothesis used by N324.
* `normalizedThetaError_bounded` packages the exact source-shaped hypothesis
  with `M = log 4 + 1`.

This PR establishes only measurability and boundedness for the concrete `H`.
It does not prove the
[contour argument (`PNT.lean`, lines 878--1060)](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/PNT.lean#L878-L1060),
the generic N324 conclusion, convergence of `∫ H`, or the prime number theorem.
-/

namespace Chebyshev

/-- **Measurability of the normalized theta error.** Let $\theta(x) = \sum_{p \le x} \log p$ be
Chebyshev's function, the sum running over primes $p$. The normalized theta error
$H(t) = \theta(e^t)e^{-t} - 1$ is a Borel measurable function of $t \in \mathbb{R}$. -/
theorem measurable_normalizedThetaError :
    Measurable normalizedThetaError := by
  unfold normalizedThetaError
  exact ((theta_mono.measurable.comp Real.measurable_exp).mul
    (Real.measurable_exp.comp measurable_neg)).sub_const 1

/-- **Explicit bound for the normalized theta error.** Let $\theta(x) = \sum_{p \le x} \log p$ be
Chebyshev's function, the sum running over primes $p$, and let $H(t) = \theta(e^t)e^{-t} - 1$ be
the normalized theta error. Then $|H(t)| \le \log 4 + 1$ for every real $t$.

The bound holds for all real $t$, not only for $t \ge 0$. -/
theorem abs_normalizedThetaError_le (t : ℝ) :
    |normalizedThetaError t| ≤ Real.log 4 + 1 := by
  have hx : (0 : ℝ) ≤ Real.exp t := le_of_lt (Real.exp_pos t)
  have hexp_pos : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
  have htheta_nn : (0 : ℝ) ≤ theta (Real.exp t) :=
    theta_nonneg (Real.exp t)
  have htheta_le : theta (Real.exp t) ≤ Real.log 4 * Real.exp t :=
    theta_le_log4_mul_x (le_of_lt (Real.exp_pos t))
  have hlog_nn : (0 : ℝ) ≤ Real.log 4 :=
    Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
  have hexp : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hprod_nn : (0 : ℝ) ≤ theta (Real.exp t) * Real.exp (-t) :=
    mul_nonneg htheta_nn (le_of_lt hexp_pos)
  have hprod_le : theta (Real.exp t) * Real.exp (-t) ≤ Real.log 4 := by
    calc theta (Real.exp t) * Real.exp (-t)
        ≤ (Real.log 4 * Real.exp t) * Real.exp (-t) :=
          mul_le_mul_of_nonneg_right htheta_le (le_of_lt hexp_pos)
      _ = Real.log 4 * (Real.exp t * Real.exp (-t)) := by ring
      _ = Real.log 4 := by rw [hexp, mul_one]
  rw [abs_le]
  unfold normalizedThetaError
  constructor
  · linarith
  · linarith

/-- **Boundedness of the normalized theta error on $[0, \infty)$.** Let
$\theta(x) = \sum_{p \le x} \log p$ be Chebyshev's function, the sum running over primes $p$, and
let $H(t) = \theta(e^t)e^{-t} - 1$ be the normalized theta error. There is a real number $M$ such
that $|H(t)| \le M$ for every real $t \ge 0$. -/
theorem normalizedThetaError_bounded :
    ∃ M : ℝ, ∀ t : ℝ, 0 ≤ t → |normalizedThetaError t| ≤ M :=
  ⟨Real.log 4 + 1, fun t _ => abs_normalizedThetaError_le t⟩

end Chebyshev
