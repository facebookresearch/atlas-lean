/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Positivity of the monic Chebyshev polynomials

`Polynomial.Chebyshev.C R n` is the polynomial `T̄_n(X)` that Kassel and Reutenauer call the monic
Chebyshev polynomial: `T̄_0 = 2`, `T̄_1 = X` and `T̄_{n+2} = X T̄_{n+1} - T̄_n`, so that
`T̄_n(q + q⁻¹) = q^n + q^{-n}`. `MetaMathlibExt.chebyshevC_eval_pos_of_two_le` states that
`T̄_k(x) > 0` for every natural number `k` and every real number `x ≥ 2`.

## Proof

For `x ≥ 2`, induction on `n` shows `2 ≤ T̄_n(x) ≤ T̄_{n+1}(x)`. The case `n = 0` is
`T̄_0(x) = 2 ≤ x = T̄_1(x)`. If the claim holds for `n`, then `T̄_{n+1}(x) ≥ T̄_n(x) ≥ 2`, and
`T̄_{n+2}(x) = x T̄_{n+1}(x) - T̄_n(x) ≥ 2 T̄_{n+1}(x) - T̄_n(x) ≥ T̄_{n+1}(x)`. The paper argues
instead that the zeros of `T̄_k(X) = 2 T_k(X / 2)` lie in `(-2, 2)` and that `T̄_k` is monic.

## References

* C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*, Journal of Integer
  Sequences 29 (2026), Article 26.4.4. The statement is Proposition 3.1 of version 2 of the arXiv
  preprint, arXiv:2507.15780v2; version 1 does not contain it.
-/

open Polynomial

namespace MetaMathlibExt

/-- For `x ≥ 2`, the values `T̄_n(x)` are at least `2` and nondecreasing in `n`. -/
private theorem two_le_eval_chebyshevC_and_le_succ {x : ℝ} (hx : 2 ≤ x) (n : ℕ) :
    2 ≤ (Chebyshev.C ℝ n).eval x ∧
      (Chebyshev.C ℝ n).eval x ≤ (Chebyshev.C ℝ (n + 1 : ℕ)).eval x := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    obtain ⟨h2, hle⟩ := ih
    refine ⟨h2.trans hle, ?_⟩
    have hrec : (Chebyshev.C ℝ (n + 1 + 1 : ℕ)).eval x =
        x * (Chebyshev.C ℝ (n + 1 : ℕ)).eval x - (Chebyshev.C ℝ n).eval x := by
      rw [show ((n + 1 + 1 : ℕ) : ℤ) = n + 2 by push_cast; ring, Chebyshev.C_add_two]
      simp
    have hmul : 2 * (Chebyshev.C ℝ (n + 1 : ℕ)).eval x ≤ x * (Chebyshev.C ℝ (n + 1 : ℕ)).eval x :=
      mul_le_mul_of_nonneg_right hx (by linarith)
    rw [hrec]
    linarith

/-- **Positivity of the monic Chebyshev polynomials.** Let $\bar T_k \in \mathbb{R}[X]$ be the
monic Chebyshev polynomials, given by $\bar T_0 = 2$, $\bar T_1 = X$ and
$\bar T_{k+2} = X \bar T_{k+1} - \bar T_k$. Then $\bar T_k(x) > 0$ for every natural number $k$
and every real number $x \ge 2$.

Source: C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*,
Journal of Integer Sequences 29 (2026), Article 26.4.4, Proposition 3.1
(`jis-2026-26.4.4-prop-6`). -/
public theorem chebyshevC_eval_pos_of_two_le (k : ℕ) (x : ℝ) (hx : 2 ≤ x) :
    0 < (Chebyshev.C ℝ k).eval x :=
  zero_lt_two.trans_le (two_le_eval_chebyshevC_and_le_succ hx k).1

end MetaMathlibExt
