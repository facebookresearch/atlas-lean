/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Half-period sine sum for even modulus

For a positive even natural number `N` and a natural number `q`,
`MetaMathlibExt.sum_sin_two_pi_mul_div_of_even` evaluates the sine sum over half a period,
`∑_{ℓ=1}^{N/2} sin (2π q ℓ / N)`: it is `0` for `q` even and `cot (q π / N)` for `q` odd. This is
Lemma 5 of Dombrowski and Dresden, *Areas Between Cosines*, one of the trigonometric sums behind
their limiting areas between `cos^n x` and `cos^n (k x)`.

## Proof

The proof follows the paper's, which applies Lagrange's trigonometric identity. Write `N = 2 M`
and `x = q π / N`. The product-to-sum formula
`2 sin x sin (2 ℓ x) = cos ((2 ℓ - 1) x) - cos ((2 ℓ + 1) x)` telescopes to Lagrange's identity
with the division cleared, `2 sin x ∑_{ℓ=1}^{M} sin (2 ℓ x) = cos x - cos ((2 M + 1) x)`. Since
`(2 M + 1) x = x + q π`, the right-hand side is `(1 - (-1) ^ q) cos x`.

* For `q` odd, `sin x ≠ 0`, as `x = n π` with `n` an integer would give `q = 2 M n`; dividing by
  `2 sin x` gives `cos x / sin x = cot x`.
* For `q` even, the right-hand side is `0`. If `sin x ≠ 0`, the sum is `0`. Otherwise `x = n π`
  with `n` an integer and every term `sin (2 ℓ x) = sin (2 ℓ n π)` is `0`. The paper divides by
  `sin x` without treating this case, which occurs exactly when `N` divides `q`.

## References

* Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*, Journal of Integer
  Sequences 28 (2025), Article 25.2.3; preprint arXiv:2404.17694v3, where the result and the proof
  followed here are Lemma 5 of Section 5.1 (*Three applications of Lagrange's identity*).
-/

namespace MetaMathlibExt

open Real

/-- Lagrange's trigonometric identity with the division cleared:
`2 sin x ∑_{ℓ=1}^{M} sin (2 ℓ x) = cos x - cos ((2 M + 1) x)`, by telescoping
`2 sin x sin (2 ℓ x) = cos ((2 ℓ - 1) x) - cos ((2 ℓ + 1) x)`. -/
private theorem two_mul_sin_mul_sum_Icc_sin (x : ℝ) (M : ℕ) :
    2 * sin x * ∑ l ∈ Finset.Icc 1 M, sin (2 * l * x) = cos x - cos ((2 * M + 1) * x) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih, two_mul_sin_mul_sin,
      show x - 2 * ((M + 1 : ℕ) : ℝ) * x = -((2 * M + 1) * x) by push_cast; ring, cos_neg,
      show x + 2 * ((M + 1 : ℕ) : ℝ) * x = (2 * ((M + 1 : ℕ) : ℝ) + 1) * x by push_cast; ring]
    ring

/-- **Half-period sine sum for even modulus.** Let $N$ be a positive even natural number. For
every natural number $q$, $\sum_{\ell=1}^{N/2} \sin(2\pi q \ell / N)$ equals $0$ if $q$ is even
and $\cot(q\pi / N)$ if $q$ is odd.

The paper also assumes $q > 0$; for $q = 0$ both sides are $0$.

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Lemma 5
(`jis-2025-25.2.3-lem-5`). -/
public theorem sum_sin_two_pi_mul_div_of_even {N : ℕ} (hN : 0 < N) (hNe : Even N)
    (q : ℕ) :
    ∑ l ∈ Finset.Icc 1 (N / 2), sin (q * l * 2 * π / N) =
      if Even q then 0 else cot (q * π / N) := by
  obtain ⟨M, rfl⟩ := hNe
  have hM : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hMM : ((M + M : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  set x : ℝ := q * π / ((M + M : ℕ) : ℝ) with hx
  have hterm (l : ℕ) : sin (q * l * 2 * π / ((M + M : ℕ) : ℝ)) = sin (2 * l * x) := by
    rw [hx]
    congr 1
    ring
  rw [show (M + M) / 2 = M by omega, Finset.sum_congr rfl fun l _ => hterm l]
  -- Lagrange's identity, with `(2 M + 1) x = x + q π`.
  have key := two_mul_sin_mul_sum_Icc_sin x M
  rw [show (2 * (M : ℝ) + 1) * x = x + q * π by rw [hx]; push_cast; field_simp; ring,
    cos_add_nat_mul_pi] at key
  split_ifs with hq
  · -- `q` even: `2 sin x ∑ = 0`; when `sin x = 0`, `x = n π` and every term vanishes.
    rw [hq.neg_one_pow, one_mul, sub_self, mul_eq_zero, mul_eq_zero] at key
    rcases key with (h2 | hs) | hS
    · norm_num at h2
    · obtain ⟨n, hn⟩ := sin_eq_zero_iff.1 hs
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [← hn, show 2 * (l : ℝ) * (n * π) = ((2 * l * n : ℤ) : ℝ) * π by push_cast; ring]
      exact sin_int_mul_pi _
    · exact hS
  · -- `q` odd: `2 sin x ∑ = 2 cos x`, and `sin x ≠ 0` since `x = n π` would make `q` even.
    rw [(Nat.not_even_iff_odd.1 hq).neg_one_pow] at key
    have hs : sin x ≠ 0 := by
      intro hs
      obtain ⟨n, hn⟩ := sin_eq_zero_iff.1 hs
      rw [hx, eq_div_iff hMM, mul_right_comm, mul_left_inj' pi_ne_zero] at hn
      have h : n * ((M + M : ℕ) : ℤ) = q := by exact_mod_cast hn
      exact hq (Int.even_coe_nat q |>.1 ⟨n * M, by rw [← h]; push_cast; ring⟩)
    rw [cot_eq_cos_div_sin, eq_div_iff hs]
    linear_combination key / 2

end MetaMathlibExt
