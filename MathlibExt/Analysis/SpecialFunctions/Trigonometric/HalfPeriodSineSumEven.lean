/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Half-period sine sums

This file evaluates three sine sums over half a period, Lemmas 5, 6 and 7 of Dombrowski and
Dresden, *Areas Between Cosines*, which are among the trigonometric sums behind their limiting
areas between `cos^n x` and `cos^n (k x)`. Throughout, `q` is a natural number, and `tan` and `cot`
are `sin / cos` and `cos / sin`, with `x / 0 = 0`.

## Main statements

* `MetaMathlibExt.sum_sin_two_pi_mul_div_of_even` (Lemma 5): for a positive even natural number
  `N`, `∑_{ℓ=1}^{N/2} sin (2π q ℓ / N)` is `0` for `q` even and `cot (q π / N)` for `q` odd.
* `MetaMathlibExt.sum_sin_two_pi_mul_div_of_odd` (Lemma 6): for an odd natural number `N`,
  `∑_{ℓ=1}^{(N-1)/2} sin (2π q ℓ / N)` is `-(1/2) tan (q π / (2 N))` for `q` even and
  `(1/2) cot (q π / (2 N))` for `q` odd.
* `MetaMathlibExt.sum_sin_pi_mul_div_of_even_of_even` (Lemma 7): for a positive even natural
  number `N` and an even natural number `q`, `∑_{ℓ=1}^{N/2} sin (q ℓ π / N)` is `0` for
  `q ≡ 0 (mod 4)` and `cot (q π / (2 N))` for `q ≡ 2 (mod 4)`.

## Proofs

As in the paper, Lemmas 5 and 6 come from Lagrange's trigonometric identity. The product-to-sum
formula `2 sin x sin (2 ℓ x) = cos ((2 ℓ - 1) x) - cos ((2 ℓ + 1) x)` telescopes to Lagrange's
identity with the division cleared, `2 sin x ∑_{ℓ=1}^{M} sin (2 ℓ x) = cos x - cos ((2 M + 1) x)`.

* Lemma 5: write `N = 2 M` and `x = q π / N`. Since `(2 M + 1) x = x + q π`, the right-hand side
  is `(1 - (-1) ^ q) cos x`.
  - For `q` odd, `sin x ≠ 0`, as `x = n π` with `n` an integer would give `q = 2 M n`; dividing
    by `2 sin x` gives `cos x / sin x = cot x`.
  - For `q` even, the right-hand side is `0`. If `sin x ≠ 0`, the sum is `0`. Otherwise
    `x = n π` with `n` an integer and every term `sin (2 ℓ x) = sin (2 ℓ n π)` is `0`. The paper
    divides by `sin x` without treating this case, which occurs exactly when `N` divides `q`.
* Lemma 6: write `N = 2 M + 1` and `x = q π / N = 2 y`. Since `(2 M + 1) x = q π`, the right-hand
  side is `cos x - (-1) ^ q`, which by the double-angle formulas is `-2 sin y ^ 2` for `q` even
  and `2 cos y ^ 2` for `q` odd, while `2 sin x = 4 sin y cos y`.
  - If `sin x ≠ 0`, then `sin y ≠ 0` and `cos y ≠ 0`, and dividing by `4 sin y cos y` gives
    `-(1/2) sin y / cos y = -(1/2) tan y` for `q` even and `(1/2) cos y / sin y = (1/2) cot y`
    for `q` odd.
  - Otherwise `sin x = 0`, which occurs exactly when `N` divides `q`: then `x = n π` with `n` an
    integer, and every term `sin (2 ℓ x) = sin (2 ℓ n π)` is `0`; as `sin y cos y = 0`, both
    `tan y` and `cot y` are `0` too.
* Lemma 7 is deduced from Lemma 5: write `q = 2 r`. Then `sin (q ℓ π / N) = sin (2π r ℓ / N)`,
  `q ≡ 0 (mod 4)` exactly when `r` is even, and `q π / (2 N) = r π / N`.

## References

* Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*, Journal of Integer
  Sequences 28 (2025), Article 25.2.3; preprint arXiv:2404.17694v3, where the results are
  Lemmas 5, 6 and 7 of Section 5.1 (*Three applications of Lagrange's identity*).
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
      exact hq (Int.even_natCast q |>.1 ⟨n * M, by rw [← h]; push_cast; ring⟩)
    rw [cot_eq_cos_div_sin, eq_div_iff hs]
    linear_combination key / 2

/-- **Half-period sine sum for odd modulus.** Let $N$ be an odd natural number. For every
natural number $q$, $\sum_{\ell=1}^{(N-1)/2} \sin(2\pi q \ell / N)$ equals
$-\frac{1}{2} \tan\frac{q\pi}{2N}$ if $q$ is even and $\frac{1}{2} \cot\frac{q\pi}{2N}$ if $q$ is
odd.

The paper also assumes $q > 0$; for $q = 0$ both sides are $0$.

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Lemma 6
(`jis-2025-25.2.3-lem-6`). -/
public theorem sum_sin_two_pi_mul_div_of_odd {N : ℕ} (hN : Odd N) (q : ℕ) :
    ∑ l ∈ Finset.Icc 1 ((N - 1) / 2), sin (q * l * 2 * π / N) =
      if Even q then -(1 / 2) * tan (q * π / (2 * N)) else 1 / 2 * cot (q * π / (2 * N)) := by
  obtain ⟨M, rfl⟩ := hN
  have hN0 : 2 * (M : ℝ) + 1 ≠ 0 := by positivity
  set y : ℝ := q * π / (2 * ((2 * M + 1 : ℕ) : ℝ)) with hy
  have hterm (l : ℕ) :
      sin (q * l * 2 * π / ((2 * M + 1 : ℕ) : ℝ)) = sin (2 * l * (2 * y)) := by
    rw [hy]
    congr 1
    ring
  rw [show (2 * M + 1 - 1) / 2 = M by omega, Finset.sum_congr rfl fun l _ => hterm l]
  -- Lagrange's identity at `x = 2 y = q π / N`, where `N x = q π`.
  have key := two_mul_sin_mul_sum_Icc_sin (2 * y) M
  rw [show (2 * (M : ℝ) + 1) * (2 * y) = q * π by rw [hy]; push_cast; field_simp,
    cos_nat_mul_pi, sin_two_mul, cos_two_mul] at key
  by_cases h0 : sin y * cos y = 0
  · -- `sin x = 0`: then `x = n π`, every term vanishes, and so do `tan y` and `cot y`.
    have hS : ∑ l ∈ Finset.Icc 1 M, sin (2 * l * (2 * y)) = 0 := by
      obtain ⟨n, hn⟩ := sin_eq_zero_iff.1 (show sin (2 * y) = 0 by
        rw [sin_two_mul]; linear_combination 2 * h0)
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [← hn, show 2 * (l : ℝ) * (n * π) = ((2 * l * n : ℤ) : ℝ) * π by push_cast; ring]
      exact sin_int_mul_pi _
    have htan : tan y = 0 := by
      rcases mul_eq_zero.1 h0 with h | h <;> simp [tan_eq_sin_div_cos, h]
    have hcot : cot y = 0 := by
      rcases mul_eq_zero.1 h0 with h | h <;> simp [cot_eq_cos_div_sin, h]
    rw [hS, htan, hcot, mul_zero, mul_zero, ite_self]
  · have hs : sin y ≠ 0 := left_ne_zero_of_mul h0
    have hc : cos y ≠ 0 := right_ne_zero_of_mul h0
    split_ifs with hq
    · -- `q` even: `4 sin y cos y ∑ = cos x - 1 = -2 sin y ^ 2`.
      rw [hq.neg_one_pow] at key
      rw [tan_eq_sin_div_cos, mul_div_assoc' _ (sin y), eq_div_iff hc]
      apply mul_left_cancel₀ hs
      linear_combination key / 4 + sin_sq_add_cos_sq y / 2
    · -- `q` odd: `4 sin y cos y ∑ = cos x + 1 = 2 cos y ^ 2`.
      rw [(Nat.not_even_iff_odd.1 hq).neg_one_pow] at key
      rw [cot_eq_cos_div_sin, mul_div_assoc' _ (cos y), eq_div_iff hs]
      apply mul_left_cancel₀ hc
      linear_combination key / 4

/-- **Half-step sine sum for even modulus and even multiplier.** Let $N$ be a positive even
natural number and $q$ an even natural number. Then $\sum_{\ell=1}^{N/2} \sin(q \ell \pi / N)$
equals $0$ if $q \equiv 0 \pmod 4$ and $\cot(q\pi / (2N))$ if $q \equiv 2 \pmod 4$.

The paper also assumes $q > 0$; that hypothesis is dropped here.

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Lemma 7
(`jis-2025-25.2.3-lem-7`). -/
public theorem sum_sin_pi_mul_div_of_even_of_even {N q : ℕ} (hN : 0 < N)
    (hNe : Even N) (hq : Even q) :
    ∑ l ∈ Finset.Icc 1 (N / 2), sin (q * l * π / N) =
      if q % 4 = 0 then 0 else cot (q * π / (2 * N)) := by
  obtain ⟨r, rfl⟩ := hq
  -- With `q = 2 r`, the sum is the one of `sum_sin_two_pi_mul_div_of_even` for `r`.
  have hterm (l : ℕ) : sin (((r + r : ℕ) : ℝ) * l * π / N) = sin (r * l * 2 * π / N) := by
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl fun l _ => hterm l, sum_sin_two_pi_mul_div_of_even hN hNe r]
  -- `2 r ≡ 0 (mod 4)` exactly when `r` is even, and `2 r π / (2 N) = r π / N`.
  refine if_congr (by rw [Nat.even_iff]; omega) rfl ?_
  congr 1
  push_cast
  ring

end MetaMathlibExt
