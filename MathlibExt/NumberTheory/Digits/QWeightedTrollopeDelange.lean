/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Digits.Defs

/-!
# The `q`-weighted Trollope–Delange formula

For an element `q` of a commutative ring, the `q`-weighted binary digit sum of a natural number
`k = ∑ ωᵢ 2ⁱ` is `s_q(k) = ∑ ωᵢ q^(i+1)` (`qWeightedDigitSum`), and `S_q(n) = ∑_{k<n} s_q(k)` is
its partial sum (`qWeightedDigitPartialSum`). The Takagi–Landsberg function is
`𝒯_a(x) = ∑ aⁿ τ(2ⁿ x)` (`takagiLandsberg`), where `τ(y)` is the distance from `y` to the
nearest integer. This file proves that, for complex `q` with `|q| > 1/2` and `a = 1/(2q)`, the
normalized fluctuation of `S_q` at the dyadic grid points `t = j / 2^(N-1)` of `[0, 1]` is
`-q 𝒯_a(t)` (`qWeightedDigitPartialSum_dyadic_fluctuation`). It also proves the
Trollope–Delange formula for real `q` (`qWeighted_trollopeDelange`).

## Main results

* `MetaMathlibExt.qWeightedDigitPartialSum_dyadic_fluctuation`: for `0 < N` and
  `j ≤ 2^(N-1)`,
  `(S_q(2j) - (j / 2^(N-1)) S_q(2^N)) / (2q)^(N-1) = -q 𝒯_a(j / 2^(N-1))`.
* `MetaMathlibExt.qWeighted_trollopeDelange`: the exact formula for the average `S_q(n) / n`
  in terms of a geometric sum and the Takagi–Landsberg function.

## Proof outline

At a dyadic rational `n / 2^M` the Takagi–Landsberg series stops after `M` terms, since
`τ(2^k n / 2^M) = 0` for `k ≥ M`. So `𝒯_a(n / 2^(M+1)) = τ(n / 2^(M+1)) + a 𝒯_a(n / 2^M)`, and
`𝒯_a` has period `1`. On the digit side, `s_q(2^M + k) = s_q(k) + q^(M+1)` for `k < 2^M`, so
`S_q(2^M + r) = S_q(2^M) + S_q(r) + r q^(M+1)` for `r ≤ 2^M`. An induction on `M`, splitting
`n ≤ 2^(M+1)` according to `n ≤ 2^M` or `n = 2^M + r`, gives
`S_q(n) = (n / 2^M) S_q(2^M) - (2q)^M 𝒯_a(n / 2^M) / 2` for every `n ≤ 2^M`. Taking `M = N` and
`n = 2j` gives the theorem, since `2j / 2^N = j / 2^(N-1)`; the hypothesis `|q| > 1/2` is used
only through `q ≠ 0`. For the Trollope–Delange formula, take `M = ⌊log₂ n⌋ + 1`, compute
`S_q(2^M)` by the geometric sum, and express `n / 2^M` in terms of the fractional logarithm.

## Implementation notes

`qWeightedDigitSum`, `qWeightedDigitPartialSum`, `takagiLandsberg`, their completed lemmas and
both theorems keep the full names, statements, definition bodies and docstrings they had in
`WantedExt.NumberTheory.QWeightedTrollopeDelangeWanted`, which imports this module and keeps its
other wanted statements about these functions. The auxiliary lemmas of the proof are private.

## References

* Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*, INTEGERS 26
  (2026), Article A61; arXiv:2407.15201 (version 3), Section 4, Proposition 1.
-/

namespace MetaMathlibExt

@[expose] public section

open Finset

/-- **The $q$-weighted binary digit sum.** Let $q$ be an element of a commutative ring and let
$k$ be a natural number with binary expansion $k = \sum_{i \ge 0} \omega_i 2^i$, where
$\omega_i \in \{0, 1\}$. The $q$-weighted binary digit sum of $k$ is
$s_q(k) = \sum_{i \ge 0} \omega_i q^{i+1}$, a finite sum because only finitely many $\omega_i$
are nonzero.

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Section 1 (definition of `s_q`). -/
def qWeightedDigitSum {R : Type*} [CommRing R] (q : R) (k : ℕ) : R :=
  ∑ i ∈ range (Nat.digits 2 k).length, ((Nat.digits 2 k).getD i 0 : R) * q ^ (i + 1)

/-- **Partial sums of the $q$-weighted binary digit sum.** For an element $q$ of a commutative
ring and a natural number $n$, the partial sum is $S_q(n) = \sum_{k=0}^{n-1} s_q(k)$, where $s_q$
is the $q$-weighted binary digit sum.

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Section 1 (definition of `S_q`). -/
def qWeightedDigitPartialSum {R : Type*} [CommRing R] (q : R) (n : ℕ) : R :=
  ∑ k ∈ range n, qWeightedDigitSum q k

/-- **The Takagi–Landsberg function.** For a real or complex parameter $a$ and a real number $x$,
let $\tau(y)$ denote the distance from a real number $y$ to the nearest integer. The
Takagi–Landsberg function is $\mathcal{T}_a(x) = \sum_{n \ge 0} a^n \tau(2^n x)$, where the
value is taken to be $0$ when the series does not converge absolutely. The series converges for
$|a| < 1$, and at dyadic rationals $x$ it is a finite sum.

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Section 1.1, equation (TakagiLandsberg). -/
noncomputable def takagiLandsberg {𝕜 : Type*} [RCLike 𝕜] (a : 𝕜) (x : ℝ) : 𝕜 :=
  ∑' n : ℕ, a ^ n * ((|2 ^ n * x - round (2 ^ n * x)| : ℝ) : 𝕜)

/-- **The $q$-weighted digit sum of zero.** For every element $q$ of a commutative ring, the
$q$-weighted binary digit sum of $0$ is $s_q(0) = 0$.

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Section 1. -/
theorem qWeightedDigitSum_zero {R : Type*} [CommRing R] (q : R) : qWeightedDigitSum q 0 = 0 := by
  simp [qWeightedDigitSum]

/-- **Binary recursion for the $q$-weighted digit sum.** Let $q$ be an element of a commutative
ring and let $k > 0$ be a natural number. Then the $q$-weighted binary digit sum satisfies
$s_q(k) = q\,(k \bmod 2) + q\,s_q(\lfloor k/2 \rfloor)$.

This gives the paper's relations $s_q(2j) = q\,s_q(j)$ for $j \ge 1$ and
$s_q(2j+1) = q\,s_q(j) + q$ for $j \ge 0$.

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, proof of Theorem 1, equations (s(2j)) and (s(2j+1)). -/
theorem qWeightedDigitSum_of_pos {R : Type*} [CommRing R] (q : R) {k : ℕ} (hk : 0 < k) :
    qWeightedDigitSum q k = q * ((k % 2 : ℕ) : R) + q * qWeightedDigitSum q (k / 2) := by
  unfold qWeightedDigitSum
  rw [Nat.digits_def' (by norm_num) hk, List.length_cons, sum_range_succ', mul_sum]
  simp only [List.getD_cons_succ, List.getD_cons_zero, zero_add, pow_one]
  rw [add_comm]
  congr 1
  · ring
  · refine sum_congr rfl fun i _ => ?_
    ring

/-- **The Takagi–Landsberg function vanishes at zero.** For every real or complex parameter $a$,
the Takagi–Landsberg function satisfies $\mathcal{T}_a(0) = 0$.

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Section 1.1. -/
theorem takagiLandsberg_zero {𝕜 : Type*} [RCLike 𝕜] (a : 𝕜) : takagiLandsberg a 0 = 0 := by
  simp [takagiLandsberg]

/-! ### The digit side -/

/-- The binary recursion of `qWeightedDigitSum`, including `k = 0`. -/
private theorem qWeightedDigitSum_eq {R : Type*} [CommRing R] (q : R) (k : ℕ) :
    qWeightedDigitSum q k = q * ((k % 2 : ℕ) : R) + q * qWeightedDigitSum q (k / 2) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [qWeightedDigitSum_zero]
  · exact qWeightedDigitSum_of_pos q hk

/-- Adding a power of two larger than `k` adds one weighted digit: for `k < 2^M`,
`s_q(2^M + k) = s_q(k) + q^(M+1)`. -/
private theorem qWeightedDigitSum_two_pow_add {R : Type*} [CommRing R] (q : R) (M : ℕ) :
    ∀ k < 2 ^ M, qWeightedDigitSum q (2 ^ M + k) = qWeightedDigitSum q k + q ^ (M + 1) := by
  induction M with
  | zero =>
    intro k hk
    obtain rfl : k = 0 := by simpa using hk
    rw [qWeightedDigitSum_eq q (2 ^ 0 + 0)]
    simp [qWeightedDigitSum_zero]
  | succ M ih =>
    intro k hk
    rw [show 2 ^ (M + 1) = 2 ^ M * 2 from pow_succ 2 M] at hk ⊢
    have h2 : (2 ^ M * 2 + k) % 2 = k % 2 := by omega
    have h3 : (2 ^ M * 2 + k) / 2 = 2 ^ M + k / 2 := by omega
    rw [qWeightedDigitSum_eq q (2 ^ M * 2 + k), h2, h3, ih (k / 2) (by omega),
      qWeightedDigitSum_eq q k]
    ring

/-- For `r ≤ 2^M`, `S_q(2^M + r) = S_q(2^M) + S_q(r) + r q^(M+1)`. -/
private theorem qWeightedDigitPartialSum_two_pow_add {R : Type*} [CommRing R] (q : R) (M r : ℕ)
    (hr : r ≤ 2 ^ M) :
    qWeightedDigitPartialSum q (2 ^ M + r) =
      qWeightedDigitPartialSum q (2 ^ M) + qWeightedDigitPartialSum q r + r * q ^ (M + 1) := by
  unfold qWeightedDigitPartialSum
  rw [sum_range_add, add_assoc]
  congr 1
  rw [sum_congr rfl fun x hx => qWeightedDigitSum_two_pow_add q M x
    (lt_of_lt_of_le (mem_range.mp hx) hr), sum_add_distrib, sum_const, card_range, nsmul_eq_mul]

/-- `S_q(2^(M+1)) = 2 S_q(2^M) + 2^M q^(M+1)`. -/
private theorem qWeightedDigitPartialSum_two_pow_succ {R : Type*} [CommRing R] (q : R) (M : ℕ) :
    qWeightedDigitPartialSum q (2 ^ (M + 1)) =
      2 * qWeightedDigitPartialSum q (2 ^ M) + 2 ^ M * q ^ (M + 1) := by
  rw [show 2 ^ (M + 1) = 2 ^ M + 2 ^ M by ring,
    qWeightedDigitPartialSum_two_pow_add q M (2 ^ M) le_rfl]
  push_cast
  ring

/-! ### The Takagi–Landsberg side -/

/-- `τ(x) = x` for `0 ≤ x ≤ 1/2`. -/
private theorem abs_sub_round_of_le_half {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    |x - round x| = x := by
  rcases h1.lt_or_eq with h1 | rfl
  · rw [round_eq_zero_iff.mpr ⟨by linarith, h1⟩]
    simp [abs_of_nonneg h0]
  · rw [show round (1 / 2 : ℝ) = 1 from round_eq_iff.mpr ⟨by norm_num, by norm_num⟩,
      abs_of_nonpos (by norm_num)]
    norm_num

/-- `τ(x) = 1 - x` for `1/2 ≤ x ≤ 1`. -/
private theorem abs_sub_round_of_half_le {x : ℝ} (h0 : 1 / 2 ≤ x) (h1 : x ≤ 1) :
    |x - round x| = 1 - x := by
  rw [show round x = 1 from round_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩,
    abs_of_nonpos (by push_cast; linarith)]
  push_cast
  ring

/-- At a dyadic rational `n / 2^M` the Takagi–Landsberg series stops after `M` terms. -/
private theorem takagiLandsberg_natCast_div_two_pow {𝕜 : Type*} [RCLike 𝕜] (a : 𝕜) (n M : ℕ) :
    takagiLandsberg a ((n : ℝ) / 2 ^ M) =
      ∑ k ∈ range M, a ^ k *
        ((|2 ^ k * ((n : ℝ) / 2 ^ M) - round (2 ^ k * ((n : ℝ) / 2 ^ M))| : ℝ) : 𝕜) := by
  unfold takagiLandsberg
  refine tsum_eq_sum fun k hk => ?_
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp (mem_range.not.mp hk))
  have h : (2 : ℝ) ^ (M + d) * ((n : ℝ) / 2 ^ M) = ((2 ^ d * n : ℕ) : ℝ) := by
    push_cast
    rw [pow_add]
    field_simp
  rw [h, round_natCast]
  simp

/-- The Takagi–Landsberg function has period `1`. -/
private theorem takagiLandsberg_add_one {𝕜 : Type*} [RCLike 𝕜] (a : 𝕜) (x : ℝ) :
    takagiLandsberg a (x + 1) = takagiLandsberg a x := by
  unfold takagiLandsberg
  congr 1
  ext k
  have h : (2 : ℝ) ^ k * (x + 1) = 2 ^ k * x + ((2 ^ k : ℕ) : ℝ) := by
    push_cast
    ring
  rw [h, round_add_natCast]
  congr 3
  push_cast
  ring

/-- The de Rham recursion at dyadic rationals:
`𝒯_a(n / 2^(M+1)) = a 𝒯_a(n / 2^M) + τ(n / 2^(M+1))`. -/
private theorem takagiLandsberg_natCast_div_two_pow_succ {𝕜 : Type*} [RCLike 𝕜] (a : 𝕜)
    (n M : ℕ) :
    takagiLandsberg a ((n : ℝ) / 2 ^ (M + 1)) =
      a * takagiLandsberg a ((n : ℝ) / 2 ^ M) +
        ((|(n : ℝ) / 2 ^ (M + 1) - round ((n : ℝ) / 2 ^ (M + 1))| : ℝ) : 𝕜) := by
  rw [takagiLandsberg_natCast_div_two_pow, takagiLandsberg_natCast_div_two_pow, sum_range_succ',
    mul_sum]
  congr 1
  · refine sum_congr rfl fun k _ => ?_
    have h : (2 : ℝ) ^ (k + 1) * ((n : ℝ) / 2 ^ (M + 1)) = 2 ^ k * ((n : ℝ) / 2 ^ M) := by
      rw [pow_succ, pow_succ]
      field_simp
    rw [h, pow_succ]
    ring
  · simp

/-! ### The fluctuation identity -/

/-- For `n ≤ 2^M`, `S_q(n) = (n / 2^M) S_q(2^M) - (2q)^M 𝒯_a(n / 2^M) / 2` with
`a = 1/(2q)`. -/
private theorem qWeightedDigitPartialSum_eq_of_le_two_pow {𝕜 : Type*} [RCLike 𝕜]
    (q : 𝕜) (hq : q ≠ 0) (M : ℕ) :
    ∀ n ≤ 2 ^ M, qWeightedDigitPartialSum q n =
      (n : 𝕜) / 2 ^ M * qWeightedDigitPartialSum q (2 ^ M) -
        (2 * q) ^ M * takagiLandsberg (1 / (2 * q)) ((n : ℝ) / 2 ^ M) / 2 := by
  induction M with
  | zero =>
    intro n hn
    have hS : ∀ m ≤ 1, qWeightedDigitPartialSum q m = 0 := by
      intro m hm
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm with rfl | rfl <;>
        simp [qWeightedDigitPartialSum, qWeightedDigitSum_zero]
    rw [takagiLandsberg_natCast_div_two_pow]
    simp [hS n hn, hS 1 le_rfl]
  | succ M ih =>
    intro n hn
    rw [qWeightedDigitPartialSum_two_pow_succ, takagiLandsberg_natCast_div_two_pow_succ]
    rcases le_or_gt n (2 ^ M) with hle | hgt
    · -- `0 ≤ n / 2^(M+1) ≤ 1/2`
      have hτ : |(n : ℝ) / 2 ^ (M + 1) - round ((n : ℝ) / 2 ^ (M + 1))| =
          (n : ℝ) / 2 ^ (M + 1) := by
        have hle' : (n : ℝ) ≤ 2 ^ M := by exact_mod_cast hle
        refine abs_sub_round_of_le_half (by positivity) ?_
        rw [div_le_iff₀ (by positivity), pow_succ]
        linarith
      rw [hτ, ih n hle]
      push_cast [RCLike.ofReal_div, RCLike.ofReal_pow, RCLike.ofReal_natCast,
        RCLike.ofReal_ofNat]
      field_simp
      ring
    · -- `n = 2^M + r` with `r ≤ 2^M`, so `1/2 ≤ n / 2^(M+1) ≤ 1`
      obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hgt.le
      have hr : r ≤ 2 ^ M := by
        rw [pow_succ] at hn
        omega
      have hr' : (r : ℝ) ≤ 2 ^ M := by exact_mod_cast hr
      have hτ : |((2 ^ M + r : ℕ) : ℝ) / 2 ^ (M + 1) -
            round (((2 ^ M + r : ℕ) : ℝ) / 2 ^ (M + 1))| =
          1 - ((2 ^ M + r : ℕ) : ℝ) / 2 ^ (M + 1) := by
        refine abs_sub_round_of_half_le ?_ ?_
        · rw [le_div_iff₀ (by positivity), pow_succ]
          push_cast
          linarith [(r.cast_nonneg : (0 : ℝ) ≤ r)]
        · rw [div_le_iff₀ (by positivity), pow_succ]
          push_cast
          linarith
      have hT : takagiLandsberg (1 / (2 * q)) (((2 ^ M + r : ℕ) : ℝ) / 2 ^ M) =
          takagiLandsberg (1 / (2 * q)) ((r : ℝ) / 2 ^ M) := by
        rw [← takagiLandsberg_add_one (1 / (2 * q)) ((r : ℝ) / 2 ^ M)]
        congr 1
        push_cast
        rw [add_div, div_self (by positivity)]
        ring
      rw [hτ, hT, qWeightedDigitPartialSum_two_pow_add q M r hr, ih r hr]
      push_cast [RCLike.ofReal_sub, RCLike.ofReal_div, RCLike.ofReal_pow,
        RCLike.ofReal_natCast, RCLike.ofReal_ofNat]
      field_simp
      ring

/-- **Dyadic values of the normalized $q$-weighted fluctuation.** Let $q$ be a complex number
with $|q| > 1/2$, let $N > 0$ be a natural number, and let $j \le 2^{N-1}$ be a natural number.
Put $t_j = j / 2^{N-1}$ and $a = 1/(2q)$. Then
$$\frac{S_q(2j) - t_j\,S_q(2^N)}{(2q)^{N-1}} = -q\,\mathcal{T}_a(t_j),$$
where $S_q$ is the partial sum of the $q$-weighted binary digit sum and $\mathcal{T}_a$ is the
Takagi–Landsberg function. With $l = 2^N$ we have $t_j l = 2j$, so the numerator is the
fluctuation $S_q(t_j l) - t_j\,S_q(l)$ at the grid point $t_j$ of $[0, 1]$.

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Proposition 1 (`integers-2026-A61-prop-1`). -/
public theorem qWeightedDigitPartialSum_dyadic_fluctuation (q : ℂ) (hq : 1 / 2 < ‖q‖)
    (N : ℕ) (hN : 0 < N) (j : ℕ) (hj : j ≤ 2 ^ (N - 1)) :
    (qWeightedDigitPartialSum q (2 * j) -
        ((j : ℂ) / 2 ^ (N - 1)) * qWeightedDigitPartialSum q (2 ^ N)) / (2 * q) ^ (N - 1) =
      -q * takagiLandsberg (1 / (2 * q)) ((j : ℝ) / 2 ^ (N - 1)) := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    norm_num at hq
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hj ⊢
  have key := qWeightedDigitPartialSum_eq_of_le_two_pow q hq0 (M + 1) (2 * j)
    (by rw [pow_succ]; omega)
  have hx : ((2 * j : ℕ) : ℝ) / 2 ^ (M + 1) = (j : ℝ) / 2 ^ M := by
    push_cast
    rw [pow_succ]
    field_simp
  rw [hx] at key
  rw [key]
  push_cast
  field_simp
  ring

namespace qWeighted_trollopeDelange

/-- The partial sum at a power of two is a scaled geometric sum. -/
private theorem partialSum_two_pow (q : ℝ) (hq : q ≠ 1) (m : ℕ) :
    qWeightedDigitPartialSum q (2 ^ m) = 2 ^ m * (q / 2 * ((1 - q ^ m) / (1 - q))) := by
  induction m with
  | zero => simp [qWeightedDigitPartialSum, qWeightedDigitSum_zero]
  | succ m ih =>
    rw [qWeightedDigitPartialSum_two_pow_succ, ih, pow_succ (2 : ℝ), pow_succ q]
    field_simp [sub_ne_zero.mpr hq.symm]
    ring

end qWeighted_trollopeDelange

/-- **The $q$-weighted Trollope–Delange formula.** Let $q$ be a real number with $|q| > 1/2$ and
$q \ne 1$, and put $a = 1/(2q)$. For a positive integer $n$, let $k = \lfloor \log_2 n \rfloor$
and let $u = \log_2 n - k$ be the fractional part of $\log_2 n$. Write
$F(u) = 2^{1-u}\,\mathcal{T}_a(2^{u-1})$. Then
$$\frac{S_q(n)}{n} = \frac{q}{2}\left(\frac{1 - q^{k+1}}{1 - q} - q^k F(u)\right),$$
where $S_q$ is the partial sum of the $q$-weighted binary digit sum and $\mathcal{T}_a$ is the
Takagi–Landsberg function.

Source: Aleksei Minabutdinov, *A q-Weighted Analogue of the Trollope-Delange Formula*,
INTEGERS 26 (2026), Article A61, Theorem 1 (`integers-2026-A61-thm-1`). -/
public theorem qWeighted_trollopeDelange (q : ℝ) (hq : 1 / 2 < |q|) (hq1 : q ≠ 1)
    (n : ℕ) (hn : 0 < n) :
    qWeightedDigitPartialSum q n / n =
      q / 2 * ((1 - q ^ (Nat.log 2 n + 1)) / (1 - q) -
        q ^ Nat.log 2 n *
          ((2 : ℝ) ^ (1 - Int.fract (Real.logb 2 n)) *
            takagiLandsberg (1 / (2 * q)) ((2 : ℝ) ^ (-(1 - Int.fract (Real.logb 2 n)))))) := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    norm_num at hq
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set k := Nat.log 2 n
  have hbound : n ≤ 2 ^ (k + 1) := (Nat.lt_pow_succ_log_self (by decide) n).le
  have hfloor : (⌊Real.logb 2 n⌋ : ℝ) = (k : ℝ) := by
    have hlog : 0 ≤ Real.logb 2 n :=
      Real.logb_nonneg (by norm_num) (by exact_mod_cast Nat.one_le_of_lt hn)
    rw [← Int.natCast_floor_eq_floor hlog, Int.cast_natCast]
    exact congrArg (fun m : ℕ => (m : ℝ)) (Real.natFloor_logb_natCast 2 n)
  have harg : (2 : ℝ) ^ (-(1 - Int.fract (Real.logb 2 n))) = (n : ℝ) / 2 ^ (k + 1) := by
    rw [Int.fract, hfloor,
      show -(1 - (Real.logb 2 n - k)) = Real.logb 2 n - (↑(k + 1 : ℕ) : ℝ) by
        push_cast
        ring,
      Real.rpow_sub_natCast two_ne_zero, Real.rpow_logb (by norm_num) (by norm_num) hn']
  have hscale : (2 : ℝ) ^ (1 - Int.fract (Real.logb 2 n)) = 2 ^ (k + 1) / (n : ℝ) := by
    rw [← neg_neg (1 - Int.fract (Real.logb 2 n)), Real.rpow_neg (by norm_num), harg, inv_div]
  rw [harg, hscale, qWeightedDigitPartialSum_eq_of_le_two_pow q hq0 (k + 1) n hbound,
    qWeighted_trollopeDelange.partialSum_two_pow q hq1, mul_pow, pow_succ q k]
  field_simp [hn'.ne', sub_ne_zero.mpr hq1.symm]

end

end MetaMathlibExt
