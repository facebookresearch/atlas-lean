/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

namespace MetaMathlibExt

@[expose] public section

open Real Filter Topology

/-- The area `∫₀^π |cos^n x - cos^n (k x)| dx` between `cos^n x` and
`cos^n (k x)` on `[0, π]`; the paper's `A_n` is its limit as `k → ∞`
(Eq. (1)), with `k` running over the natural numbers.

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Eq. (1). -/
public noncomputable def cosPowArea (n k : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..π, |cos x ^ n - cos (k * x) ^ n|

/-- For `n = 0` the two curves coincide, so the area is `0`.

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Eq. (1). -/
public theorem cosPowArea_zero_left (k : ℕ) : cosPowArea 0 k = 0 := by
  simp [cosPowArea]

/-- For `k = 1` the two curves coincide, so the area is `0`.

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Eq. (1). -/
public theorem cosPowArea_one_right (n : ℕ) : cosPowArea n 1 = 0 := by
  simp [cosPowArea]

/-- Theorem 1: for `n` odd,
`A_n = 8 / (2^(n-1) π) · ∑_{j=0}^{(n-1)/2} C(n, j) / (n - 2j)²`.

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Theorem 1
(`jis-2025-25.2.3-thm-1`). -/
public theorem_wanted tendsto_cosPowArea_of_odd {n : ℕ} (hn : Odd n) :
    Tendsto (fun k => cosPowArea n k) atTop
      (𝓝 (8 / (2 ^ (n - 1) * π) *
        ∑ j ∈ Finset.range ((n - 1) / 2 + 1), (n.choose j : ℝ) / ((n : ℝ) - 2 * j) ^ 2))

/-- Theorem 2: for `n ≡ 2 (mod 4)`,
`A_n = 16 / (2^n π) · ∑_{j=0}^{(n-2)/4} C(n, 2j) / (n/2 - 2j)²`, and for
`n ≡ 0 (mod 4)`,
`A_n = 16 / (2^n π) · ∑_{j=0}^{(n-4)/4} C(n, 2j+1) / (n/2 - (2j+1))²`.
(At `n = 0` both sides are `0`, so no positivity hypothesis is needed.)

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Theorem 2
(`jis-2025-25.2.3-thm-2`). -/
public theorem_wanted tendsto_cosPowArea_of_even (n : ℕ) :
    (n % 4 = 2 → Tendsto (fun k => cosPowArea n k) atTop
      (𝓝 (16 / (2 ^ n * π) * ∑ j ∈ Finset.range ((n - 2) / 4 + 1),
        (n.choose (2 * j) : ℝ) / ((n : ℝ) / 2 - 2 * j) ^ 2))) ∧
    (n % 4 = 0 → Tendsto (fun k => cosPowArea n k) atTop
      (𝓝 (16 / (2 ^ n * π) * ∑ j ∈ Finset.range ((n - 4) / 4 + 1),
        (n.choose (2 * j + 1) : ℝ) / ((n : ℝ) / 2 - (2 * j + 1)) ^ 2)))

/-- Theorem 3: for `n ≥ 3` the limits `A_n` and `A_{n-2}` exist and
`A_n = (n - 1)/n · A_{n-2} + 8/(n² π)` for `n` odd, `+ 16/(n² π)` for `n` even.

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Theorem 3
(`jis-2025-25.2.3-thm-3`). -/
public theorem_wanted cosPowArea_limit_recursion {n : ℕ} (hn : 3 ≤ n) :
    ∃ L L' : ℝ, Tendsto (fun k => cosPowArea n k) atTop (𝓝 L) ∧
      Tendsto (fun k => cosPowArea (n - 2) k) atTop (𝓝 L') ∧
      L = ((n : ℝ) - 1) / n * L' + (if Odd n then 8 else 16) / ((n : ℝ) ^ 2 * π)

/-- Theorem 4, double-factorial formulas: for `n` odd,
`A_n = 8/π · n!/(n!!)² · ∑_{j=0}^{(n-1)/2} (2j-1)!!/(2j)!! · 1/(2j+1)`, and for
`n ≥ 2` even,
`A_n = 16/π · n!/(n!!)² · ∑_{j=0}^{(n-2)/2} (2j)!!/(2j+1)!! · 1/(2j+2)`
(with `(-1)!! = 1`, which `Nat.doubleFactorial (2 * 0 - 1) = 0‼ = 1` matches).

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Theorem 4
(`jis-2025-25.2.3-thm-4`). -/
public theorem_wanted tendsto_cosPowArea_doubleFactorial (n : ℕ) :
    (Odd n → Tendsto (fun k => cosPowArea n k) atTop
      (𝓝 (8 / π * ((n.factorial : ℝ) / (n.doubleFactorial : ℝ) ^ 2) *
        ∑ j ∈ Finset.range ((n - 1) / 2 + 1),
          ((2 * j - 1).doubleFactorial : ℝ) /
            ((2 * j).doubleFactorial * (2 * j + 1))))) ∧
    (Even n → 0 < n → Tendsto (fun k => cosPowArea n k) atTop
      (𝓝 (16 / π * ((n.factorial : ℝ) / (n.doubleFactorial : ℝ) ^ 2) *
        ∑ j ∈ Finset.range ((n - 2) / 2 + 1),
          ((2 * j).doubleFactorial : ℝ) /
            ((2 * j + 1).doubleFactorial * (2 * j + 2)))))

/-- Theorem 4, OEIS link: for `n` odd, `n! ∑_{j=0}^{(n-1)/2} (2j-1)!!/(2j)!! ·
1/(2j+1)` is the `n`th term of the exponential generating function of
`arcsin x / (1 - x)` (OEIS A296726), and for `n ≥ 2` even,
`n! ∑_{j=0}^{(n-2)/2} (2j)!!/(2j+1)!! · 1/(2j+2)` is the `n`th term of the
exponential generating function of `arcsin² x / (2 (1 - x))` (OEIS A372324).
EGF terms are stated as `n`th derivatives at `0`.

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Theorem 4
(`jis-2025-25.2.3-thm-4`). -/
public theorem_wanted iteratedDeriv_arcsin_div_one_sub_doubleFactorial (n : ℕ) :
    (Odd n → iteratedDeriv n (fun x => arcsin x / (1 - x)) 0 =
      n.factorial * ∑ j ∈ Finset.range ((n - 1) / 2 + 1),
        ((2 * j - 1).doubleFactorial : ℝ) / ((2 * j).doubleFactorial * (2 * j + 1))) ∧
    (Even n → 0 < n → iteratedDeriv n (fun x => arcsin x ^ 2 / (2 * (1 - x))) 0 =
      n.factorial * ∑ j ∈ Finset.range ((n - 2) / 2 + 1),
        ((2 * j).doubleFactorial : ℝ) / ((2 * j + 1).doubleFactorial * (2 * j + 2)))

/-- Lemma 5: for `N` even and positive,
`∑_{ℓ=1}^{N/2} sin(2π q ℓ / N)` is `0` for `q` even and `cot(q π / N)` for `q`
odd. The paper's positivity of `q` is dropped (`q = 0` holds trivially).

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Lemma 5
(`jis-2025-25.2.3-lem-5`). -/
public theorem_wanted sum_sin_two_pi_mul_div_of_even {N : ℕ} (hN : 0 < N) (hNe : Even N)
    (q : ℕ) :
    ∑ l ∈ Finset.Icc 1 (N / 2), sin (q * l * 2 * π / N) =
      if Even q then 0 else cot (q * π / N)

/-- Lemma 6: for `N` odd,
`∑_{ℓ=1}^{(N-1)/2} sin(2π q ℓ / N)` is `-(1/2) tan(q π / (2N))` for `q` even and
`(1/2) cot(q π / (2N))` for `q` odd. The paper's positivity of `q` is dropped
(`q = 0` holds trivially).

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Lemma 6
(`jis-2025-25.2.3-lem-6`). -/
public theorem_wanted sum_sin_two_pi_mul_div_of_odd {N : ℕ} (hN : Odd N) (q : ℕ) :
    ∑ l ∈ Finset.Icc 1 ((N - 1) / 2), sin (q * l * 2 * π / N) =
      if Even q then -(1 / 2) * tan (q * π / (2 * N)) else 1 / 2 * cot (q * π / (2 * N))

/-- Lemma 7: for `N` positive and even and `q` even,
`∑_{ℓ=1}^{N/2} sin(q ℓ π / N)` is `0` for `q ≡ 0 (mod 4)` and `cot(q π / (2N))`
for `q ≡ 2 (mod 4)`. The paper's positivity of `q` is dropped.

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Lemma 7
(`jis-2025-25.2.3-lem-7`). -/
public theorem_wanted sum_sin_pi_mul_div_of_even_of_even {N q : ℕ} (hN : 0 < N)
    (hNe : Even N) (hq : Even q) :
    ∑ l ∈ Finset.Icc 1 (N / 2), sin (q * l * π / N) =
      if q % 4 = 0 then 0 else cot (q * π / (2 * N))

/-- Lemma 8: for every real `x ≠ 0`,
`(1/k - 1) cot(x/(k-1)) + (1/k + 1) cot(x/(k+1)) → 4/x` as `k → ∞`. The
hypothesis `x ≠ 0` is added: the paper says "any real number", but at `x = 0`
the cotangents and `4/x` are undefined.

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Lemma 8
(`jis-2025-25.2.3-lem-8`). -/
public theorem_wanted tendsto_cot_div_pred_add_cot_div_succ {x : ℝ} (hx : x ≠ 0) :
    Tendsto (fun k : ℕ => (1 / (k : ℝ) - 1) * cot (x / (k - 1)) +
      (1 / (k : ℝ) + 1) * cot (x / (k + 1))) atTop (𝓝 (4 / x))

/-- Lemma 9: for `q` odd, with `k = 2m + 1` odd tending to infinity,
`∑_{ℓ=1}^{(k-1)/2} ∫_{2πℓ/(k+1)}^{2πℓ/(k-1)} (cos qkx - cos qx) dx → 4/(q² π)`.

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Lemma 9
(`jis-2025-25.2.3-lem-9`). -/
public theorem_wanted tendsto_sum_integral_cos_sub_cos_odd_odd {q : ℕ} (hq : Odd q) :
    Tendsto (fun m : ℕ => ∑ l ∈ Finset.Icc 1 m,
      ∫ x in (2 * π * l / ((2 * m + 1 : ℝ) + 1))..(2 * π * l / ((2 * m + 1 : ℝ) - 1)),
        (cos (q * (2 * m + 1 : ℝ) * x) - cos (q * x))) atTop
      (𝓝 (4 / ((q : ℝ) ^ 2 * π)))

/-- Lemma 10: for `q` even, with `k = 2m + 1` odd tending to infinity and
`f(x) = cos qx - cos qkx`,
`∑_{ℓ=1}^{(k-1)/2} (∫_{(ℓ-1)π/(k-1)}^{ℓπ/(k+1)} f - ∫_{ℓπ/(k+1)}^{ℓπ/(k-1)} f)`
tends to `0` if `q ≡ 0 (mod 4)` and to `16/(q² π)` if `q ≡ 2 (mod 4)`.

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Lemma 10
(`jis-2025-25.2.3-lem-10`). -/
public theorem_wanted tendsto_sum_integral_cos_sub_cos_odd_even {q : ℕ} (hq : Even q) :
    Tendsto (fun m : ℕ => ∑ l ∈ Finset.Icc 1 m,
      ((∫ x in (((l : ℝ) - 1) * π / ((2 * m + 1 : ℝ) - 1))..((l : ℝ) * π / ((2 * m + 1 : ℝ) + 1)),
          (cos (q * x) - cos (q * (2 * m + 1 : ℝ) * x))) -
        ∫ x in ((l : ℝ) * π / ((2 * m + 1 : ℝ) + 1))..((l : ℝ) * π / ((2 * m + 1 : ℝ) - 1)),
          (cos (q * x) - cos (q * (2 * m + 1 : ℝ) * x)))) atTop
      (𝓝 (if q % 4 = 0 then 0 else 16 / ((q : ℝ) ^ 2 * π)))

/-- Lemma 11: for `q` odd, with `k = 2m` even tending to infinity and
`f(x) = cos qx - cos qkx`,
`∑_{ℓ=1}^{k/2} (∫_{(ℓ-1)2π/(k-1)}^{ℓ2π/(k+1)} f - ∫_{ℓ2π/(k+1)}^{ℓ2π/(k-1)} f)
→ 8/(q² π)`.

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Lemma 11
(`jis-2025-25.2.3-lem-11`). -/
public theorem_wanted tendsto_sum_integral_cos_sub_cos_even_odd {q : ℕ} (hq : Odd q) :
    Tendsto (fun m : ℕ => ∑ l ∈ Finset.Icc 1 m,
      ((∫ x in (((l : ℝ) - 1) * 2 * π / ((2 * m : ℝ) - 1))..((l : ℝ) * 2 * π / ((2 * m : ℝ) + 1)),
          (cos (q * x) - cos (q * (2 * m : ℝ) * x))) -
        ∫ x in ((l : ℝ) * 2 * π / ((2 * m : ℝ) + 1))..((l : ℝ) * 2 * π / ((2 * m : ℝ) - 1)),
          (cos (q * x) - cos (q * (2 * m : ℝ) * x)))) atTop
      (𝓝 (8 / ((q : ℝ) ^ 2 * π)))

/-- Lemma 12: for `q` even, with `k = 2m` even tending to infinity and
`f(x) = cos qx - cos qkx`,
`∑_{ℓ=1}^{k/2} (∫_{(ℓ-1)π/(k-1)}^{ℓπ/(k+1)} f - ∫_{ℓπ/(k+1)}^{ℓπ/(k-1)} f)`
tends to `0` if `q ≡ 0 (mod 4)` and to `16/(q² π)` if `q ≡ 2 (mod 4)`.

Source: Muhammad Adam Dombrowski and Gregory Dresden, *Areas Between Cosines*,
Journal of Integer Sequences 28 (2025), Article 25.2.3, Lemma 12
(`jis-2025-25.2.3-lem-12`). -/
public theorem_wanted tendsto_sum_integral_cos_sub_cos_even_even {q : ℕ} (hq : Even q) :
    Tendsto (fun m : ℕ => ∑ l ∈ Finset.Icc 1 m,
      ((∫ x in (((l : ℝ) - 1) * π / ((2 * m : ℝ) - 1))..((l : ℝ) * π / ((2 * m : ℝ) + 1)),
          (cos (q * x) - cos (q * (2 * m : ℝ) * x))) -
        ∫ x in ((l : ℝ) * π / ((2 * m : ℝ) + 1))..((l : ℝ) * π / ((2 * m : ℝ) - 1)),
          (cos (q * x) - cos (q * (2 * m : ℝ) * x)))) atTop
      (𝓝 (if q % 4 = 0 then 0 else 16 / ((q : ℝ) ^ 2 * π)))

end

end MetaMathlibExt
