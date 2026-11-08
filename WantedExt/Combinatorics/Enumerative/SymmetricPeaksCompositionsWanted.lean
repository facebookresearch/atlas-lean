/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Distributions.Geometric
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Heights of symmetric peaks and depths of symmetric valleys over compositions

Statements from Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the
Depths of Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026),
Article A65.

In a word `w₁ w₂ ⋯` of positive integers, a *symmetric peak* is a factor `a b a` with
`b > a`, of height `b - a`, and a *symmetric valley* is a factor `a b a` with `b < a`, of
depth `a - b`. These are the readings fixed by the paper's worked examples (the five
compositions of `5` and the fourteen compositions of `8` listed after Corollaries 1 and 2)
and by its Maple coefficient lists; the extracted text does not display the definitions.
`hsp(n)` (`dsv(n)`) sums the heights (depths) over all compositions of `n`, and
`hsp(n, k)` (`dsv(n, k)`) over those with exactly `k` parts.

The paper's geometric variables take values in `{1, 2, …}`; Mathlib's
`ProbabilityTheory.geometricMeasure` lives on `{0, 1, …}`. The shift does not change any
of the four statistics.

The trivariate generating functions of Theorems 1 and 3 are stated coefficientwise as
multivariate power series; Theorem 3 uses the corrected reading recorded in its docstring
and audit row.

Not stated (see the source audit table): the bivariate part of Lemma 2 (false as
extracted), Theorem 2(b) (false as extracted) and the variances of Theorem 6 (false as printed in the journal).
-/

open MeasureTheory ProbabilityTheory PowerSeries

namespace MetaMathlibExt

@[expose] public section

/-- The number of symmetric peaks `a b a` (`b > a`) in a word.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Section 1 (symmetric peaks). -/
def symmetricPeakCount : List ℕ → ℕ
  | a :: b :: c :: t => (if a = c ∧ a < b then 1 else 0) + symmetricPeakCount (b :: c :: t)
  | _ => 0

/-- The sum of the heights `b - a` of the symmetric peaks `a b a` (`b > a`) of a word.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Section 1 (heights of symmetric peaks). -/
def symmetricPeakHeightSum : List ℕ → ℕ
  | a :: b :: c :: t =>
      (if a = c ∧ a < b then b - a else 0) + symmetricPeakHeightSum (b :: c :: t)
  | _ => 0

/-- The number of symmetric valleys `a b a` (`b < a`) in a word.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Section 1 (symmetric valleys). -/
def symmetricValleyCount : List ℕ → ℕ
  | a :: b :: c :: t => (if a = c ∧ b < a then 1 else 0) + symmetricValleyCount (b :: c :: t)
  | _ => 0

/-- The sum of the depths `a - b` of the symmetric valleys `a b a` (`b < a`) of a word.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Section 1 (depths of symmetric valleys). -/
def symmetricValleyDepthSum : List ℕ → ℕ
  | a :: b :: c :: t =>
      (if a = c ∧ b < a then a - b else 0) + symmetricValleyDepthSum (b :: c :: t)
  | _ => 0

/-- The paper's examples for `n = 5`: `131`, `1211` and `1121` have symmetric peak
heights `2`, `1`, `1`, and `11111` has none.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
example after Corollary 1. -/
theorem symmetricPeakHeightSum_examples :
    symmetricPeakHeightSum [1, 3, 1] = 2 ∧ symmetricPeakHeightSum [1, 2, 1, 1] = 1 ∧
      symmetricPeakHeightSum [1, 1, 2, 1] = 1 ∧ symmetricPeakHeightSum [1, 1, 1, 1, 1] = 0 ∧
      symmetricPeakCount [1, 3, 1] = 1 := by
  decide

/-- Examples from the paper's list for `n = 8`: `21212` has two symmetric valleys of depth
`1`, `3131` one of depth `2`, and `323` one of depth `1`.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
example after Corollary 2. -/
theorem symmetricValleyDepthSum_examples :
    symmetricValleyDepthSum [2, 1, 2, 1, 2] = 2 ∧ symmetricValleyCount [2, 1, 2, 1, 2] = 2 ∧
      symmetricValleyDepthSum [3, 1, 3, 1] = 2 ∧ symmetricValleyDepthSum [3, 2, 3] = 1 := by
  decide

/-- Generating function of `hsp(n)`: `∑ hsp(n) xⁿ = x⁴ / ((1 - 2x)² (1 - x³))`, stated
after clearing denominators.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Lemma 1, (5) (`integers-2026-A65-lem-1`). -/
public theorem_wanted symmetricPeakHeightSum_compositions_genFun :
    PowerSeries.mk (fun n => ((∑ c : Composition n, symmetricPeakHeightSum c.blocks : ℕ) : ℤ)) *
        ((1 - 2 * X) ^ 2 * (1 - X ^ 3)) = X ^ 4

/-- Bivariate generating function of `hsp(n, k)` (`k` = number of parts):
`∑ hsp(n, k) xⁿ yᵏ = y³ x⁴ / ((1 - x³)(1 - x - yx)²)`, stated in `ℤ[y]⟦x⟧` after
clearing denominators.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Lemma 1 (`integers-2026-A65-lem-1`). -/
public theorem_wanted symmetricPeakHeightSum_compositions_bivariate_genFun :
    PowerSeries.mk (fun n => ∑ c : Composition n,
        Polynomial.C ((symmetricPeakHeightSum c.blocks : ℕ) : ℤ) * Polynomial.X ^ c.length) *
        ((1 - X ^ 3) * (1 - X - PowerSeries.C (Polynomial.X : Polynomial ℤ) * X) ^ 2) =
      PowerSeries.C (Polynomial.X ^ 3 : Polynomial ℤ) * X ^ 4

/-- Generating function of `dsv(n)`:
`∑ dsv(n) xⁿ = (x⁵ - 2x⁶ + x⁷) / ((1 - 2x)² (1 - x³)(1 - x²)²)`, stated after clearing
denominators.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Lemma 2, (11) (`integers-2026-A65-lem-2`). -/
public theorem_wanted symmetricValleyDepthSum_compositions_genFun :
    PowerSeries.mk (fun n => ((∑ c : Composition n, symmetricValleyDepthSum c.blocks : ℕ) : ℤ)) *
        ((1 - 2 * X) ^ 2 * (1 - X ^ 3) * (1 - X ^ 2) ^ 2) = X ^ 5 - 2 * X ^ 6 + X ^ 7

/-- Closed form of `hsp(n)`, with `ω± = 1 ± i√3`:
`hsp(n) = 2^{n-1} (7n - 24) / 49 + (-33 - 15i√3)(-2)ⁿ / (441 ω₊^{n+1})
+ (-33 + 15i√3)(-2)ⁿ / (441 ω₋^{n+1}) + 1/3` for all `n ≥ 0` (`2^{n-1}` written `2ⁿ / 2`).

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Corollary 1, (6) (`integers-2026-A65-cor-1`). -/
public theorem_wanted symmetricPeakHeightSum_compositions_closed_form (n : ℕ) :
    ((∑ c : Composition n, symmetricPeakHeightSum c.blocks : ℕ) : ℂ) =
      (2 : ℂ) ^ n / 2 * (7 * n - 24) / 49 +
        (-33 - 15 * Complex.I * (Real.sqrt 3 : ℂ)) * (-2) ^ n /
          (441 * (1 + Complex.I * (Real.sqrt 3 : ℂ)) ^ (n + 1)) +
        (-33 + 15 * Complex.I * (Real.sqrt 3 : ℂ)) * (-2) ^ n /
          (441 * (1 - Complex.I * (Real.sqrt 3 : ℂ)) ^ (n + 1)) + 1 / 3

/-- Closed form of `dsv(n)`, with `ω± = 1 ± i√3`:
`dsv(n) = (-6n + 7)(-1)ⁿ / 108 + 2ⁿ (21n - 79) / 1323
+ (-33 - 15√3 i)(-2)ⁿ / (441 ω₊^{n+1}) + (-33 + 15√3 i)(-2)ⁿ / (441 ω₋^{n+1}) + 1/12`
for all `n ≥ 0`.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Corollary 2, (12) (`integers-2026-A65-cor-2`). -/
public theorem_wanted symmetricValleyDepthSum_compositions_closed_form (n : ℕ) :
    ((∑ c : Composition n, symmetricValleyDepthSum c.blocks : ℕ) : ℂ) =
      (-6 * n + 7) / 108 * (-1) ^ n + (2 : ℂ) ^ n * (21 * n - 79) / 1323 +
        (-33 - 15 * (Real.sqrt 3 : ℂ) * Complex.I) * (-2) ^ n /
          (441 * (1 + Complex.I * (Real.sqrt 3 : ℂ)) ^ (n + 1)) +
        (-33 + 15 * (Real.sqrt 3 : ℂ) * Complex.I) * (-2) ^ n /
          (441 * (1 - Complex.I * (Real.sqrt 3 : ℂ)) ^ (n + 1)) + 1 / 12

/-- For `k > 3`,
`hsp(n, k) = (k - 2) ∑_{m=2}^{n-k+1} ∑_{b=1}^{min(m-1, t)} C(n - 2b - m - 1, k - 4) (m - b)`
with `t = ⌊(n - m - k + 3) / 2⌋`.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Theorem 2(a) (`integers-2026-A65-thm-2`). -/
public theorem_wanted symmetricPeakHeightSum_compositions_length (n k : ℕ) (hk : 3 < k) :
    ∑ c ∈ Finset.univ.filter (fun c : Composition n => c.length = k),
        symmetricPeakHeightSum c.blocks =
      (k - 2) * ∑ m ∈ Finset.Icc 2 (n - k + 1),
        ∑ b ∈ Finset.Icc 1 (min (m - 1) ((n - m - k + 3) / 2)),
          (n - 2 * b - m - 1).choose (k - 4) * (m - b)

/-- For `k > 3`,
`dsv(n, k) = (k - 2) ∑_{m=1}^{⌊(n-k+1)/3⌋} ∑_{b=m+1}^{⌊(n-m-(k-3))/2⌋} C(n - 2b - m - 1, k - 4) (b - m)`.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Theorem 4(a) (`integers-2026-A65-thm-4`). -/
public theorem_wanted symmetricValleyDepthSum_compositions_length (n k : ℕ) (hk : 3 < k) :
    ∑ c ∈ Finset.univ.filter (fun c : Composition n => c.length = k),
        symmetricValleyDepthSum c.blocks =
      (k - 2) * ∑ m ∈ Finset.Icc 1 ((n - k + 1) / 3),
        ∑ b ∈ Finset.Icc (m + 1) ((n - m - (k - 3)) / 2),
          (n - 2 * b - m - 1).choose (k - 4) * (b - m)

/-- `dsv(n, 3) = ∑_{m=1}^{⌊(n-2)/3⌋} d_m` with `d_m = (n - 3m) / 2` if `n - m` is even and
`d_m = 0` otherwise.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Theorem 4(b) (`integers-2026-A65-thm-4`). -/
public theorem_wanted symmetricValleyDepthSum_compositions_length_three (n : ℕ) :
    ∑ c ∈ Finset.univ.filter (fun c : Composition n => c.length = 3),
        symmetricValleyDepthSum c.blocks =
      ∑ m ∈ Finset.Icc 1 ((n - 2) / 3), if Even (n - m) then (n - 3 * m) / 2 else 0

/-- Expected values over `n ≥ 2` independent geometric variables with parameter
`p ∈ (0, 1)`, `q = 1 - p`: the number of symmetric peaks has mean `p² q (n - 2) / (1 - q³)`,
the number of symmetric valleys `p² (1/(1 - q²) - 1/(1 - q³)) (n - 2)`, the sum of peak
heights `p q (n - 2) / (1 - q³)`, and the sum of valley depths
`q (p/(1 - q³) - 1/(1 + q)²) (n - 2)`.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Theorem 5 (`integers-2026-A65-thm-5`). -/
public theorem_wanted integral_symmetricPeakValley_geometric (n : ℕ) (hn : 2 ≤ n)
    (p : unitInterval) (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
    let q : ℝ := 1 - p
    let μ := Measure.pi fun _ : Fin n => geometricMeasure p
    ∫ x, (symmetricPeakCount (List.ofFn x) : ℝ) ∂μ = p ^ 2 * q / (1 - q ^ 3) * (n - 2) ∧
      ∫ x, (symmetricValleyCount (List.ofFn x) : ℝ) ∂μ =
        p ^ 2 * (1 / (1 - q ^ 2) - 1 / (1 - q ^ 3)) * (n - 2) ∧
      ∫ x, (symmetricPeakHeightSum (List.ofFn x) : ℝ) ∂μ = p * q / (1 - q ^ 3) * (n - 2) ∧
      ∫ x, (symmetricValleyDepthSum (List.ofFn x) : ℝ) ∂μ =
        q * (p / (1 - q ^ 3) - 1 / (1 + q) ^ 2) * (n - 2)


/-- Theorem 1: the generating function
`HSP(x, y, q, h) = ∑_{n} ∑_{c ⊨ n} xⁿ y^{#parts} q^{sp(c)} h^{hsp(c)}` of compositions by size,
number of parts, number of symmetric peaks and sum of their heights is
`1 / (1 - ∑_{a ≥ 1} x^a y / (1 - y² x^{2a+1} (qh/(1 - hx) - 1/(1 - x))))`.
Encoding: `y, q, h` are the variables `0, 1, 2` of `MvPolynomial (Fin 3) ℤ` and `x` is the
power-series variable; `qh/(1 - hx) - 1/(1 - x)` is written as its expansion
`∑_{j ≥ 0} (q h^{j+1} - 1) x^j`, and inverses of series with constant term `1` are
`PowerSeries.invOfUnit _ 1`. The coefficient of `xⁿ` only involves `a ≤ n`, so the sum over `a`
is truncated at `n` coefficientwise.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65, Theorem 1 (`integers-2026-A65-thm-1`). -/
public theorem_wanted symmetricPeak_compositions_trivariate_genFun (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk fun m => ∑ c : Composition m,
        MvPolynomial.X (0 : Fin 3) ^ c.length * MvPolynomial.X 1 ^ symmetricPeakCount c.blocks *
          MvPolynomial.X 2 ^ symmetricPeakHeightSum c.blocks : PowerSeries (MvPolynomial (Fin 3) ℤ)) =
      PowerSeries.coeff n (PowerSeries.invOfUnit (1 - ∑ a ∈ Finset.Icc 1 n,
        X ^ a * PowerSeries.C (MvPolynomial.X 0) *
          PowerSeries.invOfUnit (1 - PowerSeries.C (MvPolynomial.X 0 ^ 2) * X ^ (2 * a + 1) *
            PowerSeries.mk fun j =>
              MvPolynomial.X 1 * MvPolynomial.X 2 ^ (j + 1) - 1) 1) 1)

/-- Theorem 3: the generating function
`DSV(x, y, p, d) = ∑_{n} ∑_{c ⊨ n} xⁿ y^{#parts} p^{sv(c)} d^{dsv(c)}` of compositions by size,
number of parts, number of symmetric valleys and sum of their depths is
`1 / (1 - ∑_{a ≥ 1} x^a y / (1 - y² x^{a+1} (p(x^{a-1} - d^{a-1})/(x/d - 1)
- (x^{a-1} - 1)/(x - 1))))`, i.e. with inner factor
`∑_{b=1}^{a-1} (p d^{a-b} - 1) x^{b-1}`, which is written here.
Corrected reading: the paper prints `(p x^{a-1} - d^{a-1})/(x/d - 1)`, with `p` on the first
term only; that is false (at `n = 3` it gives the composition `111` a symmetric valley of depth
`0`). The corrected term `p(x^{a-1} - d^{a-1})/(x/d - 1)` is the penultimate line of the paper's
proof, `x^a y² p d^a ((x/d)^a - x/d)/(x/d - 1)`, and agrees with the paper's specialization
`d = 1`, `(x^{a-1} - 1)(p - 1)/(x - 1)`. Encoding as in
`symmetricPeak_compositions_trivariate_genFun`, with `y, p, d` the variables `0, 1, 2`.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65, Theorem 3 (`integers-2026-A65-thm-3`). -/
public theorem_wanted symmetricValley_compositions_trivariate_genFun (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk fun m => ∑ c : Composition m,
        MvPolynomial.X (0 : Fin 3) ^ c.length * MvPolynomial.X 1 ^ symmetricValleyCount c.blocks *
          MvPolynomial.X 2 ^ symmetricValleyDepthSum c.blocks :
        PowerSeries (MvPolynomial (Fin 3) ℤ)) =
      PowerSeries.coeff n (PowerSeries.invOfUnit (1 - ∑ a ∈ Finset.Icc 1 n,
        X ^ a * PowerSeries.C (MvPolynomial.X 0) *
          PowerSeries.invOfUnit (1 - PowerSeries.C (MvPolynomial.X 0 ^ 2) * X ^ (a + 1) *
            ∑ b ∈ Finset.Ico 1 a,
              PowerSeries.C (MvPolynomial.X 1 * MvPolynomial.X 2 ^ (a - b) - 1) * X ^ (b - 1)) 1) 1)

end

end MetaMathlibExt
