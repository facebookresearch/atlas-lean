/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A counterexample to Szüsz and Volkmann's construction of normal numbers

Statements from John M. Campbell, *A Counterexample to a Purported Construction of Normal
Numbers*, Journal of Integer Sequences 29 (2026), Article 26.3.4.

The paper builds an integer sequence `h₂` (OEIS A380904) whose terms grow quadratically but carry
many trailing zeros, and a differentiable increasing interpolation `f` with `⌊f(n)⌋ = h₂(n)`,
`η(f) = 2` and `η(f') = 1`, where `η(h) = lim_{x → ∞} log h(x) / log x`. Szüsz and Volkmann's
Theorem 2 would make `0.h₂(1)h₂(2)…` normal; the paper shows it is not. Normality uses
`MetaMathlibExt.NormalNumber.IsNormalInBase`.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import MathlibExt.NumberTheory.NormalNumber

namespace MetaMathlibExt

@[expose] public section

/-- `h₁(n) = 0` for `n < 10` and `h₁(n) = 10^{⌊log₁₀ n⌋}` otherwise (`⌊log₁₀ n⌋` is
`Nat.log 10 n`).

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Section 2 (definition of `h₁`). -/
def campbellH1 (n : ℕ) : ℕ :=
  if n < 10 then 0 else 10 ^ Nat.log 10 n

/-- `h₁(9) = 0`, `h₁(10) = 10`, `h₁(99) = 10` and `h₁(100) = 100`.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Section 2. -/
theorem campbellH1_small :
    campbellH1 9 = 0 ∧ campbellH1 10 = 10 ∧ campbellH1 99 = 10 ∧ campbellH1 100 = 100 := by
  decide

/-- `h₂(n) = 10^k ⌊(∑_{i=1}^{10^k} h₁(i)) / 10^k⌋ + ∑_{i=10^k+1}^{n} h₁(i)` with
`k = ⌊log₁₀ n⌋` (OEIS A380904).

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Section 2, Equation (6)
(definition of `h₂`). -/
def campbellH2 (n : ℕ) : ℕ :=
  10 ^ Nat.log 10 n * ((∑ i ∈ Finset.Icc 1 (10 ^ Nat.log 10 n), campbellH1 i) / 10 ^ Nat.log 10 n) +
    ∑ i ∈ Finset.Icc (10 ^ Nat.log 10 n + 1) n, campbellH1 i

/-- `h₂(9) = 0`, `h₂(10) = 10`, `h₂(21) = 120`, `h₂(99) = 900` and `h₂(100) = 1000`
(Example 1 and Section 2.1 of the paper).

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Example 1 and Section 2.1. -/
theorem campbellH2_small :
    campbellH2 9 = 0 ∧ campbellH2 10 = 10 ∧ campbellH2 21 = 120 ∧ campbellH2 99 = 900 ∧
      campbellH2 100 = 1000 := by
  decide +kernel

/-- The auxiliary piecewise-linear function `h₃^{(m)}` on `[10^m - 1, 10^m]` (`m ≥ 2`):
`a(m) t + b(m)` for `t ≤ 10^m - 1/10` and `c(m) t + d(m)` afterwards, where, with
`𝓗(m) = y₁(m + 1) - y₂(m)`, `y₁(n) = h₂(10^{n-1})` and `y₂(n) = h₂(10^n - 1)`,
`a(m) = (20𝓗(m) - 11·10^m)/9 + 9·10^{m-1}`,
`b(m) = (10^m - 1)(-20𝓗(m) + 11·10^m)/9 + 10^m - 9·10^{2m-1}`,
`c(m) = -20𝓗(m) + 9·10^{m-1} + 11·10^m`, and
`d(m) = 20·10^m 𝓗(m) - 11·10^{2m} - 9·10^{2m-1} + 10^m`.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Section 2.2, Equations (16)-(20). -/
noncomputable def campbellH3 (m : ℕ) (t : ℝ) : ℝ :=
  let H : ℝ := (campbellH2 (10 ^ m) : ℝ) - campbellH2 (10 ^ m - 1)
  if t ≤ 10 ^ m - 1 / 10 then
    ((20 * H - 11 * 10 ^ m) / 9 + 9 * 10 ^ (m - 1)) * t +
      ((10 ^ m - 1) * (-20 * H + 11 * 10 ^ m) / 9 + 10 ^ m - 9 * 10 ^ (2 * m - 1))
  else
    (-20 * H + 9 * 10 ^ (m - 1) + 11 * 10 ^ m) * t +
      (20 * 10 ^ m * H - 11 * 10 ^ (2 * m) - 9 * 10 ^ (2 * m - 1) + 10 ^ m)

/-- `h₃^{(m)}(t) = a(m) t + b(m)` on the first piece `t ≤ 10^m - 1/10`.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Section 2.2. -/
theorem campbellH3_of_le {m : ℕ} {t : ℝ} (ht : t ≤ 10 ^ m - 1 / 10) :
    campbellH3 m t =
      ((20 * ((campbellH2 (10 ^ m) : ℝ) - campbellH2 (10 ^ m - 1)) - 11 * 10 ^ m) / 9 +
          9 * 10 ^ (m - 1)) * t +
        ((10 ^ m - 1) * (-20 * ((campbellH2 (10 ^ m) : ℝ) - campbellH2 (10 ^ m - 1)) +
            11 * 10 ^ m) / 9 + 10 ^ m - 9 * 10 ^ (2 * m - 1)) := by
  simp only [campbellH3, ht, ite_true]

/-- Campbell's interpolation `f`: `f(x) = (89/110) e^{(100/89)(11x - 100)} + 1/10` for
`x ≤ 100/11`, `f(x) = 10x - 90` for `100/11 ≤ x ≤ 10`, and for `m ≥ 2`
`f(x) = (x (y₂(m) - y₁(m)) - (y₁(m) + 10^{m-1} y₂(m) - 10^m y₁(m))) / (9·10^{m-1} - 1)` for
`10^{m-1} ≤ x ≤ 10^m - 1` and `f(x) = h₂(10^m - 1) + ∫_{10^m - 1}^x h₃^{(m)}(t) dt` for
`10^m - 1 ≤ x ≤ 10^m`. For `x > 10` the index is `m = ⌊log₁₀ ⌊x⌋⌋ + 1`, so a power of ten
`x = 10^{m-1}` uses the left end of its interval (the two pieces agree there). The paper's
domain is `ℝ_{≥ 0}`; the first formula is used for every `x ≤ 100/11`.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Section 2.2, Equations (15) and (21). -/
noncomputable def campbellF (x : ℝ) : ℝ :=
  if x ≤ 100 / 11 then 89 / 110 * Real.exp (100 / 89 * (11 * x - 100)) + 1 / 10
  else if x ≤ 10 then 10 * x - 90
  else
    let m := Nat.log 10 ⌊x⌋₊ + 1
    let y₁ : ℝ := campbellH2 (10 ^ (m - 1))
    let y₂ : ℝ := campbellH2 (10 ^ m - 1)
    if x ≤ 10 ^ m - 1 then
      (x * (y₂ - y₁) - (y₁ + 10 ^ (m - 1) * y₂ - 10 ^ m * y₁)) / (9 * 10 ^ (m - 1) - 1)
    else
      y₂ + ∫ t in ((10 : ℝ) ^ m - 1)..x, campbellH3 m t

/-- `f(x) = 10x - 90` for `100/11 < x ≤ 10`.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Section 2.2. -/
theorem campbellF_of_mem {x : ℝ} (h₁ : 100 / 11 < x) (h₂ : x ≤ 10) : campbellF x = 10 * x - 90 := by
  simp [campbellF, not_le.2 h₁, h₂]

/-- The base-10 digits of `h₂(n)`, most significant first; `h₂(n) = 0` is written as the single
digit `0`.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Section 1.1 (the expansion
`0.b₁b₂…` with `b_n` the base-`g` expansion of `⌊f(n)⌋`). -/
def campbellBlock (n : ℕ) : List ℕ :=
  if campbellH2 n = 0 then [0] else (Nat.digits 10 (campbellH2 n)).reverse

/-- The `j`-th digit (0-indexed) after the decimal point of `0.h₂(1)h₂(2)…`: every block is
nonempty, so the first `j + 1` blocks contain at least `j + 1` digits.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Theorem 8 (the concatenation
`0.h₂(1)h₂(2)…`). -/
def campbellConcatDigit (j : ℕ) : ℕ :=
  ((List.range (j + 1)).flatMap fun i => campbellBlock (i + 1)).getD j 0

/-- The first ten digits of `0.h₂(1)h₂(2)…` are `0000000001` (nine zero blocks, then `h₂(10) = 10`).

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Example 1. -/
theorem campbellConcatDigit_small :
    (List.range 11).map campbellConcatDigit = [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] := by
  decide +kernel

/-- The real number `0.h₂(1)h₂(2)…`.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Theorem 8. -/
noncomputable def campbellConstant : ℝ :=
  ∑' j : ℕ, (campbellConcatDigit j : ℝ) / 10 ^ (j + 1)

/-- Lemma 2: for `ℓ ≥ 1`, `∑_{i=1}^{10^{ℓ+1}-1} h₁(i) = 9090⋯900` (`ℓ` blocks `90`, then `0`),
written as `∑_{j<ℓ} 900·100^j`; and for `ℓ ≥ 2`, with `y₁(n) = h₂(10^{n-1})` and
`y₂(n) = h₂(10^n - 1)`, `(y₂(ℓ) - y₁(ℓ)) / (9·10^{ℓ-1} - 1) = 10^{ℓ-1}` and
`y₁(ℓ + 1) - y₂(ℓ) = 10^{2⌊ℓ/2⌋}`.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Lemma 2
(`jis-2026-26.3.4-lem-2`). -/
public theorem_wanted campbellH1_sum_and_y_relations :
    (∀ ℓ : ℕ, 1 ≤ ℓ →
      ∑ i ∈ Finset.Icc 1 (10 ^ (ℓ + 1) - 1), campbellH1 i = ∑ j ∈ Finset.range ℓ, 900 * 100 ^ j) ∧
    ∀ ℓ : ℕ, 2 ≤ ℓ →
      ((campbellH2 (10 ^ ℓ - 1) : ℚ) - campbellH2 (10 ^ (ℓ - 1))) / (9 * 10 ^ (ℓ - 1) - 1) =
          10 ^ (ℓ - 1) ∧
        (campbellH2 (10 ^ ℓ) : ℤ) - campbellH2 (10 ^ ℓ - 1) = 10 ^ (2 * (ℓ / 2))

/-- Lemma 3: `⌊f(n)⌋ = h₂(n)` for every positive integer `n`, and `f(n) = h₂(n)` for `n ≥ 10`.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Lemma 3
(`jis-2026-26.3.4-lem-3`). -/
public theorem_wanted floor_campbellF_eq_campbellH2 :
    (∀ n : ℕ, 1 ≤ n → ⌊campbellF n⌋₊ = campbellH2 n) ∧
    ∀ n : ℕ, 10 ≤ n → campbellF n = campbellH2 n

/-- Lemma 4: `f` is differentiable on `ℝ_{>0}`.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Lemma 4
(`jis-2026-26.3.4-lem-4`). -/
public theorem_wanted campbellF_differentiableOn : DifferentiableOn ℝ campbellF (Set.Ioi 0)

/-- Lemma 5: `f` is monotonically increasing (non-decreasing) on `ℝ_{≥ 0}`.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Lemma 5
(`jis-2026-26.3.4-lem-5`). -/
public theorem_wanted campbellF_monotoneOn : MonotoneOn campbellF (Set.Ici 0)

/-- Lemma 6: `η(f) = lim_{x → ∞} log f(x) / log x` exists and equals `2`.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Lemma 6
(`jis-2026-26.3.4-lem-6`). -/
public theorem_wanted tendsto_log_campbellF_div_log :
    Filter.Tendsto (fun x => Real.log (campbellF x) / Real.log x) Filter.atTop (nhds 2)

/-- Lemma 7: `η(f') = lim_{x → ∞} log f'(x) / log x` exists and equals `1`.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Lemma 7
(`jis-2026-26.3.4-lem-7`). -/
public theorem_wanted tendsto_log_deriv_campbellF_div_log :
    Filter.Tendsto (fun x => Real.log (deriv campbellF x) / Real.log x) Filter.atTop (nhds 1)

/-- Theorem 8: the concatenation `0.h₂(1)h₂(2)…` is not normal in base 10.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Theorem 8
(`jis-2026-26.3.4-thm-8`). -/
public theorem_wanted not_isNormalInBase_campbellConstant :
    ¬ NormalNumber.IsNormalInBase 10 campbellConstant

end

end MetaMathlibExt
