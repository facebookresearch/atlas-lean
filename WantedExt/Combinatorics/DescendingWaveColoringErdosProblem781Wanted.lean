/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Monochromatic descending waves (Erdős Problem 781)

Erdős Problem 781 (Brown, Erdős and Freedman): let `f(k)` be the minimal `n` such that any
`2`-coloring of `{1, …, n}` contains a monochromatic `k`-term descending wave, a sequence `x_1 < ⋯ <
x_k` with `x_j ≥ (x_{j+1} + x_{j-1}) / 2` for `1 < j < k`. Estimate `f(k)`. In particular, is `f(k)
= k² - k + 1` for all `k`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Fin.Basic

@[expose] public section

namespace MathlibExt.Combinatorics.DescendingWaveColoringErdosProblem781Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #781, https://www.erdosproblems.com/781 (status
DISPROVED). UnsolvedMath record UM-30007031 (`EP-781`), dataset ulamai/UnsolvedMath v1.8.0.

`ForcesMonochromaticWave k n` says `f(k) ≤ n`; it is monotone in `n`, so `f(k) = k² - k + 1` is
'forced at `k² - k + 1` and not at `k² - k`', and `f(k) ≍ k³` is stated through the same predicate
without `sInf`. Waves are strictly increasing; formal-conjectures' `IsDescendingWave` omits `x_1 < ⋯
< x_k`, which lets constant sequences count as waves. Alon and Spencer work with ascending waves
(`x_{i+1} - x_i ≤ x_{i+2} - x_{i+1}`); the reflection `x ↦ n + 1 - x` exchanges ascending and
descending waves in `{1, …, n}`, so both define the same `f`, and Alon and Spencer quote Brown,
Erdős and Freedman's bounds for it. The refutation rests on the asymptotic lower bound, not on a
finite check.
-/

/-- A `k`-term descending wave: `x₀ < x₁ < ⋯ < x_{k-1}` with `x_{j-1} + x_{j+1} ≤ 2 x_j` for
`0 < j < k - 1`. -/
def IsDescendingWave {k : ℕ} (x : Fin k → ℕ) : Prop :=
  StrictMono x ∧ ∀ i j l : Fin k, (i : ℕ) + 1 = (j : ℕ) → (j : ℕ) + 1 = (l : ℕ) →
    x i + x l ≤ 2 * x j

/-- Every `2`-coloring of `{1, …, n}` has a monochromatic `k`-term descending wave, i.e.
`f(k) ≤ n`. -/
def ForcesMonochromaticWave (k n : ℕ) : Prop :=
  ∀ c : ℕ → Fin 2, ∃ x : Fin k → ℕ, IsDescendingWave x ∧ (∀ i, 1 ≤ x i ∧ x i ≤ n) ∧
    ∃ γ : Fin 2, ∀ i, c (x i) = γ

/-- Erdős Problem 781, the yes/no question: `f(k) = k² - k + 1` for every `k ≥ 1`. -/
def waveNumberQuadratic : Prop :=
  ∀ k : ℕ, 1 ≤ k → ForcesMonochromaticWave k (k ^ 2 - k + 1) ∧
    ¬ ForcesMonochromaticWave k (k ^ 2 - k)

/-- Erdős Problem 781, estimate of `f(k)`: `f(k) ≍ k³`. -/
def waveNumberCubicOrder : Prop :=
  ∃ c C : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in Filter.atTop,
    (∀ n : ℕ, ForcesMonochromaticWave k n → c * (k : ℝ) ^ 3 ≤ n) ∧
      ForcesMonochromaticWave k ⌊C * (k : ℝ) ^ 3⌋₊

/--
Resolved false: Alon and Spencer proved `f(k) ≥ c_1 k³` (Theorem 1.1), so `f(k) > k² - k + 1` for
all large `k`; erdosproblems.com/781 lists the problem as disproved. Source: T. F. Bloom, Erdős
Problems, Problem #781, https://www.erdosproblems.com/781 (status DISPROVED); resolution: N. Alon
and J. Spencer, Ascending waves, J. Combin. Theory Ser. A 52 (1989), 275-287; T. C. Brown, P. Erdős
and A. R. Freedman, Quasi-progressions and descending waves, J. Combin. Theory Ser. A 53 (1990),
81-95, Alon-Spencer Theorem 1.1: c_1 k³ ≤ f(k) ≤ c_2 k³ for all k ≥ 1, the upper bound being Brown,
Erdős and Freedman's f(k) ≤ k³/3 - 4k/3 + 3; Brown, Erdős and Freedman also proved k² - k + 1 ≤ f(k)
and asked whether it is the exact value, and Alon and Spencer: 'Here we show that this is false',
https://web.math.princeton.edu/~nalon/PDFS/Publications1/Ascending%20waves.pdf.
-/
public theorem_wanted waveNumberQuadratic_refuted : ¬ waveNumberQuadratic

/--
Resolved true: Alon and Spencer's Theorem 1.1 gives `c_1 k³ ≤ f(k) ≤ c_2 k³`, the upper bound being
Brown, Erdős and Freedman's `f(k) ≤ (k³ - 4k + 9) / 3` (erdosproblems.com/781). Source: T. F. Bloom,
Erdős Problems, Problem #781, https://www.erdosproblems.com/781 (status DISPROVED); resolution: N.
Alon and J. Spencer, Ascending waves, J. Combin. Theory Ser. A 52 (1989), 275-287; T. C. Brown, P.
Erdős and A. R. Freedman, Quasi-progressions and descending waves, J. Combin. Theory Ser. A 53
(1990), 81-95, Alon-Spencer Theorem 1.1: c_1 k³ ≤ f(k) ≤ c_2 k³ for all k ≥ 1, the upper bound being
Brown, Erdős and Freedman's f(k) ≤ k³/3 - 4k/3 + 3; Brown, Erdős and Freedman also proved k² - k + 1
≤ f(k) and asked whether it is the exact value, and Alon and Spencer: 'Here we show that this is
false', https://web.math.princeton.edu/~nalon/PDFS/Publications1/Ascending%20waves.pdf.
-/
public theorem_wanted waveNumberCubicOrder_holds : waveNumberCubicOrder

end MathlibExt.Combinatorics.DescendingWaveColoringErdosProblem781Wanted
