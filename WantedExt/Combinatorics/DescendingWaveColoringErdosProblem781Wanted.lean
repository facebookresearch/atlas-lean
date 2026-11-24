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

/-- **Descending wave.** A $k$-term descending wave is a sequence $x_0, x_1, \dots, x_{k-1}$ of
natural numbers with $x_0 < x_1 < \dots < x_{k-1}$ and $x_{j-1} + x_{j+1} \le 2 x_j$ for every
$j$ with $0 < j < k - 1$. -/
def IsDescendingWave {k : ℕ} (x : Fin k → ℕ) : Prop :=
  StrictMono x ∧ ∀ i j l : Fin k, (i : ℕ) + 1 = (j : ℕ) → (j : ℕ) + 1 = (l : ℕ) →
    x i + x l ≤ 2 * x j

/-- **Forcing a monochromatic descending wave.** For natural numbers $k$ and $n$, the statement
that for every colouring of the natural numbers with two colours there is a monochromatic $k$-term
descending wave all of whose terms lie in $\{1, \dots, n\}$. Equivalently, every colouring of
$\{1, \dots, n\}$ with two colours has a monochromatic $k$-term descending wave, so the statement
says $f(k) \le n$, where $f(k)$ is the least $n$ with this property. -/
def ForcesMonochromaticWave (k n : ℕ) : Prop :=
  ∀ c : ℕ → Fin 2, ∃ x : Fin k → ℕ, IsDescendingWave x ∧ (∀ i, 1 ≤ x i ∧ x i ≤ n) ∧
    ∃ γ : Fin 2, ∀ i, c (x i) = γ

/-- **Erdős Problem 781, the exact-value question.** For natural numbers $k$ and $n$, say that $n$
forces a $k$-term wave if every colouring of $\{1, \dots, n\}$ with two colours has a monochromatic
$k$-term descending wave. The statement that for every natural number $k \ge 1$ the number
$k^2 - k + 1$ forces a $k$-term wave and the number $k^2 - k$ does not; that is,
$f(k) = k^2 - k + 1$ for every $k \ge 1$, where $f(k)$ is the least $n$ that forces a $k$-term
wave. -/
def waveNumberQuadratic : Prop :=
  ∀ k : ℕ, 1 ≤ k → ForcesMonochromaticWave k (k ^ 2 - k + 1) ∧
    ¬ ForcesMonochromaticWave k (k ^ 2 - k)

/-- **Erdős Problem 781, cubic order of the wave number.** For natural numbers $k$ and $n$, say
that $n$ forces a $k$-term wave if every colouring of $\{1, \dots, n\}$ with two colours has a
monochromatic $k$-term descending wave. The statement that there are real numbers $c > 0$ and $C$
such that for all sufficiently large $k$, every natural number $n$ that forces a $k$-term wave
satisfies $n \ge c k^3$, and the natural number $\lfloor \max(C k^3, 0) \rfloor$ forces a $k$-term
wave. Writing $f(k)$ for the least $n$ that forces a $k$-term wave, this says $f(k) \asymp k^3$. -/
def waveNumberCubicOrder : Prop :=
  ∃ c C : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in Filter.atTop,
    (∀ n : ℕ, ForcesMonochromaticWave k n → c * (k : ℝ) ^ 3 ≤ n) ∧
      ForcesMonochromaticWave k ⌊C * (k : ℝ) ^ 3⌋₊

/--
**Erdős Problem 781 is false.** For natural numbers $k$ and $n$, say that $n$ forces a $k$-term
wave if every colouring of $\{1, \dots, n\}$ with two colours has a monochromatic $k$-term
descending wave. It is not the case that for every natural number $k \ge 1$ the number
$k^2 - k + 1$ forces a $k$-term wave and the number $k^2 - k$ does not. Writing $f(k)$ for the
least $n$ that forces a $k$-term wave, this says that $f(k) \ne k^2 - k + 1$ for some $k \ge 1$.

Alon and Spencer proved $f(k) \ge c k^3$ for some $c > 0$, so $f(k) > k^2 - k + 1$ for all large
$k$.

Source: T. F. Bloom, Erdős
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
**Alon–Spencer: the descending-wave number has cubic order.** For natural numbers $k$ and $n$, say
that $n$ forces a $k$-term wave if every colouring of $\{1, \dots, n\}$ with two colours has a
monochromatic $k$-term descending wave. There are real numbers $c > 0$ and $C$ such that for all
sufficiently large $k$, every natural number $n$ that forces a $k$-term wave satisfies
$n \ge c k^3$, and the natural number $\lfloor \max(C k^3, 0) \rfloor$ forces a $k$-term wave.
Writing $f(k)$ for the least $n$ that forces a $k$-term wave, this says $f(k) \asymp k^3$.

Source: T. F. Bloom,
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
