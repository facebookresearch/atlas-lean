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
public import MathlibExt.Combinatorics.DescendingWaveColoringErdosProblem781

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
Erdős and Freedman's bounds for it. Their asymptotic lower bound refutes the quadratic formula.
-/

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
