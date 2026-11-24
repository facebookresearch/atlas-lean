/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Incomplete finite binomial sums of harmonic numbers

Statements from Richard Kollár, "Incomplete Finite Binomial Sums
of Harmonic Numbers", *Journal of Integer Sequences* 27 (2024),
Article 24.2.1
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/Kollar/kollar6.html>).

Here `harmonic` is Mathlib's rational harmonic number.  The paper's
auxiliary sums are
`Cₙ = ∑ k ∈ [1,n], 1 / (k * 2 ^ k)` and
`Dₙ = ∑ k ∈ [1,n], (2k).choose k / ((2 * k) * 2 ^ (2 * k))`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Harmonic.Defs
public import MathlibExt.Combinatorics.Enumerative.IncompleteBinomialHarmonicSums

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.IncompleteBinomialHarmonicSumsWanted

/-- **Half-range binomial sum of harmonic numbers with top index $2n$.** Let $H_i$ denote
the $i$-th harmonic number (with $H_0 = 0$), and let Kollár's auxiliary sums be
$C_n = \sum_{k=1}^{n} \frac{1}{k \, 2^k}$ and
$D_n = \sum_{k=1}^{n} \frac{\binom{2k}{k}}{2k \cdot 2^{2k}}$.
For every positive integer $n$,
$$\sum_{i=0}^{n} \binom{2n}{i} H_i =
2^{2n-1} \left( H_{2n} - 2 C_{2n} + D_n \right) + \frac{1}{2} \binom{2n}{n} H_n.$$

Source: Richard Kollár, "Incomplete Finite Binomial Sums of
Harmonic Numbers", Theorem 3, equation `evenH`. -/
theorem_wanted sum_range_choose_two_mul_mul_harmonic
    (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ Finset.range (n + 1), ((2 * n).choose i : ℚ) * harmonic i) =
      (2 : ℚ) ^ (2 * n - 1) *
          (harmonic (2 * n) - 2 * invPowTwoSum (2 * n) +
            centralBinomWeightedSum n) +
        (1 / 2 : ℚ) * ((2 * n).choose n : ℚ) * harmonic n

end MathlibExt.Combinatorics.Enumerative.IncompleteBinomialHarmonicSumsWanted
