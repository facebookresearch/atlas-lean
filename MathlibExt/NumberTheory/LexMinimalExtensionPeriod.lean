/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LexMinimalExtensionMonoid

/-!
# Divisibility of the minimal eventual period

The formula for the least positive eventual period gives the divisibility of that period by the
GCD of the maximizing prefix lengths.

## References

* Jonathan Caalim and Yu-ichi Tanaka, *Generalized Binomial Coefficients and the Monoid of
  Lexicographically Minimal Extensions*, INTEGERS **26** (2026), Article A113, pp. 1–14,
  Section 3, Lemma 3 and Theorem 1 (pp. 6–7). We deduce Lemma 3 from the stronger Theorem 1.
* Jonathan Caalim and Yu-ichi Tanaka, *Lexicographically Minimal Extension of a Finite Binomid
  Index*, INTEGERS **24** (2024), Article A53, pp. 1–13, Theorem 1 (p. 8), cited in the later
  paper for eventual periodicity of lex-minimal extensions and the period of a maximizing length.
-/

namespace MetaMathlibExt

/-- **The gcd of the maximizing indices divides the minimal period.** Let $m \ge 1$, let
$\eta = (e_1, e_2, \dots)$ be the lex-minimal extension of its first $m$ entries, with averages
$A_i = (e_1 + \dots + e_i)/i$, and let $g$ be the greatest common divisor of the indices
$1 \le i \le m$ with $A_i = \max \{A_j \mid 1 \le j \le m\}$. If $p$ is the least $q \ge 1$
such that $e_{i+q} = e_i$ for all sufficiently large $i$, then $g$ divides $p$.

Source: Caalim and Tanaka, *Generalized Binomial Coefficients and the Monoid
of Lexicographically Minimal Extensions*, INTEGERS 26 (2026), Article A113,
Lemma 3 (`integers-2026-A113-lem-3`). -/
public theorem IsLexMinimalExtensionOf.gcd_maxAverageIndices_dvd_minimalPeriod
    {η : ℕ → ℕ} {m : ℕ} (hη : IsLexMinimalExtensionOf η m) (hm : 1 ≤ m) {p : ℕ}
    (hp : IsLeast {q : ℕ | 0 < q ∧ ∃ N, ∀ i, N ≤ i → η (i + q) = η i} p) :
    (maxAverageIndices η m).gcd id ∣ p := by
  rw [(hη.isLeast_period_gcd_maxAverageIndices hm).unique hp]

end MetaMathlibExt
