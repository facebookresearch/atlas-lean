/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Even
public import MathlibExt.NumberTheory.ContinuedFractions.Folding
public import MathlibExt.NumberTheory.ContinuedFractions.Paperfolding

/-!
# The folding lemma for finite continued fractions

Lemma 13 of Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued
Fractions*, Journal of Integer Sequences 29 (2026), Article 26.3.6. A finite continued
fraction `[a₀; a₁, …, aₜ]` with arbitrary integer entries is `finiteContFrac`.

Theorem 14, Corollary 15 and Theorem 17 of the same paper: the simple continued fraction of
`S = ∑ sₖ` with `s₀ = 1`, `sₖ₊₁ = sₖ² / xₖ`, `x₀ = 2`, `xₖ ≥ 2` interleaves Cloitre's
self-describing sequence (`cloitreApprox`, OEIS A157196) with the terms `xₖ - 1` in ruler order,
and the digit `1` has density `2/3` in the Cloitre stages.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Folding lemma for finite continued fractions.** Let $a_0$ be an integer, let $t$ be even
and let $a_1, \dots, a_t$ be integers with $a_i \ge 1$ for every $i$, and let $q$ be the
denominator in lowest terms of the value $[a_0; a_1, \dots, a_t]$ of the finite continued
fraction. Then for every integer $x \ge 1$,
$[a_0; a_1, \dots, a_t] + 1/(x q^2) = [a_0; a_1, \dots, a_t, x, -a_t, \dots, -a_1]$.

For positive partial quotients, $q$ is the continuant $q_t$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Lemma 13, equation (`eq:fold`)
(`jis-2026-26.3.6-lem-13`). -/
public theorem_wanted finiteContFrac_add_inv_mul_den_sq (a₀ : ℤ) (a : List ℤ)
    (ha : ∀ b ∈ a, 1 ≤ b) (ht : Even a.length) (x : ℕ) (hx : 1 ≤ x) :
    finiteContFrac (a₀ :: a) + 1 / (x * ((finiteContFrac (a₀ :: a)).den : ℚ) ^ 2) =
      finiteContFrac (a₀ :: a ++ (x : ℤ) :: (a.map (fun b => -b)).reverse)

/-- **Continued fraction of a paperfolding sum via the words $A_k$.** Let $x = (x_k)_{k \ge 0}$ be
natural numbers with $x_0 = 2$ and $x_k \ge 2$ for all $k$, let $s_k$ be the paperfolding sum
terms defined by $x$, and let $S = \sum_{k \ge 0} s_k$, with continued fraction expansion
$[a_0; a_1, a_2, \ldots]$. Let $A_k$ be the continued-fraction words defined by $x$, so that
$A_0 = (1, 1)$ and $A_{k+1} = A_k \, (x_{k+1} - 1) \, A_k^r$, where the mirror image $A^r$ of a
word $A$ is obtained by reversing $A$ and then replacing a leading $2$ by $1, 1$, or two leading
letters $1, 1$ by $2$, leaving any other word unchanged. Then $a_0 = 1$, and for every $k$ the
partial quotients $a_1, a_2, \ldots$ begin with the word $A_k$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Corollary 15
(`jis-2026-26.3.6-cor-15`). -/
public theorem_wanted paperfoldingSum_contFrac_recursion (x : ℕ → ℕ) (hx0 : x 0 = 2)
    (hx : ∀ k, 2 ≤ x k) (k : ℕ) :
    (GenContFract.of (∑' n, paperfoldingSumTerm x n)).h = 1 ∧
      ∀ i (hi : i < (paperfoldingContFracWord x k).length),
        (GenContFract.of (∑' n, paperfoldingSumTerm x n)).partDens.get? i =
          some ((paperfoldingContFracWord x k)[i] : ℝ)

/-- **Digit frequencies in Cloitre's approximants.** Let $A_k$ be the $k$-th approximant of
Cloitre's sequence. As $k \to \infty$, the proportion of entries of $A_k$ equal to $1$ tends to
$2/3$, and the proportion of entries equal to $2$ tends to $1/3$.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Theorem 17
(`jis-2026-26.3.6-thm-17`). -/
public theorem_wanted tendsto_cloitreApprox_count_div_length :
    Filter.Tendsto (fun k => ((cloitreApprox k).count 1 : ℝ) / (cloitreApprox k).length)
        Filter.atTop (nhds (2 / 3)) ∧
      Filter.Tendsto (fun k => ((cloitreApprox k).count 2 : ℝ) / (cloitreApprox k).length)
        Filter.atTop (nhds (1 / 3))

end

end MetaMathlibExt
