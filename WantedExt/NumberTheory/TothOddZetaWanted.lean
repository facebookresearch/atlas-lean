/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.ReducedComplexities
public import MathlibExt.NumberTheory.TothOddZeta

namespace MetaMathlibExt

@[expose] public section

open MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry10bEuleriansymmetry
open MathlibExt.Combinatorics.ReducedComplexitiesWanted (paperfoldingSeq)

/-- **Tóth's paperfolding and Thue–Morse series for $\zeta(2k+1)$.** Let $(f_n)_{n \ge 0}$ be the
regular paperfolding sequence and $(t_n)_{n \ge 0}$ the Thue–Morse sequence, both indexed from
$0$, and let $E_{2k}$ be the even-index Euler number. For every integer $k \ge 1$,
$$
\zeta(2k+1) - \frac{2^{2k-1} |E_{2k}| \pi^{2k+1}}{(2k)!} =
\sum_{n \ge 0} \frac{N_k(n)}{(n+1)^{2k+1}},
$$
where
$$
N_k(n) = (2^{4k+1} - 2^{2k})(2 f_n - 1) +
2^{-(2k+1)} \bigl((2^{2k+1} + 1) t_n + (2^{2k+1} - 1) t_{n+1}\bigr).
$$

In the source's indexing $b_n = f_{n-1}$ for $n \ge 1$ (so $b_{2n} = b_n$, $b_{4n+1} = 0$ and
$b_{4n+3} = 1$), the right side is $\sum_{n \ge 1} N(n;k)/n^{2k+1}$ with
$N(n;k) = (2^{4k+1} - 2^{2k})(2b_n - 1) +
2^{-(2k+1)}((2^{2k+1} + 1) t_{n-1} + (2^{2k+1} - 1) t_n)$.

Source: László Tóth, *Evaluating ζ(s) at Odd Positive Integers Using Automatic Dirichlet
Series*, Journal of Integer Sequences 28 (2025), Article 25.4.4, Theorem 2
(`jis-2025-25.4.4-thm-2`); `bₙ`, `tₙ` read from arXiv:2508.04151v1. -/
public theorem_wanted riemannZeta_two_mul_add_one_sub_eq_tsum_paperfolding_thueMorse (k : ℕ)
    (hk : 1 ≤ k) :
    riemannZeta (2 * k + 1) - (2 : ℂ) ^ (2 * k - 1) / (2 * k).factorial *
        ((|chapter5EulerEven k| : ℤ) : ℂ) * (Real.pi : ℂ) ^ (2 * k + 1) =
      ((∑' n : ℕ, (((2 : ℝ) ^ (4 * k + 1) - 2 ^ (2 * k)) *
            (2 * ((paperfoldingSeq n).toNat : ℝ) - 1) +
          ((2 : ℝ) ^ (2 * k + 1))⁻¹ * (((2 : ℝ) ^ (2 * k + 1) + 1) * ((thueMorse n).toNat : ℝ) +
            ((2 : ℝ) ^ (2 * k + 1) - 1) * ((thueMorse (n + 1)).toNat : ℝ))) /
          ((n + 1 : ℕ) : ℝ) ^ (2 * k + 1) : ℝ) : ℂ)

/-- **A paperfolding Dirichlet series at odd integers.** Let $(f_n)_{n \ge 0}$ be the regular
paperfolding sequence, indexed from $0$, and let $E_{2k}$ be the even-index Euler number. For
every integer $k \ge 1$,
$$
(2^{4k+1} - 2^{2k}) \sum_{n \ge 0} \frac{2 f_n - 1}{(n+1)^{2k+1}}
= -\frac{2^{2k-1} \pi^{2k+1} |E_{2k}|}{(2k)!}.
$$

In the source's indexing $b_n = f_{n-1}$ for $n \ge 1$, the sum is
$\sum_{n \ge 1} (2 b_n - 1)/n^{2k+1}$.

Source: László Tóth, *Evaluating ζ(s) at Odd Positive Integers Using Automatic Dirichlet
Series*, Journal of Integer Sequences 28 (2025), Article 25.4.4, Lemma 5 (`jis-2025-25.4.4-lem-5`);
`bₙ` read from arXiv:2508.04151v1. -/
public theorem_wanted tsum_paperfolding_two_mul_add_one (k : ℕ) (hk : 1 ≤ k) :
    ((2 : ℝ) ^ (4 * k + 1) - 2 ^ (2 * k)) *
        ∑' n : ℕ, (2 * ((paperfoldingSeq n).toNat : ℝ) - 1) / ((n + 1 : ℕ) : ℝ) ^ (2 * k + 1) =
      -((2 : ℝ) ^ (2 * k - 1) / (2 * k).factorial) * Real.pi ^ (2 * k + 1) *
        ((|chapter5EulerEven k| : ℤ) : ℝ)

end

end MetaMathlibExt
