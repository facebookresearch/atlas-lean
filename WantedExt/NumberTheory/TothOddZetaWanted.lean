/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import MathlibExt.Analysis.Ramanujan.Part1Ch5Entry10bEuleriansymmetry
public import WantedExt.Combinatorics.ReducedComplexitiesWanted

namespace MetaMathlibExt

@[expose] public section

open MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry10bEuleriansymmetry
open MathlibExt.Combinatorics.ReducedComplexitiesWanted (paperfoldingSeq)

/-- Hurwitz zeta at `3/4` and odd arguments: for `k ≥ 1`,
`ζ(2k+1, 3/4) = -2^{2k-1} π^{2k+1} |E_{2k}| / (2k)! + 2^{2k} (2^{2k+1} - 1) ζ(2k+1)`,
where `E_{2k}` is the even Euler number.

`E_{2k}` is `chapter5EulerEven k`, defined by the binomial recurrence equivalent to the source's
generating function `1 / cosh t = ∑ E_n tⁿ / n!` (the identity `cosh t · sech t = 1`). The
source writes `k ∈ ℕ`; `k = 0` is excluded since `s = 1` is the pole of both zeta functions.

Source: László Tóth, *Evaluating ζ(s) at Odd Positive Integers Using Automatic Dirichlet
Series*, Journal of Integer Sequences 28 (2025), Article 25.4.4, Lemma 3
(`jis-2025-25.4.4-lem-3`). -/
public theorem_wanted hurwitzZeta_three_quarters_two_mul_add_one (k : ℕ) (hk : 1 ≤ k) :
    HurwitzZeta.hurwitzZeta ((3 / 4 : ℝ) : UnitAddCircle) (2 * k + 1) =
      -((2 : ℂ) ^ (2 * k - 1) / (2 * k).factorial) * (Real.pi : ℂ) ^ (2 * k + 1) *
          ((|chapter5EulerEven k| : ℤ) : ℂ) +
        2 ^ (2 * k) * (2 ^ (2 * k + 1) - 1) * riemannZeta (2 * k + 1)


/-- For `k ≥ 1`,
`ζ(2k+1) - 2^{2k-1} |E_{2k}| π^{2k+1} / (2k)! = ∑_{n ≥ 1} N(n;k) / n^{2k+1}` with
`N(n;k) = (2^{4k+1} - 2^{2k})(2bₙ - 1) + 2^{-(2k+1)}((2^{2k+1} + 1) t_{n-1} + (2^{2k+1} - 1) tₙ)`,
where `(bₙ)_{n ≥ 1}` is the regular paperfolding sequence (`b_{2n} = bₙ`, `b_{4n+1} = 0`,
`b_{4n+3} = 1`; `bₙ = paperfoldingSeq (n - 1)`), `(tₙ)_{n ≥ 0}` is the Thue-Morse sequence
(`thueMorse`), and `E_{2k}` is the even Euler number (`chapter5EulerEven k`). The sum is
indexed by `n + 1`.

Source: László Tóth, *Evaluating ζ(s) at Odd Positive Integers Using Automatic Dirichlet
Series*, Journal of Integer Sequences 28 (2025), Article 25.4.4, Theorem 2 (`jis-2025-25.4.4-thm-2`); `bₙ`, `tₙ` read from arXiv:2508.04151v1. -/
public theorem_wanted riemannZeta_two_mul_add_one_sub_eq_tsum_paperfolding_thueMorse (k : ℕ)
    (hk : 1 ≤ k) :
    riemannZeta (2 * k + 1) - (2 : ℂ) ^ (2 * k - 1) / (2 * k).factorial *
        ((|chapter5EulerEven k| : ℤ) : ℂ) * (Real.pi : ℂ) ^ (2 * k + 1) =
      ((∑' n : ℕ, (((2 : ℝ) ^ (4 * k + 1) - 2 ^ (2 * k)) *
            (2 * ((paperfoldingSeq n).toNat : ℝ) - 1) +
          ((2 : ℝ) ^ (2 * k + 1))⁻¹ * (((2 : ℝ) ^ (2 * k + 1) + 1) * ((thueMorse n).toNat : ℝ) +
            ((2 : ℝ) ^ (2 * k + 1) - 1) * ((thueMorse (n + 1)).toNat : ℝ))) /
          ((n + 1 : ℕ) : ℝ) ^ (2 * k + 1) : ℝ) : ℂ)

/-- For `k ≥ 1`,
`(2^{4k+1} - 2^{2k}) ∑_{n ≥ 1} (2bₙ - 1)/n^{2k+1} = -2^{2k-1} π^{2k+1} |E_{2k}| / (2k)!`,
with `(bₙ)` the regular paperfolding sequence (`bₙ = paperfoldingSeq (n - 1)`; the sum is indexed
by `n + 1`) and `E_{2k}` the even Euler number.

Source: László Tóth, *Evaluating ζ(s) at Odd Positive Integers Using Automatic Dirichlet
Series*, Journal of Integer Sequences 28 (2025), Article 25.4.4, Lemma 5 (`jis-2025-25.4.4-lem-5`); `bₙ` read from arXiv:2508.04151v1. -/
public theorem_wanted tsum_paperfolding_two_mul_add_one (k : ℕ) (hk : 1 ≤ k) :
    ((2 : ℝ) ^ (4 * k + 1) - 2 ^ (2 * k)) *
        ∑' n : ℕ, (2 * ((paperfoldingSeq n).toNat : ℝ) - 1) / ((n + 1 : ℕ) : ℝ) ^ (2 * k + 1) =
      -((2 : ℝ) ^ (2 * k - 1) / (2 * k).factorial) * Real.pi ^ (2 * k + 1) *
        ((|chapter5EulerEven k| : ℤ) : ℝ)

/-- For `k ≥ 1`, with `βₙ = (-1)^{bₙ}` for the regular paperfolding sequence,
`∑ βₙ / n^{2k+1} = π^{2k+1} |E_{2k}| / ((2^{2k+2} - 2)(2k)!)`, summed over `n ≥ 1`. The
printed sum `∑_{n ≥ 0} βₙ/(n+1)^{2k+1}` uses `b₀`, which the recurrence `b_{2n} = bₙ` leaves
undetermined; the paper's proof (from Lemma 5) gives the sum over `n ≥ 1` of `βₙ/n^{2k+1}`,
i.e. the printed sum with the paperfolding sequence indexed from `0` (`paperfoldingSeq`).

Source: László Tóth, *Evaluating ζ(s) at Odd Positive Integers Using Automatic Dirichlet
Series*, Journal of Integer Sequences 28 (2025), Article 25.4.4, Corollary 7 (`jis-2025-25.4.4-cor-7`); `bₙ` read from arXiv:2508.04151v1. -/
public theorem_wanted tsum_neg_one_pow_paperfolding (k : ℕ) (hk : 1 ≤ k) :
    ∑' n : ℕ, (-1 : ℝ) ^ (paperfoldingSeq n).toNat / ((n + 1 : ℕ) : ℝ) ^ (2 * k + 1) =
      Real.pi ^ (2 * k + 1) * ((|chapter5EulerEven k| : ℤ) : ℝ) /
        (((2 : ℝ) ^ (2 * k + 2) - 2) * (2 * k).factorial)

end

end MetaMathlibExt
