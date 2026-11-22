/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import MathlibExt.Analysis.Ramanujan.Part1Ch5Entry10bEuleriansymmetry
public import MathlibExt.Analysis.Ramanujan.Part1Ch7DirichletBeta

namespace MetaMathlibExt

@[expose] public section

open MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry10bEuleriansymmetry
open MathlibExt.Analysis.Ramanujan.Part1Ch7.DirichletBeta

/-- The odd-denominator zeta series: for integers `k > 1`,
`∑_{n ≥ 1} 1/(2n - 1)^k = (1 - 2^{-k}) ζ(k)`, stated over `ℂ` with Mathlib's `riemannZeta`
and the index shifted to `n ≥ 0` (`2n + 1`). The source writes `k > 1`; it uses `k` as an
integer throughout, so `k` is a natural number with `2 ≤ k` here.

Source: Jan W. H. Swanepoel, *A Short Simple Probabilistic Proof of a Well Known Identity
and the Derivation of Related New Identities Involving the Bernoulli Numbers and the Euler
Numbers*, INTEGERS 25 (2025), Article A50, Proposition 2, Equation (11)
(`integers-2025-A50-prop-2`), citing its reference [20]. -/
public theorem_wanted hasSum_one_div_odd_pow (k : ℕ) (hk : 2 ≤ k) :
    HasSum (fun n : ℕ => 1 / (2 * (n : ℂ) + 1) ^ k) ((1 - 1 / 2 ^ k) * riemannZeta k)

/-- Dirichlet beta at odd positive integers: for each even `k ≥ 2`,
`β(k - 1) = (π/2)^{k-1} |E_{k-2}| / (2 (k - 2)!)`, equivalently
`β(k - 1) = π^{k-1} |E_{k-2}| / (2^k (k - 2)!)`, the source's Equation (12)
(`β(1) = π/4`, `β(3) = π³/32`, `β(5) = 5π⁵/1536`, `β(7) = 61π⁷/184320`). With `k = 2m + 2`:
`β(2m + 1) = π^{2m+1} |E_{2m}| / (2^{2m+2} (2m)!)`. Here `β` is the existing
`chapter7DirichletBeta`, the `L`-function of the nontrivial character mod `4`, which equals the
source's series `∑_{n ≥ 1} (-1)^{n-1}/(2n - 1)^s` for `Re s > 1` and is
its analytic continuation at `s = 1`, where the series converges only conditionally to the same
value. `E_{2m}` (OEIS A028296, the source's Euler numbers `1, -1, 5, -61, …`) is the existing
`chapter5EulerEven m`.

Source: Jan W. H. Swanepoel, *A Short Simple Probabilistic Proof of a Well Known Identity
and the Derivation of Related New Identities Involving the Bernoulli Numbers and the Euler
Numbers*, INTEGERS 25 (2025), Article A50, Proposition 3, Equation (12)
(`integers-2025-A50-prop-3`), citing its references [3], [6]. -/
public theorem_wanted dirichletBeta_two_mul_add_one (m : ℕ) :
    chapter7DirichletBeta (2 * m + 1) =
      (Real.pi : ℂ) ^ (2 * m + 1) * ((|chapter5EulerEven m| : ℤ) : ℂ) /
        (2 ^ (2 * m + 2) * ((2 * m).factorial : ℂ))

/-- Theorem 1 (Equation (1)): for every integer `k ≥ 1`,
`I_k = (1/π) ∫_0^∞ (sin x / x)^k dx = (1 / (2^k (k-1)!)) ∑_{i=0}^{⌊k/2⌋} (-1)^i C(k,i) (k - 2i)^(k-1)`.
The integral is taken as the improper limit `lim_{R → ∞} ∫_0^R` (for `k = 1` it converges only
conditionally), so the statement is `∫_0^R (sin x / x)^k dx → π I_k`.

Source: Jan W. H. Swanepoel, *A Short Simple Probabilistic Proof of a Well Known Identity
and the Derivation of Related New Identities Involving the Bernoulli Numbers and the Euler
Numbers*, INTEGERS 25 (2025), Article A50, Theorem 1 (`integers-2025-A50-thm-1`). -/
public theorem_wanted tendsto_integral_sinc_pow (k : ℕ) (hk : 1 ≤ k) :
    Filter.Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, (Real.sin x / x) ^ k) Filter.atTop
      (nhds (Real.pi * ((∑ i ∈ Finset.range (k / 2 + 1),
          (-1 : ℝ) ^ i * (k.choose i : ℝ) * ((k : ℝ) - 2 * i) ^ (k - 1)) /
        (2 ^ k * ((k - 1).factorial : ℝ)))))

/-- Proposition 4 (quoting Tuck): for `k ≥ 1`,
`∑_{n ≥ 1} sin^k(n t) / n^k = π t^(k-1) I_k - t^k / 2` for `0 < t < 2π` if `k = 1` and for
`0 ≤ t ≤ 2π/k` if `k ≥ 2`. Here `π I_k = L` is the improper integral
`lim_{R → ∞} ∫_0^R (sin x / x)^k dx`, supplied as a hypothesis, and the series is the limit of
its partial sums (for `k = 1` it converges only conditionally).

Source: Jan W. H. Swanepoel, *A Short Simple Probabilistic Proof of a Well Known Identity
and the Derivation of Related New Identities Involving the Bernoulli Numbers and the Euler
Numbers*, INTEGERS 25 (2025), Article A50, Proposition 4 (`integers-2025-A50-prop-4`), quoting its reference [18]. -/
public theorem_wanted tendsto_sum_sin_pow_div_pow (k : ℕ) (hk : 1 ≤ k) (t : ℝ)
    (ht₁ : k = 1 → 0 < t ∧ t < 2 * Real.pi) (ht₂ : 2 ≤ k → 0 ≤ t ∧ t ≤ 2 * Real.pi / k)
    (L : ℝ) (hL : Filter.Tendsto (fun R : ℝ => ∫ x in (0 : ℝ)..R, (Real.sin x / x) ^ k)
      Filter.atTop (nhds L)) :
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
        Real.sin ((n + 1 : ℝ) * t) ^ k / ((n : ℝ) + 1) ^ k) Filter.atTop
      (nhds (t ^ (k - 1) * L - t ^ k / 2))

end

end MetaMathlibExt
