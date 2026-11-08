/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import MathlibExt.NumberTheory.MultipleZeta.Series

namespace MetaMathlibExt

@[expose] public section

/-- Faà di Bruno's formula for Taylor coefficients: writing `Tₙ(f; a) = f⁽ⁿ⁾(a) / n!`,
`Tₙ(f ∘ g; a) = ∑_{π ∈ P(n)} (l(π) choose π₁, …, πₙ) · T_{l(π)}(f; g(a)) · ∏_{i=1}^{n} Tᵢ(g; a)^{πᵢ}`,
where a partition `π` of `n` is described by the multiplicities `πᵢ` of its parts `i`,
`l(π) = π₁ + ⋯ + πₙ` is its number of parts, and the multinomial coefficient is
`l(π)! / (π₁! ⋯ πₙ!)`. The hypothesis "`f` and `g` have `n`th derivatives" is read as
`f` being `Cⁿ` near `g(a)` and `g` being `Cⁿ` near `a` (`ContDiffAt ℝ n`), so that Mathlib's
`iteratedDeriv` is the classical `n`th derivative; real functions of a real variable.

Source: Serge Iovleff, *About Some Nested Sums of Reciprocal Squared Numbers*, INTEGERS 26
(2026), Article A114, Corollary 1 (quoted as Corollary 4 from the paper's reference [8]). -/
public theorem_wanted taylorCoeff_comp_eq_sum_partitions (f g : ℝ → ℝ) (a : ℝ) (n : ℕ)
    (hf : ContDiffAt ℝ n f (g a)) (hg : ContDiffAt ℝ n g a) :
    iteratedDeriv n (f ∘ g) a / n.factorial =
      ∑ π : Nat.Partition n,
        ((π.parts.card.factorial : ℝ) /
            ∏ i ∈ Finset.Icc 1 n, ((π.parts.count i).factorial : ℝ)) *
          (iteratedDeriv π.parts.card f (g a) / π.parts.card.factorial) *
          ∏ i ∈ Finset.Icc 1 n, (iteratedDeriv i g a / i.factorial) ^ π.parts.count i

/-- **Nested sums of reciprocal odd squares** (Iovleff's `R₁(k)`): for every `k ≥ 0`,
`R₁(k) = ∑_{1 ≤ i_k ≤ ⋯ ≤ i_1} ∏_j (2 i_j - 1)^{-2} = (π/2)^{2k} E*_{2k} / (2k)!`, where the
Euler (zig) number `E*_{2k}` (OEIS A000364) is written as the Taylor data
`sec^{(2k)}(0)` of `sec x = 1 / cos x`. The nesting `i_1 ≥ i_2 ≥ ⋯ ≥ i_k ≥ 1` ranges over the
weakly decreasing positive tuples `MultipleZeta.WeaklyDecreasingTuple k` (the summation domain
of `MultipleZeta.starValue`); for `k = 0` the sum is `1` (the paper's convention `R(0) = 1`).
The paper's second equality `R₁(k) = (π/4) β(2k + 1)` is false as printed and is not
stated: at `k = 0`, `R₁(0) = 1` but `(π/4) β(1) = π²/16`; at `k = 1`, `R₁(1) = π²/8` but
`(π/4) β(3) = π⁴/128` (the correct factor is `4/π`).

Source: Serge Iovleff, *About Some Nested Sums of Reciprocal Squared Numbers*, INTEGERS 26
(2026), Article A114, Theorem 1. -/
public theorem_wanted tsum_weaklyDecreasing_prod_inv_odd_sq_eq (k : ℕ) :
    ∑' m : MultipleZeta.WeaklyDecreasingTuple k,
        ∏ j, ((2 * ((m.1 j : ℕ) : ℝ) - 1) ^ 2)⁻¹ =
      (Real.pi / 2) ^ (2 * k) * iteratedDeriv (2 * k) (fun x => (Real.cos x)⁻¹) 0 /
        (2 * k).factorial

/-- **Nested sums of reciprocal squares** (Iovleff's `R₀(k) = ζ*({2}^k)`): for every `k ≥ 0`,
`ζ*({2}^k) = 2 π^{2k} |(2^{2k-1} - 1) B_{2k}| / (2k)! = 2 η(2k)`, with the multiple-zeta-star
value `MultipleZeta.starValue` at the all-two index `MultipleZeta.Index.replicate k 2` and
Dirichlet's `η(s) = (1 - 2^{1-s}) ζ(s)` written through `riemannZeta` (valid also at `s = 0`).
For `k = 0` both sides are `1`.

Source: Serge Iovleff, *About Some Nested Sums of Reciprocal Squared Numbers*, INTEGERS 26
(2026), Article A114, Theorem 2. -/
public theorem_wanted starValue_replicate_two_eq (k : ℕ) :
    MultipleZeta.starValue (MultipleZeta.Index.replicate k 2)
        (MultipleZeta.Index.replicate_isAdmissibleOrEmpty k le_rfl) =
        2 * Real.pi ^ (2 * k) * |((2 : ℝ) ^ ((2 * k : ℤ) - 1) - 1) * bernoulli (2 * k)| /
          (2 * k).factorial ∧
      ((MultipleZeta.starValue (MultipleZeta.Index.replicate k 2)
          (MultipleZeta.Index.replicate_isAdmissibleOrEmpty k le_rfl) : ℝ) : ℂ) =
        2 * ((1 - (2 : ℂ) ^ ((1 : ℤ) - 2 * k)) * riemannZeta (2 * k))

/-- **Strictly nested sums of reciprocal odd squares** (Iovleff's `A₁(k)`):
`A₁(k) = ∑_{1 ≤ i_1 < ⋯ < i_k} ∏_j (2 i_j - 1)^{-2} = (π/2)^{2k} / (2k)!`. The paper states
`k > 0`; the identity also holds at `k = 0` (empty sum convention `A₁(0) = 1`, used in the
paper's proof), so `k > 0` is not assumed. The strictly nested positive indices are listed in
decreasing order as `MultipleZeta.StrictDecreasingTuple k` (the summation domain of
`MultipleZeta.strictValue`); the summand is symmetric, so the order does not matter.

Source: Serge Iovleff, *About Some Nested Sums of Reciprocal Squared Numbers*, INTEGERS 26
(2026), Article A114, Corollary 2. -/
public theorem_wanted tsum_strictDecreasing_prod_inv_odd_sq_eq (k : ℕ) :
    ∑' m : MultipleZeta.StrictDecreasingTuple k,
        ∏ j, ((2 * ((m.1 j : ℕ) : ℝ) - 1) ^ 2)⁻¹ =
      (Real.pi / 2) ^ (2 * k) / (2 * k).factorial

end

end MetaMathlibExt
