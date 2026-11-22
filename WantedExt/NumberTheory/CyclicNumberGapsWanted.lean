/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.PrimeCounting
public import MathlibExt.NumberTheory.OppermannCyclicNumbers

/-!
# Cyclic numbers: counting function, moments and gaps

Statements from John M. Campbell and Joel E. Cohen, *Cyclic Numbers and Gaps*, INTEGERS 25
(2025), Article A23.

A positive integer `n` is cyclic when `gcd(n, φ(n)) = 1` (`MetaMathlibExt.IsCyclicNumber`).
The `n`-th cyclic number `c_n` (`c_1 = 1`) is `Nat.nth IsCyclicNumber (n - 1)`; `A(x)` counts
the cyclic numbers `≤ x` and `cc(x)` the composite cyclic numbers `≤ x`.  The `k`-th moment of
`c_1, …, c_n` is `μ'(c,n,k) = n⁻¹ (c_1^k + ⋯ + c_n^k)`, the mean is `m(c,n) = μ'(c,n,1)`, and
the variance is `v(c,n) = (n-1)⁻¹ ∑ (c_i - m(c,n))²`.
-/

open Asymptotics Filter Topology

namespace MetaMathlibExt

@[expose] public section

open Classical in
/-- Campbell and Cohen, Lemma 1: `A(x) ~ cc(x) ~ x e^{-γ} / log log log x` as `x → ∞`, where
`A(x)` counts cyclic numbers `≤ x` and `cc(x)` counts composite cyclic numbers `≤ x`.

Source: John M. Campbell and Joel E. Cohen, *Cyclic Numbers and Gaps*, INTEGERS 25 (2025),
Article A23, Lemma 1 (`integers-2025-A23-lem-1`). -/
public theorem_wanted cyclicCount_isEquivalent_compositeCyclicCount :
    let A : ℝ → ℝ := fun x => (((Finset.Icc 1 ⌊x⌋₊).filter IsCyclicNumber).card : ℝ)
    let cc : ℝ → ℝ := fun x =>
      (((Finset.Icc 1 ⌊x⌋₊).filter fun m => IsCyclicNumber m ∧ 1 < m ∧ ¬m.Prime).card : ℝ)
    IsEquivalent atTop A cc ∧
      IsEquivalent atTop cc (fun x => x * Real.exp (-Real.eulerMascheroniConstant) /
        Real.log (Real.log (Real.log x)))

open Classical in
/-- Campbell and Cohen, Theorem 1, regular variation: the counting functions `A(x)` of cyclic
numbers, `π(x) = pc(x)` of (prime cyclic numbers =) primes, and `cc(x)` of composite cyclic
numbers are regularly varying with index `1`, i.e. `F(λx)/F(x) → λ` as `x → ∞` for every
`λ > 0`.

Source: John M. Campbell and Joel E. Cohen, *Cyclic Numbers and Gaps*, INTEGERS 25 (2025),
Article A23, Theorem 1 (`integers-2025-A23-thm-1`). -/
public theorem_wanted cyclicCountingFunctions_regularlyVarying_index_one :
    let A : ℝ → ℝ := fun x => (((Finset.Icc 1 ⌊x⌋₊).filter IsCyclicNumber).card : ℝ)
    let piFun : ℝ → ℝ := fun x => (Nat.primeCounting ⌊x⌋₊ : ℝ)
    let cc : ℝ → ℝ := fun x =>
      (((Finset.Icc 1 ⌊x⌋₊).filter fun m => IsCyclicNumber m ∧ 1 < m ∧ ¬m.Prime).card : ℝ)
    ∀ lam : ℝ, 0 < lam →
      Tendsto (fun x => A (lam * x) / A x) atTop (𝓝 lam) ∧
      Tendsto (fun x => piFun (lam * x) / piFun x) atTop (𝓝 lam) ∧
      Tendsto (fun x => cc (lam * x) / cc x) atTop (𝓝 lam)

/-- Campbell and Cohen, Theorem 1, display (5) (Taylor's law): `v(c,n) / m(c,n)^b` tends to
`∞` if `b < 2`, to `1/3` if `b = 2`, and to `0` if `b > 2`.

Source: John M. Campbell and Joel E. Cohen, *Cyclic Numbers and Gaps*, INTEGERS 25 (2025),
Article A23, Theorem 1 (`integers-2025-A23-thm-1`). -/
public theorem_wanted cyclicNumbers_variance_div_mean_rpow_tendsto :
    let c : ℕ → ℝ := fun n => (Nat.nth IsCyclicNumber (n - 1) : ℝ)
    let mean : ℕ → ℝ := fun n => (∑ i ∈ Finset.Icc 1 n, c i) / n
    let var : ℕ → ℝ := fun n => (∑ i ∈ Finset.Icc 1 n, (c i - mean n) ^ 2) / (n - 1)
    ∀ b : ℝ,
      (b < 2 → Tendsto (fun n => var n / mean n ^ b) atTop atTop) ∧
      (b = 2 → Tendsto (fun n => var n / mean n ^ b) atTop (𝓝 (1 / 3))) ∧
      (2 < b → Tendsto (fun n => var n / mean n ^ b) atTop (𝓝 0))

/-- Campbell and Cohen, Theorem 1, mean and variance: `m(c,n) ~ c_n / 2` and
`v(c,n) ~ c_n^2 / 12` as `n → ∞`.

Source: John M. Campbell and Joel E. Cohen, *Cyclic Numbers and Gaps*, INTEGERS 25 (2025),
Article A23, Theorem 1 (`integers-2025-A23-thm-1`). -/
public theorem_wanted cyclicNumbers_mean_variance_isEquivalent :
    let c : ℕ → ℝ := fun n => (Nat.nth IsCyclicNumber (n - 1) : ℝ)
    let mean : ℕ → ℝ := fun n => (∑ i ∈ Finset.Icc 1 n, c i) / n
    let var : ℕ → ℝ := fun n => (∑ i ∈ Finset.Icc 1 n, (c i - mean n) ^ 2) / (n - 1)
    IsEquivalent atTop mean (fun n => c n / 2) ∧
      IsEquivalent atTop var (fun n => c n ^ 2 / 12)

/-- Campbell and Cohen, Theorem 1, relation between moments: for `j ≥ 1` and every `k`,
`μ'(c,n,k) ~ (j+1)^{k/j} / (k+1) · μ'(c,n,j)^{k/j}` as `n → ∞`.

Source: John M. Campbell and Joel E. Cohen, *Cyclic Numbers and Gaps*, INTEGERS 25 (2025),
Article A23, Theorem 1 (`integers-2025-A23-thm-1`). -/
public theorem_wanted cyclicNumbers_moment_isEquivalent_moment_rpow (j k : ℕ) (hj : 1 ≤ j) :
    let c : ℕ → ℝ := fun n => (Nat.nth IsCyclicNumber (n - 1) : ℝ)
    let μ : ℕ → ℕ → ℝ := fun n k => (∑ i ∈ Finset.Icc 1 n, c i ^ k) / n
    IsEquivalent atTop (fun n => μ n k)
      (fun n => ((j : ℝ) + 1) ^ ((k : ℝ) / j) / (k + 1) * μ n j ^ ((k : ℝ) / j))

/-- Campbell and Cohen, Theorem 1, generalized Taylor's law: for every `k`,
`μ'(c,n,k) ~ 2^k / (1+k) · m(c,n)^k` as `n → ∞`.

Source: John M. Campbell and Joel E. Cohen, *Cyclic Numbers and Gaps*, INTEGERS 25 (2025),
Article A23, Theorem 1 (`integers-2025-A23-thm-1`). -/
public theorem_wanted cyclicNumbers_moment_isEquivalent_mean_pow (k : ℕ) :
    let c : ℕ → ℝ := fun n => (Nat.nth IsCyclicNumber (n - 1) : ℝ)
    let mean : ℕ → ℝ := fun n => (∑ i ∈ Finset.Icc 1 n, c i) / n
    IsEquivalent atTop (fun n : ℕ => (∑ i ∈ Finset.Icc 1 n, c i ^ k) / n)
      (fun n => (2 : ℝ) ^ k / (1 + k) * mean n ^ k)

/-- Campbell and Cohen, Theorem 2: under the Riemann hypothesis, the gaps
`d_n = c_{n+1} - c_n` between consecutive cyclic numbers satisfy `d_n = o(√p_n log p_n)`,
where `p_n` is the `n`-th prime.

Source: John M. Campbell and Joel E. Cohen, *Cyclic Numbers and Gaps*, INTEGERS 25 (2025),
Article A23, Theorem 2 (`integers-2025-A23-thm-2`). -/
public theorem_wanted cyclicNumber_gap_isLittleO_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    let c : ℕ → ℝ := fun n => (Nat.nth IsCyclicNumber (n - 1) : ℝ)
    let p : ℕ → ℝ := fun n => (Nat.nth Nat.Prime (n - 1) : ℝ)
    (fun n => c (n + 1) - c n) =o[atTop] (fun n => Real.sqrt (p n) * Real.log (p n))

end

end MetaMathlibExt
