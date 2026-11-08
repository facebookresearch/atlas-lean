/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem #690: unimodality of the k-th prime-factor density

For fixed `k ≥ 1`, is `dₖ(p)` (the density of integers whose `k`-th
smallest prime factor is `p`) unimodal in the prime `p`?
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.PrimeFin
public import MathlibExt.Data.Set.Density
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosProblem690Wanted

/-- `IsKthSmallestPrimeFactor k n p`: `p` is the `k`-th smallest prime
factor of `n` (`p ∈ primeFactors n` with exactly `k - 1` prime factors
below `p`). -/
def IsKthSmallestPrimeFactor (k n p : ℕ) : Prop :=
  p ∈ Nat.primeFactors n ∧
    ((Nat.primeFactors n).filter (fun q => q < p)).card = k - 1

/-- Natural (asymptotic) density of a set of naturals: the canonical
`Set.HasDensity` from `MathlibExt.Data.Set.Density` (default ambient set);
for naturals it is the limit of `|S ∩ [0, N)| / N`.
`dₖ(p)`: the density of integers whose `k`-th smallest prime factor
is `p`, chosen by Hilbert choice (the unique limit when it exists). -/
noncomputable def kthPrimeFactorDensity (k p : ℕ) : ℝ :=
  Classical.epsilon (fun d : ℝ =>
    Set.HasDensity {n : ℕ | IsKthSmallestPrimeFactor k n p} d)

/-- Unimodality in the prime argument: nondecreasing up to a prime peak
`p₀`, nonincreasing after it. -/
def IsUnimodalOnPrimes (f : ℕ → ℝ) : Prop :=
  ∃ p₀ : ℕ, p₀.Prime ∧
    (∀ p q : ℕ, p.Prime → q.Prime → p ≤ q → q ≤ p₀ → f p ≤ f q) ∧
    (∀ p q : ℕ, p.Prime → q.Prime → p₀ ≤ p → p ≤ q → f q ≤ f p)

/-- Erdős Problem #690: for every fixed `k ≥ 1`, `dₖ(p)` is unimodal
in the prime `p`. -/
def conjecture : Prop :=
  ∀ k : ℕ, 1 ≤ k → IsUnimodalOnPrimes (kthPrimeFactorDensity k)

/--
Resolved false: Cambie (arXiv:2501.10333, 2025), Theorem 5, proves d_k(p) unimodal for k=1,2,3
and not unimodal for 4≤k≤20; e.g. d_4(13)=31/5005 > d_4(17)=206/36465 < d_4(19)=1308/230945, so
the Lean statement for all k≥1 is false at k=4. Source: S. Cambie, Resolution of Erdős' problems
about unimodularity, arXiv preprint (2025), arXiv:2501.10333, https://arxiv.org/abs/2501.10333.
Moved from `OpenConjectures/NumberTheory/ErdosProblem690`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.NumberTheory.ErdosProblem690Wanted
