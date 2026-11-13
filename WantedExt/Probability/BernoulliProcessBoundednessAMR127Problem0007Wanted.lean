/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Talagrand's Bernoulli conjecture (O'Donnell, Problem 8)

R. O'Donnell, Open Problems in Analysis of Boolean Functions, Problem 8 (Bernoulli Conjecture): let
`T` be a finite collection of vectors in `ℝⁿ`, `b(T) = E_{x ∼ {-1,1}ⁿ}[max_{t ∈ T} ⟨t, x⟩]` and
`g(T)` the same with `x` Gaussian. Then there is a finite collection `T'` with `g(T') ≤ O(b(T))` and
`∀ t ∈ T ∃ t' ∈ T', ‖t - t'‖₁ ≤ O(b(T))`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

namespace MathlibExt.Probability.BernoulliProcessBoundednessAMR127Problem0007Wanted

/-!
Source: R. O'Donnell, Open Problems in Analysis of Boolean Functions (2012), arXiv:1204.6447,
Problem 8 (Bernoulli Conjecture). UnsolvedMath record UM-00800438 (`AMR-127-0007`), dataset
ulamai/UnsolvedMath v1.8.0.

`O(·)` is a universal constant `L` (independent of `n` and `T`). `T` and `T'` are finite nonempty
subsets of `ℝⁿ` (a maximum over the empty set is undefined); `b(T)` is the average over the `2ⁿ`
sign vectors and `g(T)` the integral against the standard Gaussian measure on `ℝⁿ` (the maximum of
finitely many linear functions is integrable). Bednorz and Latała state the theorem for `T ⊆ ℓ²(I)`,
`I` countable, as a decomposition `T ⊆ T₁ + T₂` with `sup_{T₁} ‖t‖₁ ≤ L b(T)` and `g(T₂) ≤ L b(T)`;
O'Donnell's form is the case `I = {1, …, n}` with `T'` the `T₂`-parts of the points of `T` (a subset
of `T₂`, so `g(T') ≤ g(T₂)`).
-/

/-- `b(T) = E_x max_{t ∈ T} ⟨t, x⟩` for `x` uniform on `{-1, 1}ⁿ` (`true` read as `1`). -/
noncomputable def bernoulliSup {n : ℕ} (T : Finset (Fin n → ℝ)) (hT : T.Nonempty) : ℝ :=
  (∑ x : Fin n → Bool, T.sup' hT fun t => ∑ i, t i * (if x i then (1 : ℝ) else -1)) / 2 ^ n

/-- `g(T) = E_x max_{t ∈ T} ⟨t, x⟩` for `x` a standard Gaussian vector in `ℝⁿ`. -/
noncomputable def gaussianSup {n : ℕ} (T : Finset (Fin n → ℝ)) (hT : T.Nonempty) : ℝ :=
  ∫ x, T.sup' hT (fun t => ∑ i, t i * x i)
    ∂(MeasureTheory.Measure.pi fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)

/-- Talagrand's Bernoulli conjecture in O'Donnell's form (Problem 8): there is a universal
constant `L` such that for every finite nonempty `T ⊆ ℝⁿ` there is a finite nonempty `T' ⊆ ℝⁿ` with
`g(T') ≤ L b(T)` and every `t ∈ T` within `ℓ¹`-distance `L b(T)` of some `t' ∈ T'`. -/
def bernoulliConjecture : Prop :=
  ∃ L : ℝ, ∀ (n : ℕ) (T : Finset (Fin n → ℝ)) (hT : T.Nonempty),
    ∃ (T' : Finset (Fin n → ℝ)) (hT' : T'.Nonempty), gaussianSup T' hT' ≤ L * bernoulliSup T hT ∧
      ∀ t ∈ T, ∃ t' ∈ T', ∑ i, |t i - t' i| ≤ L * bernoulliSup T hT

/--
Resolved true: Bednorz and Latała proved Talagrand's Bernoulli conjecture: every `T` with `b(T) < ∞`
decomposes as `T ⊆ T₁ + T₂` with `sup_{T₁} ‖t‖₁ ≤ L b(T)` and `g(T₂) ≤ L b(T)` for a universal `L`;
for finite `T ⊆ ℝⁿ` the `T₂`-parts of the points of `T` form the required `T'`. Source: R.
O'Donnell, Open Problems in Analysis of Boolean Functions (2012), arXiv:1204.6447, Problem 8
(Bernoulli Conjecture); resolution: W. Bednorz and R. Latała, On the boundedness of Bernoulli
processes, Ann. of Math. (2) 180 (2014), 1167-1203, arXiv:1305.4292, Theorem 1.1: for any T ⊆ ℓ²(I)
with b(T) < ∞ there is a decomposition T ⊆ T₁ + T₂ with sup_{t ∈ T₁} ∑ |tᵢ| ≤ L b(T) and g(T₂) ≤ L
b(T), L a universal constant (the "positive solution to the so-called Bernoulli Conjecture"),
https://arxiv.org/abs/1305.4292.
-/
public theorem_wanted bernoulliConjecture_holds : bernoulliConjecture

end MathlibExt.Probability.BernoulliProcessBoundednessAMR127Problem0007Wanted
