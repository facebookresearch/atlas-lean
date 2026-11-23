/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Fibers of infinite Blaschke products near zero (Hayman–Lingham Problem 5.66)

W. K. Hayman and E. F. Lingham, Research Problems in Function Theory, Problem 5.66 (K. Stephenson):
let `B` be an infinite Blaschke product in `𝔻`. Does there exist a positive `δ`, depending on `B`,
such that, for every `w`, `|w| < δ`, the set `B⁻¹({w})` is infinite?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes

@[expose] public section

namespace MathlibExt.Analysis.BlaschkeProductFiberAMR22Problem5066Wanted

/-!
Source: W. K. Hayman and E. F. Lingham, Research Problems in Function Theory, Fiftieth Anniversary
Edition (2019), arXiv:1809.07200, Problem 5.66 (K. Stephenson). UnsolvedMath record UM-02305066
(`AMR-022-5066`), dataset ulamai/UnsolvedMath v1.8.0.

An infinite Blaschke product is `B(z) = c zᵐ ∏ₙ (|aₙ|/aₙ)(aₙ - z)/(1 - āₙ z)` with `|c| = 1`,
infinitely many nonzero zeros `aₙ ∈ 𝔻` (listed with multiplicity, indexed by `ℕ`) and `∑ (1 - |aₙ|)
< ∞`; the product is Mathlib's `tprod`, which converges unconditionally on `𝔻` under the Blaschke
condition. `B⁻¹({w})` is taken inside `𝔻`. The question asks whether every infinite Blaschke product
`B` admits such a `δ = δ(B) > 0`; the target is the negation of that claim.
-/

open Metric

/-- The Blaschke factor with zero `a`: `b_a(z) = (|a| / a) (a - z) / (1 - ā z)`. -/
noncomputable def blaschkeFactor (a z : ℂ) : ℂ :=
  (‖a‖ / a) * ((a - z) / (1 - (starRingEnd ℂ) a * z))

/-- The Blaschke product `B(z) = c zᵐ ∏ₙ b_{aₙ}(z)` with zeros `aₙ` (and a zero of order `m` at the
origin). -/
noncomputable def blaschkeProduct (c : ℂ) (m : ℕ) (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  c * z ^ m * ∏' n, blaschkeFactor (a n) z

/-- The data of an infinite Blaschke product: a unimodular constant `c` and infinitely many nonzero
zeros `aₙ` in the unit disc (listed with multiplicity) satisfying the Blaschke condition
`∑ₙ (1 - |aₙ|) < ∞`. -/
def IsInfiniteBlaschkeData (c : ℂ) (a : ℕ → ℂ) : Prop :=
  ‖c‖ = 1 ∧ (∀ n, a n ≠ 0 ∧ ‖a n‖ < 1) ∧ Summable fun n => 1 - ‖a n‖

/-- Stephenson's question (Hayman–Lingham Problem 5.66): for every infinite Blaschke product `B` in
the unit disc there is `δ > 0` such that `B⁻¹({w})` is infinite for every `|w| < δ`. -/
def blaschkeFibersInfiniteNearZero : Prop :=
  ∀ (c : ℂ) (m : ℕ) (a : ℕ → ℂ), IsInfiniteBlaschkeData c a →
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, ‖w‖ < δ →
      {z | z ∈ ball (0 : ℂ) 1 ∧ blaschkeProduct c m a z = w}.Infinite

/--
Resolved false (an unpublished, unrefereed construction; the list's Update 5.66 records it as the
answer): Stephenson's inner function `f` has finite fibers `f⁻¹(w)` for a dense set of `|w| < 1`,
and its Frostman shifts `f_α = (f - α)/(1 - ᾱ f)` are Blaschke products for almost all `α`; such an
`f_α` is an infinite Blaschke product with finite fibers over a dense set of `w`. Source: W. K.
Hayman and E. F. Lingham, Research Problems in Function Theory, Fiftieth Anniversary Edition (2019),
arXiv:1809.07200, Problem 5.66 (K. Stephenson); resolution: W. K. Hayman and E. F. Lingham, Research
Problems in Function Theory, Fiftieth Anniversary Edition (2019), arXiv:1809.07200, Update 5.66 (K.
Stephenson, unpublished), Update 5.66: 'Stephenson (unpublished) has answered this question
negatively by constructing an inner function f such that f^{-1}(w) is finite on a dense subset of
|w| < 1. Then f_α = (f − α)/(1 − ᾱ f) is a Blaschke product for almost all α',
https://arxiv.org/abs/1809.07200.
-/
public theorem_wanted blaschkeFibersInfiniteNearZero_refuted : ¬ blaschkeFibersInfiniteNearZero

end MathlibExt.Analysis.BlaschkeProductFiberAMR22Problem5066Wanted
