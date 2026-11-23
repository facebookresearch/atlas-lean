/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Semiadditivity of analytic capacity (Hayman-Lingham Problem 7.39)

Hayman-Lingham, Research Problems in Function Theory, Problem 7.39 (J. Korevaar): prove or disprove
the existence of a constant `M` such that `γ(K₁ ∪ K₂) ≤ M (γ(K₁) + γ(K₂))` for all compact sets `K₁,
K₂` in `ℂ`, where `γ` is analytic capacity.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace MathlibExt.Analysis.AnalyticCapacitySemiadditivityAMR22Problem7039Wanted

/-!
Source: W. K. Hayman and E. F. Lingham, Research Problems in Function Theory, Fiftieth Anniversary
Edition (2019), arXiv:1809.07200, Problem 7.39 (J. Korevaar). UnsolvedMath record UM-02307039
(`AMR-022-7039`), dataset ulamai/UnsolvedMath v1.8.0.

Analytic capacity is `γ(K) = sup |f'(∞)|` over the functions `f` holomorphic on `ℂ \ K` with `|f| ≤
1` and `f(z) → 0` as `z → ∞`, where `f'(∞) = lim_{z → ∞} z f(z)`, valued in `ℝ≥0∞` (the definition
of `OpenConjectures/Analysis/AnalyticCapacityExactSubadditivity`, which states the open case `M =
1`, with the normalization `f(∞) = 0`).
-/

open Filter Topology
open scoped ENNReal NNReal

/-- The derivatives at infinity `f'(∞) = lim_{z → ∞} z f(z)` of the analytic functions `f` on
`ℂ \ K` with `|f| ≤ 1` and `f(∞) = 0`. -/
def derivativesAtInfinity (K : Set ℂ) : Set ℂ :=
  {a | ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Kᶜ ∧ (∀ z ∉ K, ‖f z‖ ≤ 1) ∧
    Tendsto f (cocompact ℂ) (𝓝 0) ∧ Tendsto (fun z => z * f z) (cocompact ℂ) (𝓝 a)}

/-- The analytic capacity `γ(K) = sup |f'(∞)|`. -/
noncomputable def analyticCapacity (K : Set ℂ) : ℝ≥0∞ :=
  ⨆ a : derivativesAtInfinity K, (‖(a : ℂ)‖₊ : ℝ≥0∞)

/-- The subadditivity problem for analytic capacity, with a positive answer: there is a constant
`M` with `γ(K₁ ∪ K₂) ≤ M (γ(K₁) + γ(K₂))` for all compact `K₁, K₂ ⊆ ℂ` (semiadditivity). -/
def analyticCapacitySemiadditive : Prop :=
  ∃ M : ℝ≥0, ∀ K₁ K₂ : Set ℂ, IsCompact K₁ → IsCompact K₂ →
    analyticCapacity (K₁ ∪ K₂) ≤ M * (analyticCapacity K₁ + analyticCapacity K₂)

/--
Resolved true: Tolsa proves that analytic capacity is semiadditive, `γ(E ∪ F) ≤ C (γ(E) + γ(F))` for
compact `E, F ⊆ ℂ` with an absolute constant `C`; Hayman and Lingham record (Update 7.39) that the
problem has been proved by Tolsa. Source: W. K. Hayman and E. F. Lingham, Research Problems in
Function Theory, Fiftieth Anniversary Edition (2019), arXiv:1809.07200, Problem 7.39 (J. Korevaar);
resolution: X. Tolsa, Painlevé's problem and the semiadditivity of analytic capacity, Acta Math. 190
(2003), 105-149; arXiv:math/0204027, abstract: γ(E) ≈ γ₊(E) with constants independent of E, and as
a corollary γ is semiadditive; Hayman-Lingham, Update 7.39: 'This has been proved by Tolsa',
https://doi.org/10.1007/BF02393237.
-/
public theorem_wanted analyticCapacitySemiadditive_holds : analyticCapacitySemiadditive

end MathlibExt.Analysis.AnalyticCapacitySemiadditivityAMR22Problem7039Wanted
