/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Ball-shaped minimizers of a flocking energy (Oberwolfach Reports 43/2016)

Oberwolfach workshop Many-Body Quantum Systems and Effective Theories (2016), R. L. Frank (with E.
H. Lieb): for `E_α[ρ] = ½ ∬ ρ(x)(|x - y|⁻¹ + |x - y|^α) ρ(y) dx dy` on `ℝ³`, is there `m_c(α) < ∞`
such that for `m > m_c(α)` every minimizer among `0 ≤ ρ ≤ 1`, `∫ ρ = m`, is the characteristic
function of a ball of volume `m`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

namespace MathlibExt.Analysis.FlockingMinimizerBallOWR14751Problem005Wanted

/-!
Source: R. L. Frank (with E. H. Lieb), in Many-Body Quantum Systems and Effective Theories,
Oberwolfach Reports 13 (2016), no. 43, p. 2506, DOI 10.4171/OWR/2016/43. UnsolvedMath record
UM-30003221 (`OWR-14751-005`), dataset ulamai/UnsolvedMath v1.8.0.

The energy is a lower Lebesgue integral in `[0, ∞]` (the integrand is nonnegative; the diagonal is a
null set), so every admissible density has a well-defined energy. A ball of volume `m` is written as
an open ball with `ρ` equal to its indicator almost everywhere (its volume is forced by `∫ ρ = m`).
-/

open MeasureTheory
open scoped ENNReal

/-- The energy `E_α[ρ] = ½ ∬ ρ(x) (|x - y|⁻¹ + |x - y|^α) ρ(y) dx dy ∈ [0, ∞]` of a density `ρ ≥ 0`
on `ℝ³`, as a lower Lebesgue integral (the diagonal `x = y` is a null set). -/
noncomputable def energy (α : ℝ) (ρ : EuclideanSpace ℝ (Fin 3) → ℝ) : ℝ≥0∞ :=
  2⁻¹ * ∫⁻ x, ∫⁻ y, ENNReal.ofReal (ρ x * (‖x - y‖⁻¹ + ‖x - y‖ ^ α) * ρ y)

/-- An admissible density of mass `m`: measurable, `0 ≤ ρ ≤ 1` and `∫ ρ = m`. -/
def IsAdmissible (m : ℝ) (ρ : EuclideanSpace ℝ (Fin 3) → ℝ) : Prop :=
  Measurable ρ ∧ (∀ x, 0 ≤ ρ x ∧ ρ x ≤ 1) ∧ ∫⁻ x, ENNReal.ofReal (ρ x) = ENNReal.ofReal m

/-- `ρ` minimizes `E_α` among the admissible densities of mass `m`. -/
def IsMinimizer (α m : ℝ) (ρ : EuclideanSpace ℝ (Fin 3) → ℝ) : Prop :=
  IsAdmissible m ρ ∧ ∀ σ, IsAdmissible m σ → energy α ρ ≤ energy α σ

/-- The question of Frank and Lieb (Oberwolfach Report 43/2016, p. 2506): for every `α > 0` there is
`m_c(α) < ∞` such that for every mass `m > m_c(α)` every minimizer of `E_α` among densities
`0 ≤ ρ ≤ 1` on `ℝ³` with `∫ ρ = m` is (almost everywhere) the characteristic function of a ball. -/
def largeMassMinimizersAreBalls : Prop :=
  ∀ α : ℝ, 0 < α → ∃ M : ℝ, ∀ m : ℝ, M < m → ∀ ρ, IsMinimizer α m ρ →
    ∃ (c : EuclideanSpace ℝ (Fin 3)) (r : ℝ), ρ =ᵐ[volume] (Metric.ball c r).indicator 1

/--
Resolved true: Frank and Lieb proved (Theorem 1) that for `0 < λ < N - 1` and `α > 0`, for all large
masses `m` the only minimizers of `½ ∬ ρ(x)(|x - y|^α + |x - y|^{-λ}) ρ(y) dx dy` under `0 ≤ ρ ≤ 1`,
`∫ ρ = m` on `ℝ^N` are characteristic functions of balls, up to null sets; here `N = 3`, `λ = 1`.
Before, only `α = 2` and `2 < α ≤ 4` were known. Source: R. L. Frank (with E. H. Lieb), in Many-Body
Quantum Systems and Effective Theories, Oberwolfach Reports 13 (2016), no. 43, p. 2506, DOI
10.4171/OWR/2016/43; resolution: R. L. Frank and E. H. Lieb, Proof of spherical flocking based on
quantitative rearrangement inequalities, Ann. Sc. Norm. Super. Pisa Cl. Sci. (2021),
arXiv:1909.04595, Theorem 1: for 0 < λ < N - 1 and α > 0 there is m_{N,α,λ} < ∞ such that for all m
> m_{N,α,λ} the only minimizers for E_{α,λ}(m) are characteristic functions of balls (up to sets of
measure zero); here N = 3, λ = 1, https://arxiv.org/abs/1909.04595.
-/
public theorem_wanted largeMassMinimizersAreBalls_holds : largeMassMinimizersAreBalls

end MathlibExt.Analysis.FlockingMinimizerBallOWR14751Problem005Wanted
