/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Diffusion.PathFunctionals
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Basic.NNReal.Defs
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Probability.Process.Filtration
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Separation.Hausdorff

/-!
# Squared heterozygosity occupation until absorption

Expected sums of a function of gene frequency along sample paths are obtained from the
ordinary differential equation `L{Y(p)} + K(p) = 0`; under the boundary conditions
`Y(0) = Y(1) = 0` the solution is the Green formula. This functional programme is due to
T. Maruyama and M. Kimura, "Moments for Sum of an Arbitrary Function of Gene Frequency
along a Stochastic Path of Gene Frequency Change", Proc. Nat. Acad. Sci. USA 72(4),
1602-1604 (1975). These are the forward (until absorption) statements in diffusion units,
not their retrospective Eq. 21 and not a count in generations or individuals.

Conventions follow `Domains.Biology.PopulationGenetics.Diffusion.WrightFisher`: diploid
population of `N` individuals (`2N` gene copies), diffusion time in units of `2N`
generations, ideal population `N_e = N`, and the neutral backward generator `generator 0`
with coefficient `x (1 - x) / 2` on the second derivative. For the squared heterozygosity
function `g(y) = (2y(1-y))^2`, the potential `u(y) = (2/3) y(1-y)(1+y-y^2)` satisfies
`u(0) = u(1) = 0` and `generator 0 u = -g`, since `u''(y) = -8y(1-y)`; so the Green/Dynkin
value from initial frequency `x` is `(2/3) x(1-x)(1+x-x^2)` in diffusion time units.

This is the expected occupation of the squared heterozygosity integrand, not the second
moment of the accumulated heterozygosity functional; the latter is not claimed here.

## Main results

* `generator_zero_heterozygositySqPotential`: `generator 0` maps the potential
  `u(z) = (2/3) z(1-z)(1+z-z^2)` to `-(2y(1-y))^2`, pointwise in `y`.
* `integral_sq_two_mul_one_sub_absorptionTime`: for any neutral solution started at `x`,
  the stopped squared-heterozygosity integral is integrable and its mean is
  `(2/3) x(1-x)(1+x-x^2)`.
* `integral_sq_two_mul_one_sub_absorptionTime_modifiedProcess`: the same identity for the
  constructed neutral realization `modifiedProcess x` under `rawMeasure x`.

## References

* T. Maruyama and M. Kimura, *Moments for Sum of an Arbitrary Function of Gene Frequency
  along a Stochastic Path of Gene Frequency Change*, Proc. Nat. Acad. Sci. USA 72(4),
  1602-1604 (1975), doi:10.1073/pnas.72.4.1602.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal unitInterval

open MathlibExt.Biology.PopulationGenetics.Diffusion (generator)
open MathlibExt.Biology.PopulationGenetics.Diffusion.KimuraFixationProcess
  (IsWrightFisherSolution absorptionTime)
open MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralWrightFisherRaw
  (modifiedProcess rawMeasure)

namespace MathlibExt.Biology.PopulationGenetics.Diffusion

private theorem hasDerivAt_sqPotential_first (z : ℝ) :
    HasDerivAt (fun z => (2 / 3) * z * (1 - z) * (1 + z - z ^ 2))
      ((2 / 3) * (1 - 6 * z ^ 2 + 4 * z ^ 3)) z := by
  convert ((((hasDerivAt_id' z).const_mul (2 / 3)).mul
    ((hasDerivAt_id' z).const_sub 1)).mul
    (((hasDerivAt_const (c := (1 : ℝ)) (x := z)).add (hasDerivAt_id' z)).sub
      (hasDerivAt_pow 2 z))) using 1
  simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply,
    show (2 - 1 : ℕ) = 1 from rfl]
  ring

private theorem hasDerivAt_sqPotential_second (y : ℝ) :
    HasDerivAt (fun z : ℝ => (2 / 3) * (1 - 6 * z ^ 2 + 4 * z ^ 3))
      (-8 * y * (1 - y)) y := by
  convert (((((hasDerivAt_pow 2 y).const_mul 6).const_sub 1).add
    ((hasDerivAt_pow 3 y).const_mul 4))).const_mul (2 / 3) using 1
  simp only [show (2 - 1 : ℕ) = 1 from rfl, show (3 - 1 : ℕ) = 2 from rfl]
  ring

private theorem contDiff_sqPotential :
    ContDiff ℝ 2 (fun z : ℝ => (2 / 3) * z * (1 - z) * (1 + z - z ^ 2)) :=
  (((contDiff_const.mul contDiff_id).mul
    (contDiff_const.sub contDiff_id)).mul
    ((contDiff_const.add contDiff_id).sub (contDiff_id.pow 2)))

private theorem continuous_sqHeteroSq :
    Continuous fun z : ℝ => (2 * z * (1 - z)) ^ 2 :=
  ((continuous_const.mul continuous_id).mul
    (continuous_const.sub continuous_id)).pow 2

private theorem sqPotential_zero :
    (fun z : ℝ => (2 / 3) * z * (1 - z) * (1 + z - z ^ 2)) 0 = 0 := by
  show (2 / 3) * (0 : ℝ) * (1 - 0) * (1 + 0 - 0 ^ 2) = 0
  ring

private theorem sqPotential_one :
    (fun z : ℝ => (2 / 3) * z * (1 - z) * (1 + z - z ^ 2)) 1 = 0 := by
  show (2 / 3) * (1 : ℝ) * (1 - 1) * (1 + 1 - 1 ^ 2) = 0
  ring

/-- Neutral generator applied to the squared-heterozygosity potential: for every real `y`
(no restriction to the unit interval),
`generator 0 (fun z => (2/3) z(1-z)(1+z-z^2)) y = -((2y(1-y))^2)`, pointwise in `y`. The
potential vanishes at both endpoints, `u(0) = u(1) = 0`, with `u''(y) = -8y(1-y)`; time is
in diffusion units (multiples of `2N` generations). This is a pointwise
ordinary-differential-equation identity and makes no claim about any process. -/
theorem generator_zero_heterozygositySqPotential (y : ℝ) :
    generator 0 (fun z => (2 / 3) * z * (1 - z) * (1 + z - z ^ 2)) y =
      -((2 * y * (1 - y)) ^ 2) := by
  have hD1 : deriv (fun z : ℝ => (2 / 3) * z * (1 - z) * (1 + z - z ^ 2)) =
      fun z => (2 / 3) * (1 - 6 * z ^ 2 + 4 * z ^ 3) :=
    funext fun z => (hasDerivAt_sqPotential_first z).deriv
  have h2 : HasDerivAt (fun z : ℝ => (2 / 3) * (1 - 6 * z ^ 2 + 4 * z ^ 3))
      (-8 * y * (1 - y)) y :=
    hasDerivAt_sqPotential_second y
  rw [generator, hD1, h2.deriv]
  ring

/-- **Forward squared-heterozygosity functional.** For a solution of the neutral Wright-Fisher
martingale problem started at frequency `x` under a probability measure, the squared heterozygosity
accumulated until absorption is integrable, and its expectation, in diffusion units (multiples of
`2N` generations), is `(2/3) x(1-x)(1+x-x^2)`. This is a derived corollary of the Maruyama-Kimura
functional machinery with `K = g`, `g(y) = (2y(1-y))^2` and boundary values `0` at both endpoints,
in the repository scaling. It is the occupation of the squared integrand, not the second moment of
the accumulated heterozygosity functional. -/
theorem integral_sq_two_mul_one_sub_absorptionTime {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {x : ℝ} {ℱ : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℝ≥0 → Ω → ℝ} (hX : IsWrightFisherSolution 0 ℱ μ X)
    (hX0 : ∀ᵐ ω ∂μ, X 0 ω = x) :
    Integrable (fun ω => ∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
        (2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) ^ 2) μ ∧
      ∫ ω, (∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
        (2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) ^ 2) ∂μ
        = (2 / 3) * x * (1 - x) * (1 + x - x ^ 2) := by
  exact integral_absorptionTime_of_generator_eq_neg hX hX0
    (u := fun z => (2 / 3) * z * (1 - z) * (1 + z - z ^ 2))
    (g := fun z => (2 * z * (1 - z)) ^ 2)
    contDiff_sqPotential continuous_sqHeteroSq
    (fun y => generator_zero_heterozygositySqPotential y)
    sqPotential_zero sqPotential_one

/-- **Realization reading.** For every `x : I`, the stopped squared-heterozygosity integral
of the constructed neutral realization `modifiedProcess x` is integrable with respect to
`rawMeasure x`, and its integral equals `(2/3) x(1-x)(1+x-x^2)`. This is the non-vacuity
reading of `integral_sq_two_mul_one_sub_absorptionTime` for the realization identified by
`isWrightFisherSolution_zero_modifiedProcess`. -/
theorem integral_sq_two_mul_one_sub_absorptionTime_modifiedProcess (x : I) :
    Integrable (fun ω => ∫ s in (0 : ℝ)..(absorptionTime (modifiedProcess x) ω : ℝ),
        (2 * modifiedProcess x (Real.toNNReal s) ω *
          (1 - modifiedProcess x (Real.toNNReal s) ω)) ^ 2) (rawMeasure x) ∧
      ∫ ω, (∫ s in (0 : ℝ)..(absorptionTime (modifiedProcess x) ω : ℝ),
        (2 * modifiedProcess x (Real.toNNReal s) ω *
          (1 - modifiedProcess x (Real.toNNReal s) ω)) ^ 2) ∂(rawMeasure x)
        = (2 / 3) * (x : ℝ) * (1 - (x : ℝ)) * (1 + (x : ℝ) - (x : ℝ) ^ 2) := by
  exact integral_absorptionTime_of_generator_eq_neg_modifiedProcess x
    (u := fun z => (2 / 3) * z * (1 - z) * (1 + z - z ^ 2))
    (g := fun z => (2 * z * (1 - z)) ^ 2)
    contDiff_sqPotential continuous_sqHeteroSq
    (fun y => generator_zero_heterozygositySqPotential y)
    sqPotential_zero sqPotential_one

end MathlibExt.Biology.PopulationGenetics.Diffusion
