/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.Complex.Loewner.LoewnerExistence

/-!
# Loewner chains from SLE realizations

Builds the `LoewnerChain` of an SLE`_κ` sample path from a solution `g` of the Loewner
equation driven by `√κ B_t(ω)`.

Removed: an earlier version of this file packaged a capacity-parametrized chain
(`IsCapacityParametrized`, `CapacityParametrizedChain`) and derived `hcap(g_t) = 2t`
(`chordalSLE_capacity_parametrized`, `chordalSLE_hcap_eq`,
`chordalSLE_realization_capacity_parametrized`) from it. That package stored the capacity
coefficient together with the assumption that its derivative is already `2`, so the
`hcap(g_t) = 2t` conclusions followed only by solving the assumed ODE; the Loewner equation
contributed no capacity argument. Deriving the capacity expansion and the rate `2` from
`SatisfiesLoewnerEquation` is not proved in the library, so the conditional capstone was
removed rather than presented as an SLE result. The unconditional conditional-capacity
computation (given a capacity expansion and a rate, the coefficient is `2t`) lives in
`LoewnerCapacity` (`loewner_capacity_eq_of_loewnerChain`, `coeff_ode_solution`).

Caveats on fidelity:
* Nothing here uses the law of `B`: the SLE results hold pathwise for any continuous driving
  function of the form `√κ B_t(ω)`.

## Main definitions

* `loewnerChain_of_sle_realization`.

## Main results

* `loewnerChain_of_sle_realization_maps`, `loewnerChain_of_sle_realization_driving`.

## References

* G. F. Lawler, *Conformally Invariant Processes in the Plane*, Mathematical Surveys and Monographs
  114, Amer. Math. Soc., 2005, Chapters 4 and 6.
-/

@[expose] public section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal

namespace StatMech.SLE

/-- The SLE driving function `√κ B_t(ω)` is continuous when `t ↦ B_t(ω)` is. -/
lemma continuous_sleDriving {Ω : Type*} (κ : ℝ) (B : ℝ → Ω → ℝ) (ω : Ω)
    (hcont : Continuous fun t => B t ω) : Continuous (sleDriving κ B ω) := by
  unfold sleDriving
  exact continuous_const.mul hcont

/-- The Loewner chain of an SLE`_κ` sample path `ω`, from a solution `g` of the Loewner equation
driven by `√κ B_t(ω)`. -/
noncomputable def loewnerChain_of_sle_realization {Ω : Type*} (κ : ℝ)
    (B : ℝ → Ω → ℝ) (ω : Ω) (g : ℝ → ℂ → ℂ)
    (hcont : Continuous fun t => B t ω)
    (hloe : SatisfiesLoewnerEquation (sleDriving κ B ω) g) : LoewnerChain where
  driving := sleDriving κ B ω
  driving_continuous := continuous_sleDriving κ B ω hcont
  maps := g
  loewner := hloe

@[simp] lemma loewnerChain_of_sle_realization_maps {Ω : Type*} (κ : ℝ)
    (B : ℝ → Ω → ℝ) (ω : Ω) (g : ℝ → ℂ → ℂ)
    (hcont : Continuous fun t => B t ω)
    (hloe : SatisfiesLoewnerEquation (sleDriving κ B ω) g) :
    (loewnerChain_of_sle_realization κ B ω g hcont hloe).maps = g := rfl

@[simp] lemma loewnerChain_of_sle_realization_driving {Ω : Type*} (κ : ℝ)
    (B : ℝ → Ω → ℝ) (ω : Ω) (g : ℝ → ℂ → ℂ)
    (hcont : Continuous fun t => B t ω)
    (hloe : SatisfiesLoewnerEquation (sleDriving κ B ω) g) :
    (loewnerChain_of_sle_realization κ B ω g hcont hloe).driving = sleDriving κ B ω := rfl

end StatMech.SLE
