/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Chemistry.Amounts.MolarMassComposition
public import PhyslibExt.Units.QuantityDimensions
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# MS01 quantities: Arrhenius coordinates and composition percentages

Dimension-safe Arrhenius log identities and weight/atomic-percent conversions for the
ATLAS MS01 pilot slice.

## i. Overview

This module proves the cores needed by the MS01 roadmap slice (quantities, units,
dimensional analysis, composition conventions): the Arrhenius log identity in natural and
base-10 logarithms and the wt%/at% percent forms of the canonical weight-fraction/mole-fraction
conversions.

The Arrhenius identities are stated over typed `WithDim` quantities from
`PhyslibExt.Units.QuantityDimensions`. A rate `y`, a reference value `y_ref` and a prefactor `A`
share one dimension `d`; the activation energy `E`, the gas constant `R` and the absolute
temperature `T` have the dimensions `molarEnergyDim`, `gasConstantDim` and `temperatureDim`.
The model `y = A * exp (-(E / (R * T)))` is written with
`Units.QuantityDimensions.expScaledEnergy`, whose exponent is dimensionless by construction, and
every logarithm is a `Units.QuantityDimensions.logRatio` of two quantities of the same dimension,
so Lean rejects dimensionally inconsistent inputs. The raw-real algebra is a private helper.

Composition maps and their round trips are NOT restated here. The conversions
are the canonical `Chemistry.Amounts.massFraction` /
`Chemistry.Amounts.moleFractionOfMassFraction` from ATLAS main
(`PhyslibExt.Chemistry.Amounts.MolarMassComposition`), whose closed-simplex
round-trip theorems
`Chemistry.Amounts.moleFractionOfMassFraction_massFraction_of_sum_eq_one` and
`Chemistry.Amounts.massFraction_moleFractionOfMassFraction_of_sum_eq_one` are
used directly. Likewise, the rank-nullity count of dimensionless groups for a
rational dimension matrix is `Chemistry.QuantityCalculus.finrank_ker_mulVecLin`
(`PhyslibExt.Chemistry.QuantityCalculus`) and is not restated here.

## ii. Key results

* `arrhenius_log`: under the Arrhenius model `y = A * expScaledEnergy E R T` with positive
  coordinates, `logRatio y y_ref = logRatio A y_ref - E / (R * T)`.
* `arrhenius_log10`: the base-10 form,
  `logRatio y y_ref / log 10 = logRatio A y_ref / log 10 - E / (R * T * log 10)`; on
  coordinates its left side is `Real.logb 10 (y / y_ref)`.
* `wtPct_atPct`: the wt%/at% percent forms convert by the canonical mutually
  inverse maps scaled by 100.

## iii. Table of contents

* a. Arrhenius coordinates: `arrhenius_log`, `arrhenius_log10`.
* b. Composition percentages: `wtPct`, `atPct`, `wtPct_atPct` (maps are
  `Chemistry.Amounts.massFraction` /
  `Chemistry.Amounts.moleFractionOfMassFraction`).

## iv. References

* Roadmap module MS01 (materials, core): quantities, units, dimensional
  analysis, composition conventions.
* `PhyslibExt.Units.QuantityDimensions`: ISQ dimensions as `WithDim` quantities,
  `expScaledEnergy` and `logRatio`.
* `PhyslibExt.Chemistry.Amounts.MolarMassComposition`: canonical mole/mass-fraction API.
* `PhyslibExt.Chemistry.QuantityCalculus`: canonical dimension-kernel count
  `Chemistry.QuantityCalculus.finrank_ker_mulVecLin`.
-/

@[expose] public section

namespace PhyslibExt.CondensedMatter.Quantities.Composition

open Units.QuantityDimensions

/-! ## a. Arrhenius coordinates -/

/-- The raw-real algebra behind `arrhenius_log`. -/
private lemma arrhenius_log_real {y y_ref A T R E : ℝ} (hy_ref : 0 < y_ref) (hA : 0 < A)
    (_hy : 0 < y) (_hT : 0 < T) (_hR : 0 < R)
    (h : y = A * Real.exp (-E / (R * T))) :
    Real.log (y / y_ref) = Real.log (A / y_ref) - E / (R * T) := by
  have hexp : Real.exp (-E / (R * T)) ≠ 0 := Real.exp_ne_zero _
  have hAmul : A * Real.exp (-E / (R * T)) ≠ 0 :=
    mul_ne_zero (ne_of_gt hA) hexp
  rw [h, Real.log_div hAmul (ne_of_gt hy_ref),
    Real.log_mul (ne_of_gt hA) hexp, Real.log_exp,
    Real.log_div (ne_of_gt hA) (ne_of_gt hy_ref)]
  ring

/-- Arrhenius log identity (natural log): if a rate `y` follows the Arrhenius model
`y = A * exp (-(E / (R * T)))`, written with the dimension-safe factor `expScaledEnergy E R T`,
and `y, y_ref, A, R, T` are positive, then the log of `y / y_ref` is the log of the
prefactor ratio `A / y_ref` minus `E / (R * T)`. The quantities `y`, `y_ref` and `A` share one
dimension `d`, and `E`, `R`, `T` are a molar energy, a gas constant and an absolute temperature.
Mathematical consequence (MC) of the stated model; no empirical parameter value is
asserted. -/
lemma arrhenius_log {d : Dimension ISQDimensionBase} {y y_ref A : WithDim d ℝ}
    {E : WithDim molarEnergyDim ℝ} {R : WithDim gasConstantDim ℝ}
    {T : WithDim temperatureDim ℝ} (hy_ref : 0 < y_ref.val) (hA : 0 < A.val)
    (hy : 0 < y.val) (hT : 0 < T.val) (hR : 0 < R.val)
    (h : y.val = A.val * expScaledEnergy E R T hR hT) :
    logRatio y y_ref hy hy_ref = logRatio A y_ref hA hy_ref - E.val / (R.val * T.val) := by
  rw [expScaledEnergy_val, ← neg_div] at h
  rw [logRatio_val, logRatio_val]
  exact arrhenius_log_real hy_ref hA hy hT hR h

/-- Arrhenius log identity (base 10): the same statement as `arrhenius_log` divided by
`Real.log 10`. On coordinates, `logRatio y y_ref hy hy_ref / Real.log 10` is
`Real.logb 10 (y / y_ref)`, since `Real.logb b x = Real.log x / Real.log b`. -/
lemma arrhenius_log10 {d : Dimension ISQDimensionBase} {y y_ref A : WithDim d ℝ}
    {E : WithDim molarEnergyDim ℝ} {R : WithDim gasConstantDim ℝ}
    {T : WithDim temperatureDim ℝ} (hy_ref : 0 < y_ref.val) (hA : 0 < A.val)
    (hy : 0 < y.val) (hT : 0 < T.val) (hR : 0 < R.val)
    (h : y.val = A.val * expScaledEnergy E R T hR hT) :
    logRatio y y_ref hy hy_ref / Real.log 10
      = logRatio A y_ref hA hy_ref / Real.log 10 - E.val / (R.val * T.val * Real.log 10) := by
  rw [arrhenius_log hy_ref hA hy hT hR h, sub_div, div_div]

/-! ## b. Composition percentages -/

/-- Weight percent: `100 * Chemistry.Amounts.massFraction M x i`. -/
noncomputable def wtPct {ι : Type*} [Fintype ι] (M x : ι → ℝ) : ι → ℝ :=
  fun i => 100 * Chemistry.Amounts.massFraction M x i

/-- Atomic percent (elemental case): `100 * x i` for mole fractions `x`. -/
noncomputable def atPct {ι : Type*} (x : ι → ℝ) : ι → ℝ :=
  fun i => 100 * x i

/-- wt%/at% conversion by the same mutually inverse maps scaled by 100:
normalizing a positive 100-sum vector to the simplex, converting, and scaling
back is the identity in both directions. Corollary of the canonical round trips
`Chemistry.Amounts.massFraction_moleFractionOfMassFraction_of_sum_eq_one` and
`Chemistry.Amounts.moleFractionOfMassFraction_massFraction_of_sum_eq_one` with
the factor 100 carried through. -/
lemma wtPct_atPct {ι : Type*} [Fintype ι] [Nonempty ι] {M : ι → ℝ}
    (hM : ∀ i, 0 < M i) :
    (∀ {w : ι → ℝ}, (∀ i, 0 < w i) → ∑ i, w i = 100 →
      wtPct M (Chemistry.Amounts.moleFractionOfMassFraction M
        (fun i => w i / 100)) = w)
    ∧ (∀ {x : ι → ℝ}, (∀ i, 0 < x i) → ∑ i, x i = 1 →
      atPct (Chemistry.Amounts.moleFractionOfMassFraction M
        (Chemistry.Amounts.massFraction M x)) = atPct x) := by
  constructor
  · intro w hw hsum
    have h1 : ∀ i, 0 < w i / 100 := fun i => div_pos (hw i) (by norm_num)
    have h2 : ∑ i, w i / 100 = 1 := by
      rw [← Finset.sum_div, hsum]
      norm_num
    have h3 := Chemistry.Amounts.massFraction_moleFractionOfMassFraction_of_sum_eq_one
      (fun i => (h1 i).le) h2 hM
    funext i
    simp only [wtPct]
    rw [h3]
    ring
  · intro x hx hsum
    rw [Chemistry.Amounts.moleFractionOfMassFraction_massFraction_of_sum_eq_one
      (fun i => (hx i).le) hsum hM]

end PhyslibExt.CondensedMatter.Quantities.Composition
