/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Adapted from eth/proof/rates/GeneralPieces/GenF/Exp.lean in
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
express weighted exponential laws through the canonical coefficient map,
rescaling, finite truncation, and lawful zero-constant exponential APIs.
-/
module

public import MathlibExt.RingTheory.MvPowerSeries.ExponentialHom
public import MathlibExt.RingTheory.MvPowerSeries.WeightedRescale

/-!
# Weighted multivariate formal exponentials

Mapping rational coefficients and rescaling variables according to an additive
monomial weight commutes with every finite exponential truncation. This law is
unconditional, including for series with nonzero constant coefficient.
-/

@[expose] public section

namespace MvPowerSeries

variable {X R : Type*} [CommRing R] [Algebra ℚ R]

/-- Weighted coefficient mapping and rescaling commutes with every finite
exponential truncation, without a constant coefficient restriction. -/
theorem expTrunc_rescale_map_of_weight (wt : (X →₀ ℕ) →+ ℕ) (ε : R)
    (q : MvPowerSeries X ℚ) (N : ℕ) :
    expTrunc N
        (rescale (fun i => ε ^ wt (Finsupp.single i 1))
          (map (algebraMap ℚ R) q)) =
      rescale (fun i => ε ^ wt (Finsupp.single i 1))
        (map (algebraMap ℚ R) (expTrunc N q)) := by
  rw [← map_expTrunc (rescale (fun i => ε ^ wt (Finsupp.single i 1))),
    map_expTrunc (map (algebraMap ℚ R))]

/-- The coefficient form of weighted finite exponential commutation. It
preserves the source's degreewise expression for arbitrary input series. -/
theorem coeff_expTrunc_rescale_map_of_weight (wt : (X →₀ ℕ) →+ ℕ) (ε : R)
    (q : MvPowerSeries X ℚ) (N : ℕ) (d : X →₀ ℕ) :
    coeff d
        (expTrunc N
          (rescale (fun i => ε ^ wt (Finsupp.single i 1))
            (map (algebraMap ℚ R) q))) =
      algebraMap ℚ R (coeff d (expTrunc N q)) * ε ^ wt d := by
  rw [expTrunc_rescale_map_of_weight, coeff_rescale_map_of_weight]

/-- On the zero-constant domain, weighted coefficient mapping and rescaling
commutes with the lawful full formal exponential. -/
theorem expOfConstantCoeffZero_rescale_map_of_weight (wt : (X →₀ ℕ) →+ ℕ)
    (ε : R) (q : MvPowerSeries X ℚ) (hq : constantCoeff q = 0) :
    expOfConstantCoeffZero
        (rescale (fun i => ε ^ wt (Finsupp.single i 1))
          (map (algebraMap ℚ R) q)) (by
            rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale_map_of_weight,
              coeff_zero_eq_constantCoeff_apply, hq]
            simp) =
      rescale (fun i => ε ^ wt (Finsupp.single i 1))
        (map (algebraMap ℚ R) (expOfConstantCoeffZero q hq)) := by
  rw [map_expOfConstantCoeffZero]
  symm
  apply hom_expOfConstantCoeffZero
  intro d f g hfg
  rw [coeff_rescale, coeff_rescale, hfg d (le_refl _)]

/-- Weighted coefficient equality transfers a zero constant coefficient from
the rational source series to the target series. -/
theorem constantCoeff_eq_zero_of_weight (wt : (X →₀ ℕ) →+ ℕ) (ε : R)
    (q : MvPowerSeries X ℚ) {w : MvPowerSeries X R} (hq : constantCoeff q = 0)
    (hw : ∀ d, coeff d w = algebraMap ℚ R (coeff d q) * ε ^ wt d) :
    constantCoeff w = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, hw 0,
    coeff_zero_eq_constantCoeff_apply, hq, map_zero, zero_mul]

/-- If `w` has the coefficients of `q` scaled by an additive weight, then the
same coefficient relation holds for their lawful formal exponentials. The
coefficient hypothesis and `q`'s zero constant imply the required premise for
`w`; no separate zero-constant assumption on `w` is needed. -/
theorem coeff_expOfConstantCoeffZero_of_weight (wt : (X →₀ ℕ) →+ ℕ) (ε : R)
    (q : MvPowerSeries X ℚ) {w : MvPowerSeries X R} (hq : constantCoeff q = 0)
    (hw : ∀ d, coeff d w = algebraMap ℚ R (coeff d q) * ε ^ wt d)
    (d : X →₀ ℕ) :
    coeff d
        (expOfConstantCoeffZero w (constantCoeff_eq_zero_of_weight wt ε q hq hw)) =
      algebraMap ℚ R (coeff d (expOfConstantCoeffZero q hq)) * ε ^ wt d := by
  have hw' := (eq_rescale_map_of_weight_iff wt ε q w).2 hw
  subst w
  rw [expOfConstantCoeffZero_rescale_map_of_weight, coeff_rescale_map_of_weight]

end MvPowerSeries
