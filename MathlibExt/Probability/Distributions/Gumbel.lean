/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The Gumbel distribution function and its quantile

The Gumbel law (the type I extreme-value law) with location `μ` and scale `β > 0` has
distribution function `F(x) = exp(-exp(-(x - μ) / β))` and quantile function
`Q(q) = μ - β log(-log q)` for `0 < q < 1`. It is the limit law of suitably centered maxima of
light-tailed samples, such as annual maxima in flood frequency analysis or maximal segment scores
in sequence alignment (Karlin–Altschul).

Both formulas are defined for all real parameters, and each lemma states the parameter range it
needs: the two inverse identities need only `β ≠ 0`, while monotonicity and the order
characterization of the quantile need `β > 0`. No measure is constructed here.

## Main definitions

* `ProbabilityTheory.gumbelCDF μ β x`: `exp(-exp(-(x - μ) / β))`.
* `ProbabilityTheory.gumbelQuantile μ β q`: `μ - β log(-log q)`.

## Main results

* `ProbabilityTheory.gumbelCDF_gumbelQuantile`: `gumbelCDF μ β (gumbelQuantile μ β q) = q` for
  `β ≠ 0` and `0 < q < 1`.
* `ProbabilityTheory.gumbelQuantile_gumbelCDF`: `gumbelQuantile μ β (gumbelCDF μ β x) = x` for
  `β ≠ 0`.
* `ProbabilityTheory.strictMono_gumbelCDF`: `gumbelCDF μ β` is strictly increasing for `β > 0`.
* `ProbabilityTheory.gumbelQuantile_le_iff_le_gumbelCDF`:
  `gumbelQuantile μ β q ≤ x ↔ q ≤ gumbelCDF μ β x` for `β > 0` and `0 < q < 1`.

## References

* E. J. Gumbel, *Statistics of Extremes*, Columbia University Press, New York, 1958.
-/

open Real

namespace ProbabilityTheory

@[expose] public section

noncomputable section

/-- The Gumbel distribution function formula `exp(-exp(-(x - μ) / β))`, defined for all real `μ`
and `β`. For scale `β > 0` it is the cumulative distribution function of the Gumbel law with
location `μ` and scale `β`. -/
def gumbelCDF (μ β x : ℝ) : ℝ :=
  exp (-exp (-(x - μ) / β))

/-- The Gumbel quantile formula `μ - β log(-log q)`, defined for all real `μ`, `β` and `q`. For
`β ≠ 0` and `0 < q < 1` it inverts `gumbelCDF μ β` (`gumbelCDF_gumbelQuantile`); for `β > 0` it
is the `q`-quantile of the Gumbel law with location `μ` and scale `β`. -/
def gumbelQuantile (μ β q : ℝ) : ℝ :=
  μ - β * log (-log q)

variable {μ β q x : ℝ}

/-- For `β ≠ 0` and `0 < q < 1`, `gumbelCDF μ β` at `gumbelQuantile μ β q` is `q`. -/
theorem gumbelCDF_gumbelQuantile (hβ : β ≠ 0) (hq₀ : 0 < q) (hq₁ : q < 1) :
    gumbelCDF μ β (gumbelQuantile μ β q) = q := by
  have h : -(gumbelQuantile μ β q - μ) / β = log (-log q) := by
    rw [gumbelQuantile]
    field_simp
    ring
  rw [gumbelCDF, h, exp_log (neg_pos.2 (log_neg hq₀ hq₁)), neg_neg, exp_log hq₀]

/-- For `β ≠ 0`, `gumbelQuantile μ β` at `gumbelCDF μ β x` is `x`. -/
theorem gumbelQuantile_gumbelCDF (hβ : β ≠ 0) (μ x : ℝ) :
    gumbelQuantile μ β (gumbelCDF μ β x) = x := by
  rw [gumbelQuantile, gumbelCDF, log_exp, neg_neg, log_exp]
  field_simp
  ring

/-- For scale `β > 0` the Gumbel distribution function is strictly increasing. -/
theorem strictMono_gumbelCDF (μ : ℝ) (hβ : 0 < β) : StrictMono (gumbelCDF μ β) := by
  intro a b hab
  unfold gumbelCDF
  gcongr

/-- **Order characterization of the quantile.** For scale `β > 0` and `0 < q < 1`, the
`q`-quantile is at most `x` exactly when the distribution function at `x` is at least `q`. -/
theorem gumbelQuantile_le_iff_le_gumbelCDF (hβ : 0 < β) (hq₀ : 0 < q) (hq₁ : q < 1) :
    gumbelQuantile μ β q ≤ x ↔ q ≤ gumbelCDF μ β x := by
  simpa only [gumbelCDF_gumbelQuantile hβ.ne' hq₀ hq₁] using
    ((strictMono_gumbelCDF μ hβ).le_iff_le (a := gumbelQuantile μ β q) (b := x)).symm

end

end

end ProbabilityTheory
