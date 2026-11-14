/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Gumbel quantile inverts the Gumbel CDF

Flood frequency analysis fits a distribution to annual maxima and reads
design levels off its quantile function. For the Gumbel distribution with
fitted location `μ` and scale `β > 0`, the CDF is
`F(x) = exp(-exp(-(x - μ) / β))` and the quantile function (inverse CDF) is
`Q(q) = μ - β * log(-log q)` for `q ∈ (0, 1)`. The two theorems here are the
stated mathematical inversion of that fitted distribution: `F(Q(q)) = q`
and `Q(F(x)) = x`. This is a statement about the fitted formulas, not an
empirical or stationarity claim about a real river.

## i. Overview

Both inversions are `exp`/`log` cancellations once the definitions are
unfolded and the inner arithmetic is simplified with `β ≠ 0`.

## ii. Key results

- `EarthScience.gumbelCDF`: Gumbel CDF for annual maxima.
- `EarthScience.gumbelQuantile`: Gumbel quantile (inverse CDF).
- `EarthScience.gumbelQuantile_inverts_cdf`: the CDF at the `q`-quantile
  is `q`.
- `EarthScience.gumbelCDF_inverts_quantile`: the quantile at `CDF(x)`
  is `x`.

## iii. Table of contents

- A. Gumbel CDF and quantile
- B. The two inversions

## iv. References

- `Real.exp_log`, `Real.log_exp`, `Real.log_neg` (Mathlib).

## A. Gumbel CDF and quantile
-/

@[expose] public section

namespace EarthScience

/-- Gumbel CDF for annual maxima, with fitted location `μ` and scale `β > 0`. -/
noncomputable def gumbelCDF (μ β x : ℝ) : ℝ :=
  Real.exp (-Real.exp (-(x - μ) / β))

/-- Gumbel quantile (inverse CDF): the level exceeded with probability `1 - q`. -/
noncomputable def gumbelQuantile (μ β q : ℝ) : ℝ :=
  μ - β * Real.log (-Real.log q)

/-!
## B. The two inversions
-/

/-- Quantile inverts the CDF: the CDF at the `q`-quantile is `q`. -/
theorem gumbelQuantile_inverts_cdf {μ β q : ℝ} (hβ : 0 < β) (hq0 : 0 < q) (hq1 : q < 1) :
    gumbelCDF μ β (gumbelQuantile μ β q) = q := by
  have hβ' : β ≠ 0 := ne_of_gt hβ
  have hlog : Real.log q < 0 := Real.log_neg hq0 hq1
  have hneg : 0 < -Real.log q := by linarith
  simp only [gumbelCDF, gumbelQuantile]
  have hinner : (-(μ - β * Real.log (-Real.log q) - μ)) / β
      = Real.log (-Real.log q) := by
    field_simp
    ring
  rw [hinner, Real.exp_log hneg, neg_neg, Real.exp_log hq0]

/-- CDF inverts the quantile: the quantile at `CDF(x)` is `x`. -/
theorem gumbelCDF_inverts_quantile {μ β x : ℝ} (hβ : 0 < β) :
    gumbelQuantile μ β (gumbelCDF μ β x) = x := by
  have hβ' : β ≠ 0 := ne_of_gt hβ
  simp only [gumbelCDF, gumbelQuantile]
  rw [Real.log_exp, neg_neg, Real.log_exp]
  field_simp
  ring

end EarthScience
