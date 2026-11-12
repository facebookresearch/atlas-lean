/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Local (Redington) immunization

The surplus `surplus A L r = A r - L r` is the asset value minus the liability
value at rate `r`. When the surplus is zero at `r₀` (matched value), its first
derivative vanishes at `r₀` (matched duration), its second derivative is
strictly positive at `r₀` (strictly more asset convexity), and it is continuous
at `r₀`, the second-derivative test makes `r₀` a local minimum of the surplus,
so the surplus stays nonnegative for rates near `r₀`
(`surplus_nonneg_near_of_matched`). This is local protection against small
parallel yield shifts only, not global protection and not protection against
curve twists.

## Main results

* `MathlibExt.Economics.Finance.Immunization.surplus_nonneg_near_of_matched`

## References

SOA Exam FM syllabus (Redington immunization). Atlas roadmap target FI04.T03.
-/

@[expose] public section

namespace MathlibExt.Economics.Finance.Immunization

/-- Surplus at rate `r`: asset value minus liability value. -/
noncomputable def surplus (A L : ℝ → ℝ) (r : ℝ) : ℝ := A r - L r

/-- **Local (Redington) immunization.** If the surplus is zero at `r₀` (matched
value), its first derivative vanishes at `r₀` (matched duration, since the
derivative of a present value is `-Dmod * P`), its second derivative is strictly
positive at `r₀` (strictly more asset convexity), and the surplus is continuous
at `r₀`, then the surplus stays nonnegative for all rates sufficiently close to
`r₀`. This is local protection against small parallel yield shifts only, not
global protection against curve twists. -/
theorem surplus_nonneg_near_of_matched {A L : ℝ → ℝ} {r₀ : ℝ}
    (hval : surplus A L r₀ = 0)
    (hderiv : deriv (surplus A L) r₀ = 0)
    (hderiv2 : 0 < deriv (deriv (surplus A L)) r₀)
    (hcont : ContinuousAt (surplus A L) r₀) :
    ∃ δ > 0, ∀ r, |r - r₀| < δ → 0 ≤ surplus A L r := by
  have hmin : IsLocalMin (surplus A L) r₀ :=
    isLocalMin_of_deriv_deriv_pos hderiv2 hderiv hcont
  have hev : Filter.Eventually (fun r => surplus A L r₀ ≤ surplus A L r) (nhds r₀) :=
    hmin
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, h⟩ := hev
  exact ⟨δ, hδ, fun r hr => by
    have h' := h (by rwa [Real.dist_eq])
    rwa [hval] at h'⟩

end MathlibExt.Economics.Finance.Immunization
