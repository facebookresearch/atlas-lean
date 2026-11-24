/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import MathlibExt.Analysis.Calculus.StrictSecondDerivativeTest

/-!
# Local (Redington) immunization

The surplus `surplus A L r = A r - L r` is the asset value minus the liability
value at rate `r`.

`redington_immunization` is the Redington statement. Let the asset and
liability values `A` and `L` be differentiable near `r₀`, with derivatives
differentiable at `r₀`. If the values match at `r₀`, the first derivatives
match there (matched dollar duration), and the asset's second derivative
strictly exceeds the liability's (strictly greater asset dollar convexity),
then the surplus stays nonnegative for rates near `r₀`. This is local
protection against small parallel yield shifts only, not global protection and
not protection against curve twists. The hypotheses are stated in
raw-derivative / dollar terms: no positive matched present value is assumed,
so they are not identified here with modified duration / convexity, which
divide by the matched value. `redington_immunization_strict` gives the strict
conclusion under the same hypotheses: the surplus is strictly positive at every
nearby rate other than `r₀`.

The proofs go through `surplus_pos_near_of_matched`, an abstract lemma about
the surplus alone: zero value, vanishing first derivative, positive second
derivative, and continuity at `r₀` make `r₀` a strict local minimum by the
strict second-derivative test (`isStrictLocalMin_of_deriv_deriv_pos`). Its
nonnegative corollary is `surplus_nonneg_near_of_matched`. These hypotheses
constrain only the difference `A - L` and do not make `A` or `L`
differentiable, so on their own they do not certify the Redington conditions on
the asset and liability.

## Main results

* `MathlibExt.Economics.Finance.Immunization.redington_immunization`
* `MathlibExt.Economics.Finance.Immunization.redington_immunization_strict`
* `MathlibExt.Economics.Finance.Immunization.surplus_nonneg_near_of_matched`
* `MathlibExt.Economics.Finance.Immunization.surplus_pos_near_of_matched`

## References

SOA Exam FM syllabus (Redington immunization). Atlas roadmap target FI04.T03.
-/

@[expose] public section

namespace MathlibExt.Economics.Finance.Immunization

/-- Surplus at rate `r`: asset value minus liability value. -/
noncomputable def surplus (A L : ℝ → ℝ) (r : ℝ) : ℝ := A r - L r

/-- **Abstract surplus lemma, strict form.** If the surplus is zero at `r₀`, its
first derivative vanishes at `r₀`, its second derivative is strictly positive at
`r₀`, and the surplus is continuous at `r₀`, then `r₀` is a strict local minimum
of the surplus (`isStrictLocalMin_of_deriv_deriv_pos`): the surplus is strictly
positive at every rate `r ≠ r₀` sufficiently close to `r₀`. As for
`surplus_nonneg_near_of_matched`, the hypotheses constrain only the difference
`A - L`. -/
theorem surplus_pos_near_of_matched {A L : ℝ → ℝ} {r₀ : ℝ}
    (hval : surplus A L r₀ = 0)
    (hderiv : deriv (surplus A L) r₀ = 0)
    (hderiv2 : 0 < deriv (deriv (surplus A L)) r₀)
    (hcont : ContinuousAt (surplus A L) r₀) :
    ∃ δ > 0, ∀ r, r ≠ r₀ → |r - r₀| < δ → 0 < surplus A L r := by
  have hmin : IsStrictLocalMin (surplus A L) r₀ :=
    isStrictLocalMin_of_deriv_deriv_pos hderiv2 hderiv hcont
  have hev : ∀ᶠ r in nhds r₀, r ∈ ({r₀}ᶜ : Set ℝ) → surplus A L r₀ < surplus A L r :=
    eventually_nhdsWithin_iff.mp hmin
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ, hδ, fun r hne hr => ?_⟩
  have h' := @h r (by rwa [Real.dist_eq]) (Set.mem_compl_singleton_iff.mpr hne)
  rwa [hval] at h'

/-- **Abstract surplus lemma.** If the surplus is zero at `r₀`, its first
derivative vanishes at `r₀`, its second derivative is strictly positive at
`r₀`, and the surplus is continuous at `r₀`, then the surplus stays nonnegative
for all rates sufficiently close to `r₀`. The hypotheses constrain only the
difference `A - L`, not `A` and `L` themselves: they do not make the asset or
liability value differentiable, and Lean's `deriv` is `0` where a function is
not differentiable. So they do not by themselves certify the Redington
conditions; the faithful Redington statement, with the duration and convexity
conditions stated on `A` and `L`, is `redington_immunization`. This is the
nonnegative corollary of `surplus_pos_near_of_matched`. -/
theorem surplus_nonneg_near_of_matched {A L : ℝ → ℝ} {r₀ : ℝ}
    (hval : surplus A L r₀ = 0)
    (hderiv : deriv (surplus A L) r₀ = 0)
    (hderiv2 : 0 < deriv (deriv (surplus A L)) r₀)
    (hcont : ContinuousAt (surplus A L) r₀) :
    ∃ δ > 0, ∀ r, |r - r₀| < δ → 0 ≤ surplus A L r := by
  obtain ⟨δ, hδ, h⟩ := surplus_pos_near_of_matched hval hderiv hderiv2 hcont
  refine ⟨δ, hδ, fun r hr => ?_⟩
  rcases eq_or_ne r r₀ with rfl | hne
  · exact hval.ge
  · exact (h r hne hr).le

/-- **Local (Redington) immunization, strict form.** Under the hypotheses of
`redington_immunization`, the surplus is strictly positive at every rate
`r ≠ r₀` sufficiently close to `r₀`: the strict convexity condition protects
against every small nonzero parallel yield shift. -/
theorem redington_immunization_strict {A L : ℝ → ℝ} {r₀ : ℝ}
    (hA : ∀ᶠ r in nhds r₀, DifferentiableAt ℝ A r)
    (hL : ∀ᶠ r in nhds r₀, DifferentiableAt ℝ L r)
    (hA' : DifferentiableAt ℝ (deriv A) r₀) (hL' : DifferentiableAt ℝ (deriv L) r₀)
    (hval : A r₀ = L r₀) (hdur : deriv A r₀ = deriv L r₀)
    (hconv : deriv (deriv L) r₀ < deriv (deriv A) r₀) :
    ∃ δ > 0, ∀ r, r ≠ r₀ → |r - r₀| < δ → 0 < surplus A L r := by
  have hsurp : surplus A L = fun r => A r - L r := rfl
  have hderiv : deriv (surplus A L) =ᶠ[nhds r₀] fun r => deriv A r - deriv L r := by
    filter_upwards [hA, hL] with r hAr hLr
    rw [hsurp]
    exact deriv_fun_sub hAr hLr
  refine surplus_pos_near_of_matched ?_ ?_ ?_ ?_
  · simp [surplus, hval]
  · rw [hderiv.eq_of_nhds, hdur, sub_self]
  · rw [hderiv.deriv_eq, deriv_fun_sub hA' hL']
    linarith
  · rw [hsurp]
    exact (hA.self_of_nhds.sub hL.self_of_nhds).continuousAt

/-- **Local (Redington) immunization.** Let the asset and liability values `A`
and `L` be differentiable near `r₀`, with derivatives differentiable at `r₀`, so
their dollar durations (the negated first derivatives) and dollar convexities
(the second derivatives) are defined there. If the values match at `r₀`
(`A r₀ = L r₀`), the dollar durations match (`deriv A r₀ = deriv L r₀`), and the
asset dollar convexity strictly exceeds the liability dollar convexity
(`deriv (deriv L) r₀ < deriv (deriv A) r₀`), then the surplus stays nonnegative
for all rates sufficiently close to `r₀`. This is local protection against
small parallel yield shifts only, not global protection and not protection
against curve twists. No positive matched present value is assumed, so the
hypotheses are not identified here with modified duration / convexity, which
divide by the matched value. The strict conclusion at `r ≠ r₀` is
`redington_immunization_strict`. -/
theorem redington_immunization {A L : ℝ → ℝ} {r₀ : ℝ}
    (hA : ∀ᶠ r in nhds r₀, DifferentiableAt ℝ A r)
    (hL : ∀ᶠ r in nhds r₀, DifferentiableAt ℝ L r)
    (hA' : DifferentiableAt ℝ (deriv A) r₀) (hL' : DifferentiableAt ℝ (deriv L) r₀)
    (hval : A r₀ = L r₀) (hdur : deriv A r₀ = deriv L r₀)
    (hconv : deriv (deriv L) r₀ < deriv (deriv A) r₀) :
    ∃ δ > 0, ∀ r, |r - r₀| < δ → 0 ≤ surplus A L r := by
  obtain ⟨δ, hδ, h⟩ := redington_immunization_strict hA hL hA' hL' hval hdur hconv
  refine ⟨δ, hδ, fun r hr => ?_⟩
  rcases eq_or_ne r r₀ with rfl | hne
  · simp [surplus, hval]
  · exact (h r hne hr).le

end MathlibExt.Economics.Finance.Immunization
