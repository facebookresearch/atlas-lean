/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.QuantileLink
public import MathlibExt.Probability.Distributions.GaussianCdf

/-!
# Equipercentile linking tests

A Gaussian location-scale link in an instantiable form (the affine
relation only on `(0, 1)`, where Atlas quantiles live), the spec applied
to two concrete Gaussian measures, and the Dirac step cdf, which has
neither regularity property (this example alone does not show that each
hypothesis is independently necessary).
-/

open MeasureTheory Set

@[expose] public section

namespace QuantileLinkTest

open ProbabilityTheory QuantileLink

/-- Gaussian location-scale test of the link, in an instantiable form.

Abstractly: if two quantile functions `qF, qG` satisfy the affine
relation `qG u = 1 + 2 * qF u` on `Ioo 0 1` (only there -- Atlas
quantiles are `0` off `(0, 1)`, so the v1 all-reals form was
impossible), a function `F` inverts `qF` pointwise, and `F` takes
values in `Ioo 0 1`, then the linked map `qG ∘ F` is `x ↦ 1 + 2 * x`.

Gaussian witness (why the hypotheses are satisfiable): take `F` the
standard normal cdf, `qF` its quantile and `qG` the quantile of the
normal with mean `1` and standard deviation `2`; the affine relation
is the usual location-scale quantile identity, on `(0, 1)`. -/
theorem gaussian_affine_link (F qF qG : ℝ → ℝ)
    (hlink : ∀ u ∈ Ioo (0 : ℝ) 1, qG u = 1 + 2 * qF u)
    (hqF : ∀ x : ℝ, qF (F x) = x)
    (hF : ∀ x : ℝ, F x ∈ Ioo (0 : ℝ) 1) :
    ∀ x : ℝ, qG (F x) = 1 + 2 * x := by
  intro x
  rw [hlink (F x) (hF x), hqF x]

/-- The production spec applied to two concrete Gaussian measures:
the standard normal and the normal with mean `1` and variance `4`.
Transport and both inverse identities hold for the actual
`cdfQuantile`/`cdf` API. -/
theorem gaussian_equipercentileLink :
    Measure.map
        (fun x => cdfQuantile (ProbabilityTheory.gaussianReal 1 4)
          (cdf (ProbabilityTheory.gaussianReal 0 1) x))
        (ProbabilityTheory.gaussianReal 0 1)
        = ProbabilityTheory.gaussianReal 1 4 ∧
    (∀ x : ℝ,
      (cdfQuantile (ProbabilityTheory.gaussianReal 0 1) ∘
          fun y => cdf (ProbabilityTheory.gaussianReal 1 4) y)
        ((fun x => cdfQuantile (ProbabilityTheory.gaussianReal 1 4)
          (cdf (ProbabilityTheory.gaussianReal 0 1) x)) x) = x) ∧
    (∀ y : ℝ,
      (fun x => cdfQuantile (ProbabilityTheory.gaussianReal 1 4)
          (cdf (ProbabilityTheory.gaussianReal 0 1) x))
        ((cdfQuantile (ProbabilityTheory.gaussianReal 0 1) ∘
          fun z => cdf (ProbabilityTheory.gaussianReal 1 4) z) y) = y) :=
  equipercentileLink_spec _ _
    (ProbabilityTheory.continuous_cdf_gaussianReal 0 (by norm_num))
    (ProbabilityTheory.strictMono_cdf_gaussianReal 0 (by norm_num))
    (ProbabilityTheory.continuous_cdf_gaussianReal 1 (by norm_num))
    (ProbabilityTheory.strictMono_cdf_gaussianReal 1 (by norm_num))


/-- The Dirac step cdf: a single atom at `0`. Its cdf is the step
`x ↦ 0` for `x < 0`, `1` for `x ≥ 0`, hence neither continuous nor
strictly monotone. This shows the two regularity hypotheses exclude
atomic laws; it does not by itself show each hypothesis is
independently necessary. -/
theorem stepCdf_dirac_zero :
    cdf (Measure.dirac (0 : ℝ)) =
      (fun x : ℝ => if x < 0 then (0 : ℝ) else 1) ∧
    ¬ Continuous (cdf (Measure.dirac (0 : ℝ))) ∧
    ¬ StrictMono (cdf (Measure.dirac (0 : ℝ))) := by
  have hdirac : ∀ x : ℝ, cdf (Measure.dirac (0 : ℝ)) x =
      (if x < 0 then (0 : ℝ) else 1) := by
    intro x
    rw [cdf_eq_real]
    by_cases hx : x < 0
    · rw [ite_eq_left hx, Measure.real_def, Measure.dirac_apply]
      have hmem : (0 : ℝ) ∉ Iic x := by simpa using hx
      rw [indicator_of_notMem hmem, ENNReal.toReal_zero]
    · rw [ite_eq_right hx, Measure.real_def, Measure.dirac_apply]
      have hmem : (0 : ℝ) ∈ Iic x := by simpa using le_of_not_gt hx
      rw [indicator_of_mem hmem, Pi.one_apply, ENNReal.toReal_one]
  refine ⟨funext hdirac, ?_, ?_⟩
  · intro hcon
    have h0 : cdf (Measure.dirac (0 : ℝ)) 0 = 1 := by
      rw [hdirac 0]
      norm_num
    have htend : Filter.Tendsto (cdf (Measure.dirac (0 : ℝ)))
        (nhdsWithin (0 : ℝ) (Iio 0)) (nhds (cdf (Measure.dirac (0 : ℝ)) 0)) :=
      Filter.Tendsto.mono_left (hcon.tendsto 0) nhdsWithin_le_nhds
    have hev : ∀ᶠ x in nhdsWithin (0 : ℝ) (Iio 0),
        cdf (Measure.dirac (0 : ℝ)) x = 0 := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx' : x < 0 := hx
      rw [hdirac x, ite_eq_left hx']
    have hconst : Filter.Tendsto (fun _ : ℝ => (0 : ℝ))
        (nhdsWithin (0 : ℝ) (Iio 0)) (nhds (cdf (Measure.dirac (0 : ℝ)) 0)) :=
      Filter.Tendsto.congr' hev htend
    have huniq := tendsto_nhds_unique hconst tendsto_const_nhds
    rw [h0] at huniq
    norm_num at huniq
  · intro hmono
    have e1 : cdf (Measure.dirac (0 : ℝ)) (-1) = 0 := by
      rw [hdirac (-1)]
      norm_num
    have e2 : cdf (Measure.dirac (0 : ℝ)) (-2) = 0 := by
      rw [hdirac (-2)]
      norm_num
    have hinj := hmono.injective (e1.trans e2.symm)
    norm_num at hinj

end QuantileLinkTest
