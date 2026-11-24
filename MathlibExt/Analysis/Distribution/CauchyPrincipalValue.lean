/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Cauchy principal value of a Schwartz function divided by its argument

Symmetric truncations of the integral of a real Schwartz function divided by its argument
converge as the cutoff tends to zero from the right.
-/

open Filter MeasureTheory Set
open scoped SchwartzMap

namespace MathlibExt.Analysis.Distribution.CauchyPrincipalValueWanted

private theorem integrableOn_div_of_le_abs {f : ℝ → ℝ} (hf : Integrable f)
    {s : Set ℝ} (hs : MeasurableSet s) {a : ℝ} (ha : 0 < a)
    (hbound : ∀ x ∈ s, a ≤ |x|) :
    IntegrableOn (fun x => f x / x) s := by
  have hm : AEMeasurable (fun x => f x / x) volume :=
    hf.aestronglyMeasurable.aemeasurable.div measurable_id.aemeasurable
  refine (hf.norm.const_mul a⁻¹).integrableOn.mono'
    (hm.aestronglyMeasurable.mono_measure Measure.restrict_le_self) ?_
  filter_upwards [ae_restrict_mem hs] with x hx
  rw [norm_div, Real.norm_eq_abs x, mul_comm, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left (norm_nonneg _) ha (hbound x hx)

/--
**Existence of the Cauchy principal value of $\varphi(x)/x$.** For every real-valued Schwartz
function $\varphi$ on $\mathbb{R}$ there is a real number $L$ such that
$\int_{\{x \in \mathbb{R} \,:\, |x| \ge \varepsilon\}} \varphi(x)/x \, dx \to L$ as
$\varepsilon \to 0^+$, the integrals being taken with respect to Lebesgue measure.

Sources: Mathlib `docs/undergrad.yaml`, section "Distribution calculus" /
"Distributions on R^d" / entry "Cauchy principal values";
F. Friedlander and M. Joshi, *Introduction to the Theory of Distributions*, Ch. 2.
-/
public theorem cauchyPrincipalValue_exists (φ : 𝓢(ℝ, ℝ)) :
    ∃ L : ℝ, Filter.Tendsto (fun ε : ℝ => ∫ x in {x : ℝ | ε ≤ |x|}, φ x / x ∂volume)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  -- Reflect the negative half-line and extend the paired quotient across zero.
  let numerator : ℝ → ℝ := fun x => φ x - φ (-x)
  let paired := dslope numerator 0
  have hd : Differentiable ℝ numerator :=
    φ.differentiable.sub (φ.differentiable.comp differentiable_neg)
  have hc : Continuous paired := by
    rw [continuous_iff_continuousAt]
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · exact continuousAt_dslope_same.mpr hd.differentiableAt
    · exact (continuousAt_dslope_of_ne hx).mpr hd.continuous.continuousAt
  have hpaired {x : ℝ} (hx : x ≠ 0) :
      paired x = φ x / x - φ (-x) / x := by
    change dslope numerator 0 x = _
    rw [dslope_of_ne _ hx, slope, ← sub_div]
    simp [numerator, div_eq_inv_mul, smul_eq_mul]
  have hφ : Integrable (φ : ℝ → ℝ) := φ.integrable
  have hreflect : Integrable (fun x => φ (-x)) :=
    (Measure.measurePreserving_neg volume).integrable_comp_of_integrable hφ
  have hpos {ε : ℝ} (hε : 0 < ε) :
      IntegrableOn (fun x => φ x / x) (Ici ε) :=
    integrableOn_div_of_le_abs hφ measurableSet_Ici hε fun x hx => hx.trans (le_abs_self x)
  have hreflectPos {ε : ℝ} (hε : 0 < ε) :
      IntegrableOn (fun x => φ (-x) / x) (Ici ε) :=
    integrableOn_div_of_le_abs hreflect measurableSet_Ici hε fun x hx => hx.trans (le_abs_self x)
  have htail : IntegrableOn paired (Ici 1) :=
    (integrableOn_congr_fun
      (fun x hx => hpaired (ne_of_gt (zero_lt_one.trans_le hx))) measurableSet_Ici).mpr
        ((hpos zero_lt_one).sub (hreflectPos zero_lt_one))
  have hwhole : IntegrableOn paired (Ici 0) := by
    rw [← Icc_union_Ioi_eq_Ici (zero_le_one : (0 : ℝ) ≤ 1)]
    exact (hc.continuousOn.integrableOn_compact isCompact_Icc).union
      (htail.mono_set Ioi_subset_Ici_self)
  -- The cutoff removes an interval whose integral tends to zero.
  let L := ∫ x in Ici 0, paired x
  have hprimitive := intervalIntegral.continuous_primitive
    (fun a b => hc.intervalIntegrable (μ := volume) a b) 0
  have hlimit : Tendsto (fun ε : ℝ => L - ∫ x in 0..ε, paired x)
      (nhdsWithin 0 (Ioi 0)) (nhds L) := by
    have hcont : ContinuousAt (fun ε : ℝ => L - ∫ x in 0..ε, paired x) 0 :=
      (continuous_const.sub hprimitive).continuousAt
    simpa only [intervalIntegral.integral_same, sub_zero] using
      hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  refine ⟨L, hlimit.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with ε hε
  have hεpos : 0 < ε := hε
  have hsplit : {x : ℝ | ε ≤ |x|} = Ici ε ∪ Iic (-ε) := by
    ext x
    change ε ≤ |x| ↔ ε ≤ x ∨ x ≤ -ε
    rw [le_abs, le_neg]
  have hneg : IntegrableOn (fun x => φ x / x) (Iic (-ε)) :=
    integrableOn_div_of_le_abs hφ measurableSet_Iic hεpos fun x hx =>
      (le_neg.mp (show x ≤ -ε from hx)).trans (neg_le_abs x)
  have hreflection :
      (∫ x in Iic (-ε), φ x / x) = -(∫ x in Ici ε, φ (-x) / x) := by
    rw [← integral_comp_neg_Ioi ε (fun x : ℝ => φ x / x), integral_Ici_eq_integral_Ioi,
      ← integral_neg]
    simp only [div_neg]
  have htrunc :
      (∫ x in {x : ℝ | ε ≤ |x|}, φ x / x) = ∫ x in Ici ε, paired x := by
    rw [hsplit, setIntegral_union (Ici_disjoint_Iic.mpr (not_le_of_gt (neg_lt_self hεpos)))
        measurableSet_Iic
        (hpos hεpos) hneg, hreflection, ← sub_eq_add_neg,
      ← integral_sub (hpos hεpos) (hreflectPos hεpos)]
    exact setIntegral_congr_fun measurableSet_Ici fun x hx =>
      (hpaired (ne_of_gt (hεpos.trans_le hx))).symm
  rw [htrunc, ← intervalIntegral.integral_Ici_sub_Ici' hwhole
    (hwhole.mono_set (Ici_subset_Ici.mpr hεpos.le))]
  exact sub_sub_cancel _ _

end MathlibExt.Analysis.Distribution.CauchyPrincipalValueWanted
