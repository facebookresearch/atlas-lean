/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.EMetricSpace.BoundedVariation

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.VectorMeasure.IntegrationByParts
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-!
# Length of continuously differentiable curves

This file proves that the variation of a continuously differentiable Banach-space-valued curve
on a compact interval is the integral of the norm of its derivative.
-/

open MeasureTheory Set
open scoped ENNReal

@[expose] public section

namespace MetaMathlibExt

private lemma curveLength_pairwiseDisjoint_Ioc {u : ℕ → ℝ} (hu : Monotone u) (n : ℕ) :
    (↑(Finset.range n) : Set ℕ).PairwiseDisjoint
      (fun i => Ioc (u i) (u (i + 1))) := by
  rintro i hi j hj hij
  simp only [Function.onFun]
  apply Set.disjoint_left.2
  intro x hxi hxj
  simp only [mem_Ioc] at hxi hxj
  rcases lt_or_gt_of_ne hij with hij' | hij'
  · exact (not_lt_of_ge (hxi.2.trans (hu (Nat.add_one_le_iff.2 hij')))) hxj.1
  · exact (not_lt_of_ge (hxj.2.trans (hu (Nat.add_one_le_iff.2 hij')))) hxi.1

private theorem curveLength_indefiniteIntegral_boundedVariation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {h : ℝ → E} (hh : Integrable h) (c : ℝ) :
    BoundedVariationOn (fun x => ∫ t in c..x, h t) univ := by
  let μ : VectorMeasure ℝ E := volume.withDensityᵥ h
  have hμlt : μ.variation univ < ∞ := by
    rw [show μ = volume.withDensityᵥ h from rfl, Measure.variation_withDensityᵥ hh,
      withDensity_apply _ MeasurableSet.univ]
    simpa [HasFiniteIntegral] using hh.hasFiniteIntegral
  apply ne_top_of_le_ne_top hμlt.ne
  rw [eVariationOn]
  apply iSup_le
  rintro ⟨n, u, hu, -⟩
  calc
    (∑ i ∈ Finset.range n,
        edist (∫ t in c..u (i + 1), h t) (∫ t in c..u i, h t)) =
        ∑ i ∈ Finset.range n, ‖μ (Ioc (u i) (u (i + 1)))‖ₑ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [edist_eq_enorm_sub, show μ = volume.withDensityᵥ h from rfl,
        withDensityᵥ_apply hh measurableSet_Ioc,
        ← intervalIntegral.integral_of_le (hu (by omega))]
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (hh.intervalIntegrable (a := c) (b := u i))
        (hh.intervalIntegrable (a := u i) (b := u (i + 1)))
      rw [← hadd]
      abel_nf
    _ ≤ ∑ i ∈ Finset.range n, μ.variation (Ioc (u i) (u (i + 1))) := by
      gcongr with i hi
      exact μ.enorm_measure_le_variation _
    _ = μ.variation (⋃ i ∈ Finset.range n, Ioc (u i) (u (i + 1))) := by
      rw [measure_biUnion_finset (curveLength_pairwiseDisjoint_Ioc hu n) (by simp)]
    _ ≤ μ.variation univ := measure_mono (subset_univ _)

private theorem curveLength_vectorMeasure_indefiniteIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {h : ℝ → E} (hh : Integrable h) (c : ℝ) :
    (curveLength_indefiniteIntegral_boundedVariation hh c).vectorMeasure =
      volume.withDensityᵥ h := by
  apply VectorMeasure.ext_of_Icc
  intro x y hxy
  rw [(curveLength_indefiniteIntegral_boundedVariation hh c).vectorMeasure_Icc hxy]
  have hcont : Continuous (fun z => ∫ t in c..z, h t) := hh.continuous_primitive c
  rw [hcont.continuousAt.continuousWithinAt.rightLim_eq,
    hcont.continuousAt.continuousWithinAt.leftLim_eq,
    withDensityᵥ_apply hh measurableSet_Icc, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hxy]
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hh.intervalIntegrable (a := c) (b := x))
    (hh.intervalIntegrable (a := x) (b := y))
  rw [← hadd]
  abel_nf

private lemma curveLength_eVariationOn_sub_const
    {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) (c : E) (s : Set ℝ) :
    eVariationOn (fun x => f x - c) s = eVariationOn f s := by
  rw [eVariationOn, eVariationOn]
  congr 1 with p
  apply Finset.sum_congr rfl
  intro i hi
  rw [edist_eq_enorm_sub, edist_eq_enorm_sub]
  congr 1
  abel

private theorem curveLength_integral_indicator_derivWithin_eq_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {γ : ℝ → E} {a b x : ℝ} (hab : a < b)
    (hγ : ContDiffOn ℝ 1 γ (Icc a b)) (hx : x ∈ Icc a b) :
    ∫ t in a..x, (Icc a b).indicator (derivWithin γ (Icc a b)) t = γ x - γ a := by
  have hax : a ≤ x := hx.1
  have hsub : Icc a x ⊆ Icc a b := by
    intro t ht
    exact ⟨ht.1, ht.2.trans hx.2⟩
  rw [intervalIntegral.integral_congr (g := derivWithin γ (Icc a b)) (fun t ht => by
    apply Set.indicator_of_mem
    exact hsub (by simpa [uIcc_of_le hax] using ht))]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hax
  · exact hγ.continuousOn.mono hsub
  · intro t ht
    have ht' : t ∈ Ioo a b := ⟨ht.1, ht.2.trans_le hx.2⟩
    exact (hγ.differentiableOn_one t ⟨ht'.1.le, ht'.2.le⟩).hasDerivWithinAt.hasDerivAt
      (Icc_mem_nhds ht'.1 ht'.2)
  · have hcont : ContinuousOn (derivWithin γ (Icc a b)) (uIcc a x) := by
      simpa [uIcc_of_le hax] using
        (hγ.continuousOn_derivWithin (uniqueDiffOn_Icc hab) (by norm_num)).mono hsub
    exact hcont.intervalIntegrable

private theorem curveLength_lintegral_indicator_derivWithin_eq_ofReal_integral_norm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {γ : ℝ → E} {a b : ℝ} (hab : a < b)
    (hγ : ContDiffOn ℝ 1 γ (Icc a b)) :
    ∫⁻ t in Ioc a b, ‖(Icc a b).indicator (derivWithin γ (Icc a b)) t‖ₑ =
      ENNReal.ofReal (∫ t in a..b, ‖derivWithin γ (Icc a b) t‖) := by
  let g := derivWithin γ (Icc a b)
  let h := (Icc a b).indicator g
  have hgcont : ContinuousOn g (Icc a b) :=
    hγ.continuousOn_derivWithin (uniqueDiffOn_Icc hab) (by norm_num)
  have hh : Integrable h := hgcont.integrableOn_Icc.integrable_indicator measurableSet_Icc
  change ∫⁻ t in Ioc a b, ‖h t‖ₑ = ENNReal.ofReal (∫ t in a..b, ‖g t‖)
  rw [← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm hh.restrict,
    intervalIntegral.integral_of_le hab.le]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  have htIcc : t ∈ Icc a b := ⟨ht.1.le, ht.2⟩
  simp [h, htIcc]

/-- On an interval, integrating the norm of `derivWithin` gives the same result as integrating
the norm of `deriv`. -/
theorem _root_.intervalIntegral.integral_norm_deriv_eq_integral_norm_derivWithin_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, ‖deriv f t‖) = ∫ t in a..b, ‖derivWithin f (Icc a b) t‖ := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne b] with t htb
  intro ht
  rw [uIoc_of_le hab] at ht
  have ht' : t ∈ Ioo a b := ⟨ht.1, lt_of_le_of_ne ht.2 htb⟩
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht'.1 ht'.2)]

/-- The variation of a `C¹` curve on `[a, b]` is the integral of the norm of its derivative
within `[a, b]`. -/
theorem _root_.ContDiffOn.eVariationOn_Icc_eq_ofReal_integral_norm_derivWithin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {γ : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContDiffOn ℝ 1 γ (Icc a b)) :
    eVariationOn γ (Icc a b) =
      ENNReal.ofReal (∫ t in a..b, ‖derivWithin γ (Icc a b) t‖) := by
  rcases hab.eq_or_lt with rfl | hab
  · rw [intervalIntegral.integral_same, ENNReal.ofReal_zero]
    exact eVariationOn.subsingleton γ (by simp [Set.Subsingleton])
  let g := derivWithin γ (Icc a b)
  let h := (Icc a b).indicator g
  let F := fun x => ∫ t in a..x, h t
  have hgcont : ContinuousOn g (Icc a b) :=
    hγ.continuousOn_derivWithin (uniqueDiffOn_Icc hab) (by norm_num)
  have hh : Integrable h := hgcont.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hF : EqOn F (fun x => γ x - γ a) (Icc a b) := by
    intro x hx
    simpa [F, h, g] using curveLength_integral_indicator_derivWithin_eq_sub hab hγ hx
  have hFcont : Continuous F := by
    simpa [F] using hh.continuous_primitive a
  have hbv : BoundedVariationOn F univ := by
    simpa [F] using curveLength_indefiniteIntegral_boundedVariation hh a
  have hvm : hbv.vectorMeasure = volume.withDensityᵥ h := by
    simpa [F] using curveLength_vectorMeasure_indefiniteIntegral hh a
  have hright : Function.rightLim F = F := by
    funext x
    exact hFcont.continuousAt.continuousWithinAt.rightLim_eq
  calc
    eVariationOn γ (Icc a b) = eVariationOn (fun x => γ x - γ a) (Icc a b) :=
      (curveLength_eVariationOn_sub_const γ (γ a) (Icc a b)).symm
    _ = eVariationOn F (Icc a b) := (eVariationOn.eq_of_eqOn hF).symm
    _ = eVariationOn F (Ioc a b) :=
      (eVariationOn.eVariationOn_Ioc_eq_Icc_of_continuousWithinAt
        hFcont.continuousAt.continuousWithinAt).symm
    _ = eVariationOn (Function.rightLim F) (Ioc a b) := by rw [hright]
    _ = hbv.vectorMeasure.variation (Ioc a b) := hbv.variation_vectorMeasure_Ioc.symm
    _ = (volume.withDensityᵥ h).variation (Ioc a b) := by rw [hvm]
    _ = (volume.withDensity fun x => ‖h x‖ₑ) (Ioc a b) := by
      rw [Measure.variation_withDensityᵥ hh]
    _ = ∫⁻ x in Ioc a b, ‖h x‖ₑ := withDensity_apply _ measurableSet_Ioc
    _ = ENNReal.ofReal (∫ t in a..b, ‖derivWithin γ (Icc a b) t‖) := by
      simpa [h, g] using
        curveLength_lintegral_indicator_derivWithin_eq_ofReal_integral_norm hab hγ

/-- **Length of a $C^1$ curve.** Let $E$ be a real Banach space, let $a \le b$ be real numbers,
and let $\gamma : \mathbb{R} \to E$ be continuously differentiable on $[a, b]$. Then the total
variation of $\gamma$ on $[a, b]$ (its length, a priori a value in $[0, \infty]$) equals
$\int_a^b \lVert \gamma'(t) \rVert \, dt$.

Proof: Extend the derivative of $\gamma$ relative to $[a, b]$ by zero outside the interval and
identify the vector measure of its primitive with the corresponding density vector measure. The
variation of that measure is the integral of the norm, and the ordinary derivative agrees with the
derivative relative to $[a, b]$ almost everywhere on the interval.

Proves `Wanted` entry `curve_length_eq_integral_norm_deriv`.

Sources: `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` /
`Submanifolds of R^n`, entry `curve length` (unmapped);
W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 6;
stable ref https://en.wikipedia.org/wiki/Arc_length.
-/
theorem curve_length_eq_integral_norm_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {γ : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b)) :
    eVariationOn γ (Set.Icc a b) = ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖) := by
  calc
    eVariationOn γ (Set.Icc a b) =
        ENNReal.ofReal (∫ t in a..b, ‖derivWithin γ (Set.Icc a b) t‖) :=
      ContDiffOn.eVariationOn_Icc_eq_ofReal_integral_norm_derivWithin hab hγ
    _ = ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖) := by
      rw [← intervalIntegral.integral_norm_deriv_eq_integral_norm_derivWithin_Icc γ hab]

end MetaMathlibExt
