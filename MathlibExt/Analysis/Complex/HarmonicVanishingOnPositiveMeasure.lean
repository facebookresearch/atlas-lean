/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# Harmonic function vanishing on a set of positive measure is zero

The following OpenBMB notice applies to the adapted statement and its documentation.

Copyright (c) 2026 OpenBMB

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

Attribution and modification notice: the statement below is taken from openbmb/ma-proofbench at
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_88.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. The original ATLAS import converted
`theorem ma_proofbench_l2_88 … := by sorry` into the Batteries `theorem_wanted`
`eq_zero_of_harmonicOnNhd_of_vanishing_on_pos_volume`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.Complex.HarmonicVanishingOnPositiveMeasureWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system.
This change proves the theorem and moves it to the proved library.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.Convex.Topology
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Topology.Bases
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Instances.Real.Lemmas

/-! # Harmonic unique continuation from positive measure

Real analyticity makes each nontrivial one-dimensional section have isolated zeros.
Two coordinate sections and Fubini show that the zero set is null on a rectangle
where the function is not identically zero. A countable cover by rectangles and
the analytic identity theorem give the result on a connected open set.
-/

open Set Filter MeasureTheory

namespace MathlibExt.Analysis.Complex.HarmonicVanishingOnPositiveMeasureWanted

-- An analytic section that is not identically zero has isolated zeros.
private theorem countable_zeros_of_nonzero {f : ℝ → ℝ} {U : Set ℝ}
    (hf : AnalyticOnNhd ℝ f U) (hU : IsPreconnected U) {x : ℝ}
    (hx : x ∈ U) (hn : f x ≠ 0) : ({y | f y = 0} ∩ U).Countable := by
  rcases hf.eqOn_zero_or_eventually_ne_zero_of_preconnected hU with hz | hne
  · exact (hn (hz hx)).elim
  · have hmem : {y | f y = 0}ᶜ ∈ codiscreteWithin U := hne
    have hdisc := isDiscrete_of_codiscreteWithin hmem
    let : DiscreteTopology ↥({y | f y = 0} ∩ U) := isDiscrete_iff_discreteTopology.mp hdisc
    exact TopologicalSpace.separableSpace_iff_countable.mp inferInstance

-- Outside the countable exceptional set on a vertical section, each horizontal section
-- has a countable zero set. Fubini then gives a null planar zero set.
private theorem zero_rect_measure {F : ℝ × ℝ → ℝ} {U V : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hUc : IsPreconnected U) (hVc : IsPreconnected V)
    (hF : ContinuousOn F (U ×ˢ V))
    (hv : ∀ x ∈ U, AnalyticOnNhd ℝ (fun y => F (x, y)) V)
    (hh : ∀ y ∈ V, AnalyticOnNhd ℝ (fun x => F (x, y)) U)
    {x₀ y₀ : ℝ} (hx₀ : x₀ ∈ U) (hy₀ : y₀ ∈ V) (hn : F (x₀, y₀) ≠ 0) :
    (volume.prod volume) ({p | F p = 0} ∩ (U ×ˢ V)) = 0 := by
  have hM : MeasurableSet ({p | F p = 0} ∩ (U ×ˢ V)) := by
    let S := U ×ˢ V
    have hcont : Continuous (fun p : S => F p) :=
      continuousOn_iff_continuous_domRestrict.mp hF
    have hz : MeasurableSet {p : S | F p = 0} :=
      measurableSet_eq_fun hcont.measurable measurable_const
    have himage :=
      (MeasurableEmbedding.subtype_coe ((hU.prod hV).measurableSet)).measurableSet_image.mpr hz
    convert himage using 1
    ext p
    constructor
    · intro hp
      exact ⟨⟨p, hp.2⟩, hp.1, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨hp, p.property⟩
  have hey : ∀ᵐ y : ℝ ∂volume, y ∈ V → F (x₀, y) ≠ 0 := by
    apply ae_iff.mpr
    have heq : {y : ℝ | ¬ (y ∈ V → F (x₀, y) ≠ 0)} = {y | F (x₀, y) = 0} ∩ V := by
      ext y
      simp [and_comm]
    rw [heq]
    exact (countable_zeros_of_nonzero (hv x₀ hx₀) hVc hy₀ hn).measure_zero volume
  rw [Measure.prod_apply_symm hM, ← lintegral_zero]
  apply lintegral_congr_ae
  filter_upwards [hey] with y hy
  by_cases hV' : y ∈ V
  · have hcount := countable_zeros_of_nonzero (hh y hV') hUc hx₀ (hy hV')
    have heq : (fun x : ℝ => (x, y)) ⁻¹' ({p | F p = 0} ∩ (U ×ˢ V)) =
        {x | F (x, y) = 0} ∩ U := by
      ext x
      simp [hV']
    rw [heq]
    exact hcount.measure_zero volume
  · have heq : (fun x : ℝ => (x, y)) ⁻¹' ({p | F p = 0} ∩ (U ×ˢ V)) = ∅ := by
      ext x
      simp [hV']
    rw [heq, measure_empty]

-- Rational rectangles give a countable cover of any open planar domain.
private def ratRect (q : ℚ × ℚ × ℚ × ℚ) : Set (ℝ × ℝ) :=
  Ioo (q.1 : ℝ) (q.2.1 : ℝ) ×ˢ Ioo (q.2.2.1 : ℝ) (q.2.2.2 : ℝ)

private theorem open_contains_ratRect {D : Set (ℝ × ℝ)} (hD : IsOpen D)
    {p : ℝ × ℝ} (hp : p ∈ D) : ∃ q, p ∈ ratRect q ∧ ratRect q ⊆ D := by
  have hb := Real.isTopologicalBasis_Ioo_rat.prod Real.isTopologicalBasis_Ioo_rat
  obtain ⟨s, hs, hps, hsD⟩ := hb.exists_subset_of_mem_open hp hD
  rcases hs with ⟨U, hU, V, hV, rfl⟩
  simp only [mem_iUnion, mem_singleton_iff] at hU hV
  rcases hU with ⟨a, b, _, rfl⟩
  rcases hV with ⟨c, d, _, rfl⟩
  exact ⟨(a, b, c, d), hps, hsD⟩

private theorem analytic_zero_measure_prod {F : ℝ × ℝ → ℝ} {D : Set (ℝ × ℝ)}
    (hD : IsOpen D) (hDc : IsPreconnected D) (hF : AnalyticOnNhd ℝ F D)
    (hn : ¬ EqOn F 0 D) : volume ({p | F p = 0} ∩ D) = 0 := by
  classical
  let A (q : ℚ × ℚ × ℚ × ℚ) : Set (ℝ × ℝ) :=
    if ratRect q ⊆ D then {p | F p = 0} ∩ ratRect q else ∅
  have hA (q : ℚ × ℚ × ℚ × ℚ) : volume (A q) = 0 := by
    by_cases hd : ratRect q ⊆ D
    · simp only [A, ite_eq_left hd]
      by_cases hnon : (ratRect q).Nonempty
      · let U := Ioo (q.1 : ℝ) (q.2.1 : ℝ)
        let V := Ioo (q.2.2.1 : ℝ) (q.2.2.2 : ℝ)
        have ho : IsOpen (ratRect q) := isOpen_Ioo.prod isOpen_Ioo
        have hnonzero : ∃ p ∈ ratRect q, F p ≠ 0 := by
          by_contra! hzero
          obtain ⟨p, hp⟩ := hnon
          have hev : F =ᶠ[nhds p] 0 :=
            Filter.eventually_of_mem (ho.mem_nhds hp) fun x hx => hzero x hx
          exact hn (hF.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hDc (hd hp) hev)
        obtain ⟨⟨x₀, y₀⟩, hp, hpne⟩ := hnonzero
        have hcont : ContinuousOn F (U ×ˢ V) := fun p hp =>
          (hF p (hd hp)).continuousAt.continuousWithinAt
        change (volume.prod volume) ({p | F p = 0} ∩ (U ×ˢ V)) = 0
        refine zero_rect_measure isOpen_Ioo isOpen_Ioo
          (convex_Ioo _ _).isPreconnected (convex_Ioo _ _).isPreconnected hcont ?_ ?_
          hp.1 hp.2 hpne
        · intro x hx y hy
          have hsec : AnalyticAt ℝ (fun t : ℝ => (x, t)) y :=
            analyticAt_const.prod analyticAt_id
          exact (hF (x, y) (hd ⟨hx, hy⟩)).comp hsec
        · intro y hy x hx
          have hsec : AnalyticAt ℝ (fun t : ℝ => (t, y)) x :=
            analyticAt_id.prod analyticAt_const
          exact AnalyticAt.comp (f := fun t : ℝ => (t, y)) (x := x)
            (hF (x, y) (hd ⟨hx, hy⟩)) hsec
      · rw [Set.not_nonempty_iff_eq_empty.mp hnon, inter_empty, measure_empty]
    · simp only [A, ite_eq_right hd, measure_empty]
  have hsub : {p | F p = 0} ∩ D ⊆ ⋃ q, A q := by
    intro p hp
    obtain ⟨q, hpq, hq⟩ := open_contains_ratRect hD hp.2
    refine mem_iUnion.mpr ⟨q, ?_⟩
    simp only [A, ite_eq_left hq]
    exact ⟨hp.1, hpq⟩
  exact le_antisymm ((measure_mono hsub).trans_eq (measure_iUnion_null_iff.mpr hA)) bot_le

private theorem harmonic_vanishing_positive_measure
    (Ω : Set ℂ) (h : ℂ → ℝ) (hΩ_open : IsOpen Ω) (hΩ_connected : IsConnected Ω)
    (hh_harmonic : InnerProductSpace.HarmonicOnNhd h Ω)
    (h_zero_on_pos_meas : ∃ s : Set ℂ, s ⊆ Ω ∧ 0 < volume s ∧ ∀ z ∈ s, h z = 0) :
    ∀ z ∈ Ω, h z = 0 := by
  by_contra! hn
  obtain ⟨s, hsΩ, hspos, hszero⟩ := h_zero_on_pos_meas
  let e := Complex.equivRealProdCLM
  let D := e.symm ⁻¹' Ω
  let F := h ∘ e.symm
  have hD : IsOpen D := hΩ_open.preimage e.symm.continuous
  have himage : D = e '' Ω := by
    ext p
    constructor
    · intro hp
      exact ⟨e.symm p, hp, e.apply_symm_apply p⟩
    · rintro ⟨p, hp, rfl⟩
      change e.symm (e p) ∈ Ω
      rwa [e.symm_apply_apply]
  have hDc : IsPreconnected D :=
    himage ▸ (hΩ_connected.isPreconnected.image _ e.continuous.continuousOn)
  have hF : AnalyticOnNhd ℝ F D := fun p hp =>
    (HarmonicAt.analyticAt (hh_harmonic (e.symm p) hp)).comp
      (e.symm.toContinuousLinearMap.analyticAt p)
  have hFn : ¬ EqOn F 0 D := by
    intro heq
    obtain ⟨z, hz, hzne⟩ := hn
    have hmem : e z ∈ D := himage.symm ▸ mem_image_of_mem e hz
    apply hzne
    have hv := heq hmem
    change h (e.symm (e z)) = 0 at hv
    rwa [e.symm_apply_apply] at hv
  let Z := {p | F p = 0} ∩ D
  have hzvol : volume Z = 0 := analytic_zero_measure_prod hD hDc hF hFn
  have hpre : volume (Complex.measurableEquivRealProd ⁻¹' Z) = 0 := by
    rw [Complex.volume_preserving_equiv_real_prod.measure_preimage
      (NullMeasurableSet.of_null hzvol), hzvol]
  have hin : s ⊆ Complex.measurableEquivRealProd ⁻¹' Z := by
    intro z hz
    change F (e z) = 0 ∧ e.symm (e z) ∈ Ω
    dsimp only [F, Function.comp_apply]
    rw [e.symm_apply_apply]
    exact ⟨hszero z hz, hsΩ hz⟩
  exact (not_lt_of_ge ((measure_mono hin).trans_eq hpre)) hspos

/-- **A harmonic function vanishing on a set of positive measure is zero.** Let
$\Omega \subseteq \mathbb{C}$ be a nonempty connected open set and let
$h : \mathbb{C} \to \mathbb{R}$ be harmonic on $\Omega$. If $h$ vanishes on some subset
$s \subseteq \Omega$ of positive (outer) Lebesgue measure, then $h(z) = 0$ for all $z \in \Omega$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functions of a complex
variable; Miscellaneous topics of analysis in the complex plane),
`benchmark/level2/ma_proofbench_l2_88.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem eq_zero_of_harmonicOnNhd_of_vanishing_on_pos_volume
  (Ω : Set ℂ) (h : ℂ → ℝ) (hΩ_open : IsOpen Ω) (hΩ_connected : IsConnected Ω)
  (hh_harmonic : InnerProductSpace.HarmonicOnNhd h Ω)
  (h_zero_on_pos_meas :
    ∃ s : Set ℂ, s ⊆ Ω ∧ 0 < MeasureTheory.volume s ∧ ∀ z ∈ s, h z = 0) :
  ∀ z ∈ Ω, h z = 0 := by
  exact harmonic_vanishing_positive_measure Ω h hΩ_open hΩ_connected hh_harmonic h_zero_on_pos_meas

end MathlibExt.Analysis.Complex.HarmonicVanishingOnPositiveMeasureWanted
