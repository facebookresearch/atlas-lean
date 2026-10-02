/-
Copyright (c) 2026 Paul-Antoine Bonin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul-Antoine Bonin
-/
import Mathlib.Probability.Distributions.Uniform

/-!
# CDIS Probabilités V: the rejection method

* id 97: uniform law on the subgraph of a density. If `X` has density `f` and `U` is uniform
  on `]0,1[` and independent of `X`, then `(X, U f(X))` is uniform on
  `A_f = {(x, y) | 0 ≤ y ≤ f(x)}`.
* id 96: stability of the uniform law under conditioning. If `U` is uniform on `A` and
  `B ⊆ A`, then `U` conditioned on `U ∈ B` is uniform on `B`.

The course asks `ℓ(A) > 0` and `ℓ(B) > 0`; the Lean statement only needs `ℓ(A) < ∞`
(when `ℓ(B) = 0` both sides are the zero measure).
-/

open MeasureTheory ProbabilityTheory Set

namespace CDIS

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {P : Measure Ω} {μ : Measure E}

/-- Conditioning on `{U ∈ B}` then pushing forward by `U` is conditioning the law of `U` on `B`. -/
lemma map_cond_preimage {U : Ω → E} (hU : Measurable U) {B : Set E} (hB : MeasurableSet B) :
    (P[|U ⁻¹' B]).map U = (P.map U)[|B] := by
  simp only [ProbabilityTheory.cond, Measure.map_apply hU hB]
  rw [Measure.map_smul, Measure.restrict_map hU hB]
  exact hU.aemeasurable

/-- CDIS P.V, id 96 (stability of the uniform law under conditioning). -/
theorem isUniform_cond_preimage {U : Ω → E} (hU : Measurable U) {A B : Set E}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hBA : B ⊆ A) (hAfin : μ A ≠ ⊤)
    (hu : pdf.IsUniform U A P μ) : pdf.IsUniform U B (P[|U ⁻¹' B]) μ where
  aemeasurable := hU.aemeasurable
  map_eq := by
    rw [map_cond_preimage hU hB, hu.map_eq, cond_cond_eq_cond_inter' hA hB hAfin,
      inter_eq_right.2 hBA]

/-- The subgraph `A_f = {(x, y) | 0 ≤ y ≤ f(x)}` of a function `f : ℝ → ℝ`. -/
def subgraph (f : ℝ → ℝ) : Set (ℝ × ℝ) := {p | 0 ≤ p.2 ∧ p.2 ≤ f p.1}

lemma measurableSet_subgraph {f : ℝ → ℝ} (hf : Measurable f) : MeasurableSet (subgraph f) :=
  (measurableSet_le measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd (hf.comp measurable_fst))

/-- For `c ≥ 0`: `c · P(U c ∈ t) = ℓ(t ∩ [0, c])` when `U` is uniform on `]0,1[`. -/
lemma ofReal_mul_volume_preimage_mul {c : ℝ} (hc : 0 ≤ c) {t : Set ℝ} (ht : MeasurableSet t) :
    ENNReal.ofReal c * volume.restrict (Ioo (0 : ℝ) 1) ((· * c) ⁻¹' t) =
      volume (t ∩ Icc 0 c) := by
  rcases hc.eq_or_lt with rfl | hc
  · simp only [ENNReal.ofReal_zero, zero_mul, Icc_self]
    exact (measure_mono_null inter_subset_right (measure_singleton 0)).symm
  rw [Measure.restrict_apply (measurable_mul_const c ht)]
  have hset : (· * c) ⁻¹' t ∩ Ioo 0 1 = (· * c) ⁻¹' (t ∩ Ioo 0 c) := by
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_Ioo]
    constructor
    · rintro ⟨h, h0, h1⟩
      exact ⟨h, by positivity, by nlinarith⟩
    · rintro ⟨h, h0, h1⟩
      exact ⟨h, pos_of_mul_pos_left h0 hc.le, (mul_lt_iff_lt_one_left hc).1 h1⟩
  rw [hset, Real.volume_preimage_mul_right hc.ne', ← mul_assoc, ← ENNReal.ofReal_mul hc.le,
    abs_inv, abs_of_pos hc, mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one, one_mul]
  exact measure_congr (Filter.EventuallyEqSet.inter (ae_eq_refl t) Ioo_ae_eq_Icc)

/-- CDIS P.V, id 97 (uniform law on the subgraph of a density). -/
theorem isUniform_subgraph [IsProbabilityMeasure P] {f : ℝ → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) {X U : Ω → ℝ}
    (hX : HasLaw X (volume.withDensity fun x ↦ ENNReal.ofReal (f x)) P)
    (hU : HasLaw U (volume.restrict (Ioo (0 : ℝ) 1)) P) (hXU : IndepFun X U P) :
    pdf.IsUniform (fun ω ↦ (X ω, U ω * f (X ω))) (subgraph f) P volume := by
  set μX := volume.withDensity fun x ↦ ENNReal.ofReal (f x)
  set ν := volume.restrict (Ioo (0 : ℝ) 1)
  set T : ℝ × ℝ → ℝ × ℝ := fun p ↦ (p.1, p.2 * f p.1) with hTdef
  have hT : Measurable T := measurable_fst.prodMk (measurable_snd.mul (hf.comp measurable_fst))
  have hXU' : AEMeasurable (fun ω ↦ (X ω, U ω)) P := hX.aemeasurable.prodMk hU.aemeasurable
  have hjoint : P.map (fun ω ↦ (X ω, U ω)) = μX.prod ν := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hU.aemeasurable).1 hXU,
      hX.map_eq, hU.map_eq]
  have hlaw : P.map (fun ω ↦ (X ω, U ω * f (X ω))) = (μX.prod ν).map T := by
    rw [← hjoint, AEMeasurable.map_map_of_aemeasurable hT.aemeasurable hXU']
    rfl
  have : IsProbabilityMeasure ((μX.prod ν).map T) := by
    rw [← hlaw]
    exact (Measure.isProbabilityMeasure_map_iff (hT.comp_aemeasurable hXU')).2 ‹_›
  -- the two measures agree on rectangles
  have hrect : ∀ {s t : Set ℝ}, MeasurableSet s → MeasurableSet t →
      (μX.prod ν).map T (s ×ˢ t) = volume.restrict (subgraph f) (s ×ˢ t) := by
    intro s t hs ht
    have hst := hs.prod ht
    rw [Measure.map_apply hT hst, Measure.prod_apply (hT hst), Measure.restrict_apply hst,
      Measure.volume_eq_prod, Measure.prod_apply (hst.inter (measurableSet_subgraph hf)),
      lintegral_withDensity_eq_lintegral_mul _ hf.ennreal_ofReal
        (measurable_measure_prodMk_left (hT hst))]
    refine lintegral_congr fun x ↦ ?_
    by_cases hx : x ∈ s
    · have h1 : Prod.mk x ⁻¹' (T ⁻¹' (s ×ˢ t)) = (· * f x) ⁻¹' t := by
        ext u; simp [hTdef, hx]
      have h2 : Prod.mk x ⁻¹' (s ×ˢ t ∩ subgraph f) = t ∩ Icc 0 (f x) := by
        ext y; simp [subgraph, hx]
      simp only [Pi.mul_apply, h1, h2]
      exact ofReal_mul_volume_preimage_mul (hf0 x) ht
    · have h1 : Prod.mk x ⁻¹' (T ⁻¹' (s ×ˢ t)) = ∅ := by ext u; simp [hTdef, hx]
      have h2 : Prod.mk x ⁻¹' (s ×ˢ t ∩ subgraph f) = ∅ := by ext y; simp [hx]
      simp [h1, h2]
  have heq : (μX.prod ν).map T = volume.restrict (subgraph f) := Measure.ext_prod hrect
  have hA : volume (subgraph f) = 1 := by
    have := hrect MeasurableSet.univ MeasurableSet.univ
    rwa [univ_prod_univ, measure_univ, Measure.restrict_apply_univ, eq_comm] at this
  refine ⟨(hT.comp_aemeasurable hXU'), ?_⟩
  rw [hlaw, heq, ProbabilityTheory.cond, hA, inv_one, one_smul]

end CDIS
