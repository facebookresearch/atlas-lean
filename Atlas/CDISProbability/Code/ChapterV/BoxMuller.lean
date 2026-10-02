/-
Copyright (c) 2026 Paul-Antoine Bonin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul-Antoine Bonin
-/
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.HasLaw

/-!
# CDIS Probabilités V: the Box-Muller transform

* id 98: if `U` and `V` are independent and uniform on `]0,1[`, then
  `X = √(-2 ln U) cos(2πV)` and `Y = √(-2 ln U) sin(2πV)` are independent standard Gaussians.

Proof. Substitute `u = e^{-r²/2}` (`r > 0`) and `v = (θ + π) / 2π` (`θ ∈ ]-π, π[`). The Jacobian
is `r e^{-r²/2} / 2π`, and the Box-Muller map becomes `(r, θ) ↦ -(r cos θ, r sin θ)`. Mathlib's
change of variables to polar coordinates (`lintegral_comp_polarCoord_symm`) turns the result
into an integral against the standard Gaussian density of `ℝ²`, which is invariant under
`x ↦ -x`.
-/

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal

namespace CDIS

/-- The Box-Muller map `(u, v) ↦ √(-2 ln u) (cos 2πv, sin 2πv)`. -/
noncomputable def boxMuller (w : ℝ × ℝ) : ℝ × ℝ :=
  (√(-2 * log w.1) * cos (2 * π * w.2), √(-2 * log w.1) * sin (2 * π * w.2))

lemma measurable_boxMuller : Measurable boxMuller := by
  unfold boxMuller
  fun_prop

section Substitution

lemma image_exp_neg_sq_Ioi : (fun r : ℝ ↦ exp (-r ^ 2 / 2)) '' Ioi 0 = Ioo 0 1 := by
  ext u
  simp only [mem_image, mem_Ioi, mem_Ioo]
  constructor
  · rintro ⟨r, hr, rfl⟩
    refine ⟨exp_pos _, ?_⟩
    rw [← exp_zero]
    exact exp_lt_exp.2 (by nlinarith)
  · rintro ⟨hu0, hu1⟩
    have hlog : log u < 0 := log_neg hu0 hu1
    refine ⟨√(-2 * log u), sqrt_pos.2 (by linarith), ?_⟩
    rw [sq_sqrt (by linarith), show -(-2 * log u) / 2 = log u by ring, exp_log hu0]

lemma image_affine_Ioo : (fun θ : ℝ ↦ (θ + π) / (2 * π)) '' Ioo (-π) π = Ioo 0 1 := by
  ext v
  simp only [mem_image, mem_Ioo]
  have hπ : 0 < 2 * π := by positivity
  constructor
  · rintro ⟨θ, ⟨h1, h2⟩, rfl⟩
    exact ⟨div_pos (by linarith) hπ, (div_lt_one hπ).2 (by linarith)⟩
  · rintro ⟨hv0, hv1⟩
    refine ⟨2 * π * v - π, ⟨by nlinarith [pi_pos], by nlinarith [pi_pos]⟩, ?_⟩
    field_simp
    ring

/-- Substitution `u = e^{-r²/2}` on `]0,1[`. -/
lemma lintegral_Ioo_eq_lintegral_Ioi (H : ℝ → ℝ≥0∞) :
    ∫⁻ u in Ioo 0 1, H u =
      ∫⁻ r in Ioi 0, ENNReal.ofReal (r * exp (-r ^ 2 / 2)) * H (exp (-r ^ 2 / 2)) := by
  rw [← image_exp_neg_sq_Ioi, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (f' := fun r ↦ -(r * exp (-r ^ 2 / 2)))]
  · refine setLIntegral_congr_fun measurableSet_Ioi fun r hr ↦ ?_
    rw [abs_neg, abs_of_pos (mul_pos hr (exp_pos _))]
  · intro r _
    have hin : HasDerivAt (fun r : ℝ ↦ -r ^ 2 / 2) (-r) r := by
      convert (hasDerivAt_pow 2 r).neg.div_const 2 using 1
      ring
    refine (hin.exp.congr_deriv ?_).hasDerivWithinAt
    ring
  · intro r hr s hs hrs
    have h := exp_injective hrs
    have : r ^ 2 = s ^ 2 := by linarith
    exact (sq_eq_sq₀ (le_of_lt hr) (le_of_lt hs)).1 this

/-- Substitution `v = (θ + π) / 2π` on `]0,1[`. -/
lemma lintegral_Ioo_eq_lintegral_Ioo_pi (G : ℝ → ℝ≥0∞) :
    ∫⁻ v in Ioo 0 1, G v =
      ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal (1 / (2 * π)) * G ((θ + π) / (2 * π)) := by
  rw [← image_affine_Ioo, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
    (f' := fun _ ↦ 1 / (2 * π))]
  · refine setLIntegral_congr_fun measurableSet_Ioo fun θ _ ↦ ?_
    rw [abs_of_pos (by positivity)]
  · intro θ _
    refine (((hasDerivAt_id θ).add_const π).div_const (2 * π)).hasDerivWithinAt.congr_deriv ?_
    simp
  · intro a _ b _ hab
    have hπ : (2 * π) ≠ 0 := by positivity
    simp only at hab
    field_simp at hab
    linarith

/-- After the substitution the Box-Muller map is minus the polar-coordinates map. -/
lemma boxMuller_subst {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    boxMuller (exp (-r ^ 2 / 2), (θ + π) / (2 * π)) = -polarCoord.symm (r, θ) := by
  have h2π : 2 * π * ((θ + π) / (2 * π)) = θ + π := by field_simp
  have hsq : √(-2 * log (exp (-r ^ 2 / 2))) = r := by
    rw [log_exp, show -2 * (-r ^ 2 / 2) = r ^ 2 by ring, sqrt_sq hr.le]
  simp only [boxMuller, h2π, hsq, cos_add_pi, sin_add_pi, polarCoord_symm_apply, Prod.neg_mk,
    mul_neg]

end Substitution

lemma measurable_polarCoord_symm : Measurable polarCoord.symm := by
  change Measurable fun p : ℝ × ℝ ↦ (p.1 * cos p.2, p.1 * sin p.2)
  fun_prop

section Gaussian

/-- Density of the standard Gaussian on `ℝ²`. -/
noncomputable def gaussianPDF2 (p : ℝ × ℝ) : ℝ≥0∞ := gaussianPDF 0 1 p.1 * gaussianPDF 0 1 p.2

lemma measurable_gaussianPDF2 : Measurable gaussianPDF2 :=
  ((measurable_gaussianPDF 0 1).comp measurable_fst).mul
    ((measurable_gaussianPDF 0 1).comp measurable_snd)

lemma gaussianReal_prod_eq_withDensity :
    (gaussianReal 0 1).prod (gaussianReal 0 1) = volume.withDensity gaussianPDF2 := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero, prod_withDensity (measurable_gaussianPDF 0 1)
    (measurable_gaussianPDF 0 1), Measure.volume_eq_prod]
  rfl

/-- In polar coordinates the density is `e^{-r²/2} / 2π`. -/
lemma gaussianPDF2_polarCoord_symm (r θ : ℝ) :
    gaussianPDF2 (polarCoord.symm (r, θ)) = ENNReal.ofReal (exp (-r ^ 2 / 2) / (2 * π)) := by
  simp only [gaussianPDF2, gaussianPDF, polarCoord_symm_apply, gaussianPDFReal]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [mul_mul_mul_comm, ← exp_add, ← mul_inv, mul_self_sqrt h2π, div_eq_inv_mul (exp _)]
  congr 2
  have := cos_sq_add_sin_sq θ
  linear_combination (-(r ^ 2) / 2) * this

lemma map_neg_gaussianReal_prod :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (fun p ↦ -p) =
      (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  have h := Measure.map_prod_map (gaussianReal 0 1) (gaussianReal 0 1)
    (f := fun x : ℝ ↦ -x) (g := fun x : ℝ ↦ -x) measurable_neg measurable_neg
  rw [gaussianReal_map_neg, neg_zero] at h
  exact h.symm

end Gaussian

/-- The key identity: for every measurable `g ≥ 0`,
`∫_{]0,1[²} g(boxMuller w) dw = ∫ g(-x) γ₂(dx)`. -/
lemma lintegral_boxMuller {g : ℝ × ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ w in Ioo 0 1 ×ˢ Ioo 0 1, g (boxMuller w) =
      ∫⁻ x, g (-x) ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have hgT : Measurable (g ∘ boxMuller) := hg.comp measurable_boxMuller
  rw [Measure.volume_eq_prod, setLIntegral_prod (fun w ↦ g (boxMuller w)) hgT.aemeasurable]
  calc ∫⁻ u in Ioo 0 1, ∫⁻ v in Ioo 0 1, g (boxMuller (u, v))
      = ∫⁻ u in Ioo 0 1, ∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal (1 / (2 * π)) * g (boxMuller (u, (θ + π) / (2 * π))) :=
        lintegral_congr fun u ↦ lintegral_Ioo_eq_lintegral_Ioo_pi _
    _ = ∫⁻ r in Ioi 0, ENNReal.ofReal (r * exp (-r ^ 2 / 2)) * ∫⁻ θ in Ioo (-π) π,
          ENNReal.ofReal (1 / (2 * π)) *
            g (boxMuller (exp (-r ^ 2 / 2), (θ + π) / (2 * π))) :=
        lintegral_Ioo_eq_lintegral_Ioi _
    _ = ∫⁻ r in Ioi 0, ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal (r * exp (-r ^ 2 / 2)) *
          (ENNReal.ofReal (1 / (2 * π)) * g (-polarCoord.symm (r, θ))) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun r hr ↦ ?_
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun θ ↦ ?_
        rw [boxMuller_subst hr]
    _ = ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 •
          (gaussianPDF2 (polarCoord.symm p) * g (-polarCoord.symm p)) := by
        rw [polarCoord_target, Measure.volume_eq_prod, setLIntegral_prod]
        · refine setLIntegral_congr_fun measurableSet_Ioi fun r hr ↦ ?_
          refine lintegral_congr fun θ ↦ ?_
          have hr' : (0 : ℝ) < r := hr
          have key : ENNReal.ofReal (r * exp (-r ^ 2 / 2)) * ENNReal.ofReal (1 / (2 * π)) =
              ENNReal.ofReal r * ENNReal.ofReal (exp (-r ^ 2 / 2) / (2 * π)) := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hr'.le]
            congr 1
            ring
          rw [gaussianPDF2_polarCoord_symm, smul_eq_mul, ← mul_assoc, ← mul_assoc, key]
        · refine Measurable.aemeasurable ?_
          refine ((measurable_fst.ennreal_ofReal).smul ?_)
          exact (measurable_gaussianPDF2.comp measurable_polarCoord_symm).mul
            (hg.comp measurable_polarCoord_symm.neg)
    _ = ∫⁻ x, gaussianPDF2 x * g (-x) :=
        lintegral_comp_polarCoord_symm (fun x ↦ gaussianPDF2 x * g (-x))
    _ = ∫⁻ x, g (-x) ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
        rw [gaussianReal_prod_eq_withDensity]
        exact (lintegral_withDensity_eq_lintegral_mul _ measurable_gaussianPDF2
          (hg.comp measurable_neg)).symm

/-- CDIS P.V, id 98 (Box-Muller), measure form: the Box-Muller map pushes the uniform law on
`]0,1[²` forward to the standard Gaussian law on `ℝ²`. -/
theorem map_boxMuller :
    (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)).map boxMuller =
      (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  refine Measure.ext_of_lintegral _ fun g hg ↦ ?_
  rw [lintegral_map hg measurable_boxMuller, lintegral_boxMuller hg,
    ← lintegral_map hg measurable_neg, map_neg_gaussianReal_prod]

section RandomVariables

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {U V : Ω → ℝ}

/-- The pair `(X, Y)` of the Box-Muller transform has the standard Gaussian law on `ℝ²`. -/
theorem hasLaw_boxMuller (hU : HasLaw U (volume.restrict (Ioo (0 : ℝ) 1)) P)
    (hV : HasLaw V (volume.restrict (Ioo (0 : ℝ) 1)) P) (hUV : IndepFun U V P) :
    HasLaw (fun ω ↦ boxMuller (U ω, V ω)) ((gaussianReal 0 1).prod (gaussianReal 0 1)) P where
  aemeasurable :=
    measurable_boxMuller.comp_aemeasurable (hU.aemeasurable.prodMk hV.aemeasurable)
  map_eq := by
    have hUV' := (indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable).1 hUV
    rw [hU.map_eq, hV.map_eq, Measure.prod_restrict, ← Measure.volume_eq_prod] at hUV'
    rw [show (fun ω ↦ boxMuller (U ω, V ω)) = boxMuller ∘ (fun ω ↦ (U ω, V ω)) from rfl,
      ← AEMeasurable.map_map_of_aemeasurable measurable_boxMuller.aemeasurable
        (hU.aemeasurable.prodMk hV.aemeasurable), hUV', map_boxMuller]

/-- CDIS P.V, id 98 (Box-Muller): if `U` and `V` are independent and uniform on `]0,1[`, then
`X = √(-2 ln U) cos(2πV)` and `Y = √(-2 ln U) sin(2πV)` are independent and both have law
`N(0, 1)`. -/
theorem boxMuller_gaussian (hU : HasLaw U (volume.restrict (Ioo (0 : ℝ) 1)) P)
    (hV : HasLaw V (volume.restrict (Ioo (0 : ℝ) 1)) P) (hUV : IndepFun U V P) :
    HasLaw (fun ω ↦ √(-2 * log (U ω)) * cos (2 * π * V ω)) (gaussianReal 0 1) P ∧
      HasLaw (fun ω ↦ √(-2 * log (U ω)) * sin (2 * π * V ω)) (gaussianReal 0 1) P ∧
      IndepFun (fun ω ↦ √(-2 * log (U ω)) * cos (2 * π * V ω))
        (fun ω ↦ √(-2 * log (U ω)) * sin (2 * π * V ω)) P := by
  have h := hasLaw_boxMuller hU hV hUV
  have hfst : HasLaw Prod.fst (gaussianReal 0 1) ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    ⟨measurable_fst.aemeasurable, by rw [Measure.map_fst_prod, measure_univ, one_smul]⟩
  have hsnd : HasLaw Prod.snd (gaussianReal 0 1) ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    ⟨measurable_snd.aemeasurable, by rw [Measure.map_snd_prod, measure_univ, one_smul]⟩
  have hX : HasLaw (fun ω ↦ √(-2 * log (U ω)) * cos (2 * π * V ω)) (gaussianReal 0 1) P :=
    hfst.fun_comp h
  have hY : HasLaw (fun ω ↦ √(-2 * log (U ω)) * sin (2 * π * V ω)) (gaussianReal 0 1) P :=
    hsnd.fun_comp h
  refine ⟨hX, hY, ?_⟩
  rw [indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable, hX.map_eq,
    hY.map_eq]
  exact h.map_eq

end RandomVariables

end CDIS
