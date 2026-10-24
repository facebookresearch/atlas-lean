/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Joint continuity of the divided difference

For `f` holomorphic on an open set `Ω`, the divided difference `(z, ζ) ↦ dslope f z ζ`, equal to
`(f ζ - f z) / (ζ - z)` off the diagonal and to `f′ z` on it, is jointly continuous on `Ω × Ω`
(`Complex.continuousOn_dslope_prod`), symmetric (`dslope_comm`), and holomorphic in each
variable (`Complex.differentiableOn_dslope_left`; Mathlib's `Complex.differentiableOn_dslope`
is the other variable). This is the divided-difference claim in the proof of the general Cauchy
integral formula.

Mathlib has continuity and holomorphy of `dslope f c` in the second variable for fixed `c`
(`continuousOn_dslope`, `Complex.differentiableOn_dslope`), but not joint continuity.

Code-derived port of `dividedDiff_symm`, `continuousOn_dividedDiff`,
`differentiableOn_dividedDiff_fst` and the helper `dslope_sub_deriv_norm_le` from
`v1/Atlas/ComplexVariables/code/Lecture13.lean` at commit
`6191bf1ba03d204784385ef5be2472be88035b93`, lines 225–320 (Claim 1 of Lecture 13), restated on
`dslope` instead of the archived `dividedDiff` wrapper. The archived formalization and its
original license/provenance remain in `v1/` (the original license text is `v1/LICENSE`). This
records equivalence to the archived Lean statement, not verification against the printed
textbook.
-/

set_option autoImplicit false

open Set Filter Topology Metric

/-- The divided difference is symmetric: `dslope f a b = dslope f b a`. -/
public theorem dslope_comm {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (f : 𝕜 → E) (a b : 𝕜) : dslope f a b = dslope f b a := by
  rcases eq_or_ne a b with rfl | hne
  · rfl
  · rw [dslope_of_ne f hne.symm, dslope_of_ne f hne, slope_comm]

namespace Complex

private lemma dslope_sub_deriv_norm_le {f : ℂ → ℂ} {s : Set ℂ} {z ζ z₀ : ℂ} {C : ℝ}
    (hf : ∀ w ∈ s, DifferentiableAt ℂ f w)
    (hC : ∀ w ∈ s, ‖deriv f w - deriv f z₀‖ ≤ C)
    (hs : Convex ℝ s) (hz : z ∈ s) (hζ : ζ ∈ s) :
    ‖dslope f z ζ - deriv f z₀‖ ≤ C := by
  rcases eq_or_ne ζ z with heq | hne
  · subst heq; simp only [dslope_same]; exact hC _ hz
  · rw [dslope_of_ne _ hne]
    set h := fun w => f w - deriv f z₀ * w
    have hh_diff : ∀ w ∈ s, DifferentiableAt ℂ h w := fun w hw =>
      (hf w hw).sub ((differentiableAt_const _).mul differentiableAt_id)
    have hh_deriv : ∀ w ∈ s, deriv h w = deriv f w - deriv f z₀ := fun w hw =>
      ((hf w hw).hasDerivAt.sub
        (by simpa using (hasDerivAt_id w).const_mul (deriv f z₀))).deriv
    have hh_bound : ∀ w ∈ s, ‖deriv h w‖ ≤ C := fun w hw => by
      rw [hh_deriv w hw]; exact hC w hw
    have mvt := hs.norm_image_sub_le_of_norm_deriv_le hh_diff hh_bound hz hζ
    have hh_sub : h ζ - h z = (f ζ - f z) - deriv f z₀ * (ζ - z) := by simp [h]; ring
    rw [hh_sub] at mvt
    rw [show slope f z ζ - deriv f z₀ =
        (ζ - z)⁻¹ * ((f ζ - f z) - deriv f z₀ * (ζ - z)) from by
      rw [slope_def_module]; simp only [smul_eq_mul]
      field_simp [sub_ne_zero.mpr hne], norm_mul, norm_inv]
    calc ‖ζ - z‖⁻¹ * ‖(f ζ - f z) - deriv f z₀ * (ζ - z)‖
        ≤ ‖ζ - z‖⁻¹ * (C * ‖ζ - z‖) :=
          mul_le_mul_of_nonneg_left mvt (inv_nonneg.mpr (norm_nonneg _))
      _ = C := by field_simp [norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)]

/-- The divided difference `(z, ζ) ↦ dslope f z ζ` of a holomorphic function is jointly continuous
on `Ω × Ω`; on the diagonal it is `deriv f`. -/
public theorem continuousOn_dslope_prod {f : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hf : DifferentiableOn ℂ f Ω) :
    ContinuousOn (fun p : ℂ × ℂ => dslope f p.1 p.2) (Ω ×ˢ Ω) := by
  apply (hΩ.prod hΩ).continuousOn_iff.mpr
  intro ⟨z₀, ζ₀⟩ ⟨hz₀, hζ₀⟩
  simp only at hz₀ hζ₀
  rcases eq_or_ne z₀ ζ₀ with rfl | hne
  · rw [Metric.continuousAt_iff]
    intro ε hε
    have hf' : ContinuousAt (deriv f) z₀ :=
      (hf.deriv hΩ).continuousOn.continuousAt (hΩ.mem_nhds hz₀)
    rw [Metric.continuousAt_iff] at hf'
    obtain ⟨δ₁, hδ₁, hδ₁_bound⟩ := hf' (ε / 2) (half_pos hε)
    obtain ⟨δ₂, hδ₂, hball⟩ := Metric.isOpen_iff.mp hΩ z₀ hz₀
    set δ := min δ₁ δ₂
    refine ⟨δ, lt_min hδ₁ hδ₂, fun ⟨z, ζ⟩ hdist => ?_⟩
    rw [Prod.dist_eq] at hdist; simp only at hdist
    have hz : dist z z₀ < δ := lt_of_le_of_lt (le_max_left _ _) hdist
    have hζ : dist ζ z₀ < δ := lt_of_le_of_lt (le_max_right _ _) hdist
    change dist (dslope f z ζ) (dslope f z₀ z₀) < ε
    rw [dslope_same, dist_comm, dist_eq_norm, norm_sub_rev]
    have hfδ : ∀ w ∈ ball z₀ δ, DifferentiableAt ℂ f w := fun w hw =>
      hf.differentiableAt (hΩ.mem_nhds (hball (ball_subset_ball (min_le_right _ _) hw)))
    have hCδ : ∀ w ∈ ball z₀ δ, ‖deriv f w - deriv f z₀‖ ≤ ε / 2 := fun w hw => by
      rw [← dist_eq_norm]
      exact le_of_lt (hδ₁_bound (lt_of_lt_of_le (mem_ball.mp hw) (min_le_left _ _)))
    calc ‖dslope f z ζ - deriv f z₀‖
        ≤ ε / 2 := dslope_sub_deriv_norm_le hfδ hCδ (convex_ball z₀ δ)
            (mem_ball.mpr hz) (mem_ball.mpr hζ)
      _ < ε := half_lt_self hε
  · set g : ℂ × ℂ → ℂ := fun p => (f p.2 - f p.1) / (p.2 - p.1)
    have hf_cont : ContinuousOn f Ω := hf.continuousOn
    have h1 : ContinuousAt f z₀ := hf_cont.continuousAt (hΩ.mem_nhds hz₀)
    have h2 : ContinuousAt f ζ₀ := hf_cont.continuousAt (hΩ.mem_nhds hζ₀)
    have hg_cont : ContinuousAt g (z₀, ζ₀) :=
      ((h2.comp continuousAt_snd).sub (h1.comp continuousAt_fst)).div
        (continuousAt_snd.sub continuousAt_fst) (sub_ne_zero.mpr (Ne.symm hne))
    exact hg_cont.congr <| by
      filter_upwards [(isOpen_ne_fun continuous_fst continuous_snd).mem_nhds
        (show (z₀, ζ₀) ∈ {p : ℂ × ℂ | p.1 ≠ p.2} from hne)]
      rintro ⟨z, ζ⟩ (hzζ : z ≠ ζ)
      simp only [g]
      rw [dslope_of_ne _ hzζ.symm, slope_def_module, smul_eq_mul, div_eq_inv_mul]

/-- For `f` holomorphic on an open `Ω` and `ζ₀ ∈ Ω`, `z ↦ dslope f z ζ₀` is holomorphic on `Ω`. -/
public theorem differentiableOn_dslope_left {f : ℂ → ℂ} {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hf : DifferentiableOn ℂ f Ω) {ζ₀ : ℂ} (hζ₀ : ζ₀ ∈ Ω) :
    DifferentiableOn ℂ (fun z => dslope f z ζ₀) Ω := by
  simp_rw [dslope_comm f _ ζ₀]
  exact (differentiableOn_dslope (hΩ.mem_nhds hζ₀)).mpr hf

end Complex

