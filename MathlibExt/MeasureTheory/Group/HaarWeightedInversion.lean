/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.MeasureTheory.Group.ModularCharacterContinuity

/-!
# Weighted inversion for a general left Haar measure

The character used here is the right-pushforward character: translating the measure
on the right by `g` multiplies it by `Measure.modularCharacter g`. Inversion therefore
preserves the integral after multiplying the inverted integrand by this character.
Two compact-support Fubini swaps prove the formula without global finiteness or
separation assumptions on the locally compact group.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set
open scoped NNReal Pointwise

namespace MeasureTheory

noncomputable section

universe uG uE

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

omit [LocallyCompactSpace G] [CompleteSpace E] [μ.Regular] in
/-- Individual left translations preserve the Haar integral. -/
private theorem integral_mul_left_haar (F : G → E) (g : G) :
    (∫ s, F (g * s) ∂μ) = ∫ s, F s ∂μ := by
  have he : MeasurableEmbedding (fun s : G => g * s) :=
    (Homeomorph.mulLeft g).measurableEmbedding
  rw [← he.integral_map, map_mul_left_eq_self]

omit [CompleteSpace E] in
/-- Let `G` be a locally compact topological group with its Borel σ-algebra and a regular left Haar
measure `μ`. The integrands take values in a normed real vector space `E`; the weight is the
positive modular character.

Individual right translations scale the integral by the adopted modular character. -/
theorem integral_mul_right_modular (F : G → E) (g : G) :
    (∫ s, F (s * g) ∂μ) = (Measure.modularCharacter g : ℝ) • ∫ s, F s ∂μ := by
  have he : MeasurableEmbedding (fun s : G => s * g) :=
    (Homeomorph.mulRight g).measurableEmbedding
  have : (Measure.map (fun s : G => s * g) μ).Regular :=
    Measure.Regular.map (Homeomorph.mulRight g)
  have hmap : Measure.map (fun s : G => s * g) μ = Measure.modularCharacter g • μ := by
    change Measure.map (fun s : G => s * g) μ = Measure.modularCharacterFun g • μ
    rw [Measure.modularCharacterFun_eq_haarScalarFactor μ g]
    exact Measure.isMulLeftInvariant_eq_smul_of_regular _ μ
  calc
    _ = ∫ s, F s ∂Measure.map (fun s : G => s * g) μ := (he.integral_map (μ := μ) F).symm
    _ = ∫ s, F s ∂(Measure.modularCharacter g • μ) := by rw [hmap]
    _ = Measure.modularCharacter g • ∫ s, F s ∂μ := integral_smul_nnreal_measure _ _
    _ = (Measure.modularCharacter g : ℝ) • ∫ s, F s ∂μ := rfl

omit [CompleteSpace E] in
/-- Left shifts of the inverted argument preserve its modularly weighted integral. -/
private theorem integral_modular_shift (F : G → E) (g : G) :
    (∫ s, (Measure.modularCharacter s : ℝ) • F (g * s⁻¹) ∂μ) =
      ∫ s, (Measure.modularCharacter s : ℝ) • F s⁻¹ ∂μ := by
  let K : E := ∫ s, (Measure.modularCharacter s : ℝ) • F s⁻¹ ∂μ
  have hmul (s : G) : (Measure.modularCharacter (s * g) : ℝ) =
      (Measure.modularCharacter g : ℝ) * (Measure.modularCharacter s : ℝ) := by
    rw [map_mul, NNReal.coe_mul, mul_comm]
  have htranslated :
      (∫ s, (Measure.modularCharacter (s * g) : ℝ) • F (g * (s * g)⁻¹) ∂μ) =
        (Measure.modularCharacter g : ℝ) • K := by
    calc
      _ = ∫ s, (Measure.modularCharacter g : ℝ) •
          ((Measure.modularCharacter s : ℝ) • F s⁻¹) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with s
        rw [hmul, mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul, mul_smul]
      _ = (Measure.modularCharacter g : ℝ) • K := integral_smul _ _
  have hscaled : (Measure.modularCharacter g : ℝ) •
      (∫ s, (Measure.modularCharacter s : ℝ) • F (g * s⁻¹) ∂μ) =
        (Measure.modularCharacter g : ℝ) • K :=
    (integral_mul_right_modular μ
      (fun s => (Measure.modularCharacter s : ℝ) • F (g * s⁻¹)) g).symm.trans htranslated
  have hg : (Measure.modularCharacter g : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Measure.modularCharacterFun_pos g))
  have h := congrArg (fun x : E => (Measure.modularCharacter g : ℝ)⁻¹ • x) hscaled
  simpa only [smul_smul, inv_mul_cancel₀ hg, one_smul] using h

/-- Let `G` be a locally compact topological group with its Borel σ-algebra and a regular left Haar
measure `μ`. The integrands take values in a normed real vector space `E`; the weight is the
positive modular character. For the inversion identity, the integrand is continuous and
compactly supported. Assume the vector space `E` is complete.

In the right-pushforward convention, multiplying an inverted compactly supported continuous
integrand by the Haar modular character preserves its Bochner integral. -/
theorem integral_modularCharacter_smul_inv_of_hasCompactSupport
    {F : G → E} (hFcont : Continuous F) (hFcomp : HasCompactSupport F) :
    (∫ s, (Measure.modularCharacter s : ℝ) • F s⁻¹ ∂μ) = ∫ s, F s ∂μ := by
  obtain ⟨ψ, hψcomp, hψnonneg, hψone⟩ := exists_continuous_nonneg_pos (1 : G)
  let I : ℝ := ∫ s, ψ s ∂μ
  have hI : I ≠ 0 := ne_of_gt
    (ψ.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      hψcomp hψnonneg hψone)
  let K : E := ∫ s, (Measure.modularCharacter s : ℝ) • F s⁻¹ ∂μ
  let R : Set G := (fun p : G × G => p.1⁻¹ * p.2) ''
    (tsupport F ×ˢ tsupport (ψ : G → ℝ))
  have hR : IsCompact R :=
    (hFcomp.prod hψcomp).image (continuous_fst.inv.mul continuous_snd)
  let J : G → G → E := fun s t => ψ (t * s) • F t
  have hJcont : Continuous J.uncurry :=
    (ψ.continuous.comp (continuous_snd.mul continuous_fst)).smul
      (hFcont.comp continuous_snd)
  have hJcomp : HasCompactSupport J.uncurry := by
    refine HasCompactSupport.intro (hR.prod hFcomp) ?_
    rintro ⟨s, t⟩ hst
    change ψ (t * s) • F t = 0
    by_cases ht : t ∈ tsupport F
    · have hψ : ψ (t * s) = 0 := by
        by_contra hne
        apply hst
        refine ⟨?_, ht⟩
        refine ⟨(t, t * s), ⟨ht, subset_closure hne⟩, ?_⟩
        change t⁻¹ * (t * s) = s
        rw [inv_mul_cancel_left]
      rw [hψ, zero_smul]
    · have htzero : F t = 0 := by
        by_contra hne
        exact ht (subset_closure hne)
      rw [htzero, smul_zero]
  have hJvalue : (∫ s, (∫ t, J s t ∂μ) ∂μ) = I • ∫ t, F t ∂μ := by
    calc
      _ = ∫ t, (∫ s, J s t ∂μ) ∂μ :=
        integral_integral_swap_of_hasCompactSupport (μ := μ) (ν := μ) hJcont hJcomp
      _ = ∫ t, I • F t ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with t
        change (∫ s, ψ (t * s) • F t ∂μ) = I • F t
        rw [integral_smul_const, integral_mul_left_haar μ (ψ : G → ℝ) t]
      _ = I • ∫ t, F t ∂μ := integral_smul _ _
  let L : G → G → E := fun s x =>
    (Measure.modularCharacter s : ℝ) • (ψ x • F (x * s⁻¹))
  have hδ : Continuous (fun s : G => (Measure.modularCharacter s : ℝ)) :=
    continuous_subtype_val.comp Measure.continuous_modularCharacter
  have hLcont : Continuous L.uncurry :=
    (hδ.comp continuous_fst).smul
      ((ψ.continuous.comp continuous_snd).smul
        (hFcont.comp (continuous_snd.mul continuous_fst.inv)))
  have hLcomp : HasCompactSupport L.uncurry := by
    refine HasCompactSupport.intro (hR.prod hψcomp) ?_
    rintro ⟨s, x⟩ hsx
    change (Measure.modularCharacter s : ℝ) • (ψ x • F (x * s⁻¹)) = 0
    by_cases hx : x ∈ tsupport (ψ : G → ℝ)
    · have hFzero : F (x * s⁻¹) = 0 := by
        by_contra hne
        apply hsx
        refine ⟨?_, hx⟩
        refine ⟨(x * s⁻¹, x), ⟨subset_closure hne, hx⟩, ?_⟩
        change (x * s⁻¹)⁻¹ * x = s
        rw [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
      rw [hFzero, smul_zero, smul_zero]
    · have hψzero : ψ x = 0 := by
        by_contra hne
        exact hx (subset_closure hne)
      rw [hψzero, zero_smul, smul_zero]
  have hJL : (∫ s, (∫ t, J s t ∂μ) ∂μ) = ∫ s, (∫ x, L s x ∂μ) ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with s
    change (∫ t, ψ (t * s) • F t ∂μ) =
      ∫ x, (Measure.modularCharacter s : ℝ) • (ψ x • F (x * s⁻¹)) ∂μ
    calc
      _ = ∫ x, ψ (x * s) • F ((x * s) * s⁻¹) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [mul_inv_cancel_right]
      _ = (Measure.modularCharacter s : ℝ) •
          ∫ x, ψ x • F (x * s⁻¹) ∂μ :=
        integral_mul_right_modular μ (fun x => ψ x • F (x * s⁻¹)) s
      _ = ∫ x, (Measure.modularCharacter s : ℝ) • (ψ x • F (x * s⁻¹)) ∂μ :=
        (integral_smul _ _).symm
  have hLvalue : (∫ s, (∫ x, L s x ∂μ) ∂μ) = I • K := by
    calc
      _ = ∫ x, (∫ s, L s x ∂μ) ∂μ :=
        integral_integral_swap_of_hasCompactSupport (μ := μ) (ν := μ) hLcont hLcomp
      _ = ∫ x, ψ x • K ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        change (∫ s, (Measure.modularCharacter s : ℝ) • (ψ x • F (x * s⁻¹)) ∂μ) =
          ψ x • K
        calc
          _ = ∫ s, ψ x • ((Measure.modularCharacter s : ℝ) • F (x * s⁻¹)) ∂μ := by
            apply integral_congr_ae
            filter_upwards [] with s
            exact smul_comm _ _ _
          _ = ψ x • ∫ s, (Measure.modularCharacter s : ℝ) • F (x * s⁻¹) ∂μ :=
            integral_smul _ _
          _ = ψ x • K := congrArg (fun y : E => ψ x • y) (integral_modular_shift μ F x)
      _ = I • K := integral_smul_const _ _
  have hscaled : I • (∫ s, F s ∂μ) = I • K := hJvalue.symm.trans (hJL.trans hLvalue)
  have h := congrArg (fun x : E => I⁻¹ • x) hscaled
  have heq : (∫ s, F s ∂μ) = K := by
    simpa only [smul_smul, inv_mul_cancel₀ hI, one_smul] using h
  exact heq.symm

end

end MeasureTheory
