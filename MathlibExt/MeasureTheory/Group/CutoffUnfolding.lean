/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions adapted from `anthropics/fermats-last-theorem`, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, in
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MeasureTheory_integral_mul_eq_integral_integral_subgroup_mul_mul_of_forall_integral_translate_eq_one.lean
Copyright (c) 2026 Anthropic, PBC. Licensed under Apache 2.0:
https://www.apache.org/licenses/LICENSE-2.0.
The source NOTICE also credits the respective Mathlib authors, Apache 2.0.
-/

module

public import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import MathlibExt.MeasureTheory.Group.ActionCutoff
import MathlibExt.MeasureTheory.Group.CutoffIndependence

/-!
# Unfolding with normalized cutoffs

An integrable observable need not be invariant to unfold its integral into
an orbit integral against a normalized nonnegative cutoff. Tonelli gives
product integrability; a measure-preserving skew product and Fubini give
the equality. For nested closed subgroups, cutoff independence replaces
the inner cutoff while requiring invariance only under the smaller group.
-/

public section

open MeasureTheory Filter
open scoped ENNReal

namespace MeasureTheory

section Action

variable {A X : Type*} [Group A] [MulAction A X]
  [MeasurableSpace A] [MeasurableInv A] [MeasurableSpace X]
  (τ : Measure A) [SFinite τ] [τ.IsInvInvariant]
  (μ : Measure X) [SFinite μ]
  (hact : Measurable fun p : A × X => p.1 • p.2)
  (hμ : ∀ a : A, MeasurePreserving (fun x : X => a • x) μ μ)

include hact in
omit [MeasurableInv A] [τ.IsInvInvariant] [SFinite μ] in
private theorem integrable_normalized_kernel {g : X → ℂ} {w : X → ℝ}
    (hg : Measurable g) (hgi : Integrable g μ)
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (hw1 : ∀ x, g x ≠ 0 → ∫ a, w (a • x) ∂τ = 1) :
    Integrable (fun p : X × A => g p.1 * (w (p.2 • p.1) : ℂ))
      (μ.prod τ) := by
  have hm : Measurable (fun p : X × A => g p.1 * (w (p.2 • p.1) : ℂ)) :=
    (hg.comp measurable_fst).mul
      (Complex.measurable_ofReal.comp
        (hw.comp (hact.comp (measurable_snd.prodMk measurable_fst))))
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hm.enorm.aemeasurable]
  have hn (x : X) (a : A) :
      ‖g x * (w (a • x) : ℂ)‖ₑ = ‖g x‖ₑ * ENNReal.ofReal (w (a • x)) := by
    rw [enorm_mul]
    congr 1
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (hw0 _)]
  simp_rw [hn, lintegral_const_mul' _ _ enorm_ne_top]
  have he : ∀ x, ‖g x‖ₑ * (∫⁻ a, ENNReal.ofReal (w (a • x)) ∂τ) = ‖g x‖ₑ := by
    intro x
    by_cases hx : g x = 0
    · simp [hx]
    · rw [← ofReal_integral_eq_lintegral_ofReal
        (integrable_of_integral_eq_one (hw1 x hx))
        (Eventually.of_forall fun a => hw0 _), hw1 x hx]
      simp
  simp_rw [he]
  exact hasFiniteIntegral_iff_enorm.mp hgi.2

include hact hμ in
/-- Unfolding an integrable complex function against a normalized nonnegative
cutoff gives an integrable product kernel. No invariance of `g` is required. -/
theorem integrable_comp_smul_mul_of_normalized
    {g : X → ℂ} {w : X → ℝ} (hg : Measurable g) (hgi : Integrable g μ)
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (hw1 : ∀ x, g x ≠ 0 → ∫ a, w (a • x) ∂τ = 1) :
    Integrable (fun p : A × X => g (p.1 • p.2) * (w p.2 : ℂ))
      (τ.prod μ) := by
  have hk := (integrable_normalized_kernel τ μ hact hg hgi hw hw0 hw1).swap
  have hp := (Measure.measurePreserving_inv τ).skew_product hact
    (Eventually.of_forall fun a => (hμ a).map_eq)
  have hi := (hp.integrable_comp hk.aestronglyMeasurable).mpr hk
  simpa only [Function.comp_def, Prod.swap, inv_smul_smul] using hi

include hact hμ in
/-- Unfold an integrable, not necessarily invariant, complex function into
its orbit integral against a normalized nonnegative cutoff. Normalization
is needed only on the support of `g`. -/
theorem integral_eq_integral_smul_mul_of_normalized
    {g : X → ℂ} {w : X → ℝ} (hg : Measurable g) (hgi : Integrable g μ)
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (hw1 : ∀ x, g x ≠ 0 → ∫ a, w (a • x) ∂τ = 1) :
    ∫ x, g x ∂μ = ∫ x, (∫ a, g (a • x) ∂τ) * (w x : ℂ) ∂μ := by
  have hk : Integrable (fun p : A × X => g p.2 * (w (p.1 • p.2) : ℂ))
      (τ.prod μ) := by
    simpa only [Function.comp_def, Prod.swap] using
      (integrable_normalized_kernel τ μ hact hg hgi hw hw0 hw1).swap
  have hp := (Measure.measurePreserving_inv τ).skew_product hact
    (Eventually.of_forall fun a => (hμ a).map_eq)
  have hh := integrable_comp_smul_mul_of_normalized τ μ hact hμ hg hgi hw hw0 hw1
  calc
    ∫ x, g x ∂μ = ∫ p : A × X, g p.2 * (w (p.1 • p.2) : ℂ) ∂τ.prod μ := by
      rw [integral_prod_symm _ hk]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      change g x = ∫ a, g x * (w (a • x) : ℂ) ∂τ
      rw [integral_const_mul, integral_complex_ofReal]
      by_cases hx : g x = 0
      · simp [hx]
      · rw [hw1 x hx]
        simp
    _ = ∫ p : A × X, g (p.1 • p.2) * (w p.2 : ℂ) ∂τ.prod μ := by
      have hm : AEStronglyMeasurable
          (fun p : A × X => g p.2 * (w (p.1 • p.2) : ℂ))
          (Measure.map (fun p : A × X => (p.1⁻¹, p.1 • p.2)) (τ.prod μ)) := by
        rw [hp.map_eq]
        exact hk.1
      have he := integral_map hp.measurable.aemeasurable hm
      simpa only [hp.map_eq, inv_smul_smul] using he
    _ = ∫ x, (∫ a, g (a • x) ∂τ) * (w x : ℂ) ∂μ := by
      rw [integral_prod_symm _ hh]
      simp_rw [integral_mul_const]

end Action

private theorem integral_fibre_cutoff_eq
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (T S : Subgroup G) (hST : S ≤ T)
    [MeasurableSpace T] [BorelSpace T] [MeasurableSpace S] [BorelSpace S]
    (τ : Measure T) [SFinite τ] [τ.IsMulLeftInvariant]
    (τS : Measure S) [SFinite τS] [τS.IsInvInvariant]
    (F : G → ℂ) (hFm : Measurable F)
    (hFS : ∀ (s : S) (x : G), F ((s : G) * x) = F x)
    (wS : G → ℝ) (hwS0 : ∀ x, 0 ≤ wS x) (hwSm : Measurable wS)
    (hwS1 : ∀ x, F x ≠ 0 → ∫ s : S, wS ((s : G) * x) ∂τS = 1)
    (β : T → ℝ) (hβ0 : ∀ t, 0 ≤ β t) (hβm : Measurable β)
    (hβ1 : ∀ t : T, ∫ s : S, β (Subgroup.inclusion hST s * t) ∂τS = 1)
    (x : G) :
    ∫ t : T, F ((t : G) * x) * (wS ((t : G) * x) : ℂ) ∂τ =
      ∫ t : T, F ((t : G) * x) * (β t : ℂ) ∂τ := by
  let : MulAction S T := MulAction.compHom T (Subgroup.inclusion hST)
  have : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology _
  have : SecondCountableTopology T := TopologicalSpace.Subtype.secondCountableTopology _
  have hc : Continuous (Subgroup.inclusion hST : S → T) :=
    continuous_subtype_val.subtype_mk _
  have ha : Measurable fun p : S × T => p.1 • p.2 :=
    ((hc.comp continuous_fst).mul continuous_snd).measurable
  have hτ (s : S) : MeasurePreserving (fun t : T => s • t) τ τ :=
    measurePreserving_mul_left τ (Subgroup.inclusion hST s)
  refine integral_mul_eq_of_normalized_smul τS τ ha hτ
    (hFm.comp (continuous_subtype_val.mul continuous_const).measurable) ?_
    (hwSm.comp (continuous_subtype_val.mul continuous_const).measurable) hβm
    (fun t => hwS0 _) hβ0 ?_ ?_
  · intro s t
    change F (((s : G) * (t : G)) * x) = F ((t : G) * x)
    rw [mul_assoc, hFS]
  · intro t ht
    change ∫⁻ s : S, ENNReal.ofReal (wS (((s : G) * (t : G)) * x)) ∂τS = 1
    simp_rw [mul_assoc]
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_of_integral_eq_one (hwS1 _ ht))
      (Eventually.of_forall fun s => hwS0 _), hwS1 _ ht, ENNReal.ofReal_one]
  · intro t _
    change ∫⁻ s : S, ENNReal.ofReal (β (Subgroup.inclusion hST s * t)) ∂τS = 1
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_of_integral_eq_one (hβ1 t))
      (Eventually.of_forall fun s => hβ0 _), hβ1 t, ENNReal.ofReal_one]

/-- Unfold an `S`-invariant bounded observable through a larger closed
subgroup `T`, using an `S`-normalized cutoff on `T` for the inner average.
Only the starting cutoff `wS` needs compact support. The conclusion does
not require `F` to be `T`-invariant. -/
theorem integral_mul_eq_integral_subgroup_average
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (T : Subgroup G) (hT : IsClosed (T : Set G)) [MeasurableSpace T] [BorelSpace T]
    (S : Subgroup G) (hS : IsClosed (S : Set G)) (hST : S ≤ T)
    [MeasurableSpace S] [BorelSpace S]
    (μ : Measure G) [μ.IsHaarMeasure]
    (τ : Measure T) [τ.IsHaarMeasure] [τ.IsInvInvariant]
    (τS : Measure S) [τS.IsHaarMeasure] [τS.IsInvInvariant]
    (F : G → ℂ) (hFm : Measurable F) (hFb : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C)
    (hFS : ∀ (s : S) (x : G), F ((s : G) * x) = F x)
    (wS : G → ℝ) (hwS0 : ∀ x, 0 ≤ wS x) (hwSm : Measurable wS)
    (hwSc : HasCompactSupport wS)
    (hwS1 : ∀ x, F x ≠ 0 → ∫ s : S, wS ((s : G) * x) ∂τS = 1)
    (β : T → ℝ) (hβ0 : ∀ t, 0 ≤ β t) (hβm : Measurable β)
    (hβ1 : ∀ t : T, ∫ s : S, β (Subgroup.inclusion hST s * t) ∂τS = 1)
    (W : G → ℝ) (hW0 : ∀ x, 0 ≤ W x) (hWm : Measurable W)
    (hW1 : ∀ x, F x ≠ 0 → ∫ t : T, W ((t : G) * x) ∂τ = 1) :
    ∫ x, F x * (wS x : ℂ) ∂μ =
      ∫ x, (∫ t : T, F ((t : G) * x) * (β t : ℂ) ∂τ) * (W x : ℂ) ∂μ := by
  have : SigmaCompactSpace T := hT.isClosedEmbedding_subtypeVal.sigmaCompactSpace
  have : SigmaCompactSpace S := hS.isClosedEmbedding_subtypeVal.sigmaCompactSpace
  have hi := integrable_mul_of_integral_subgroup_translate_eq_one
    S μ τS hS F hFm hFb hFS wS hwS0 hwSm hwSc hwS1
  have ha : Measurable fun p : T × G => p.1 • p.2 :=
    ((continuous_subtype_val.comp continuous_fst).mul continuous_snd).measurable
  have hn (x : G) (hx : F x * (wS x : ℂ) ≠ 0) :
      ∫ t : T, W (t • x) ∂τ = 1 :=
    hW1 x (fun h => hx (by rw [h, zero_mul]))
  rw [integral_eq_integral_smul_mul_of_normalized τ μ ha
    (fun t => measurePreserving_mul_left μ (t : G))
    (g := fun x => F x * (wS x : ℂ))
    (hFm.mul (Complex.measurable_ofReal.comp hwSm)) hi hWm hW0 hn]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  exact congrArg (fun z : ℂ => z * (W x : ℂ))
    (integral_fibre_cutoff_eq T S hST τ τS F hFm hFS
      wS hwS0 hwSm hwS1 β hβ0 hβm hβ1 x)

end MeasureTheory
