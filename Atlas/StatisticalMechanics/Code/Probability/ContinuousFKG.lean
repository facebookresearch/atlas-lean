/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































import Mathlib

open MeasureTheory
open scoped BigOperators ENNReal

namespace StatMech
namespace Probability

set_option linter.unusedSectionVars false


theorem ContinuousFKG.integrable_of_bdd {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    Integrable f μ := by
  refine (memLp_top_of_bound hf.aestronglyMeasurable C ?_).integrable le_top
  exact Filter.Eventually.of_forall (fun x => by simpa [Real.norm_eq_abs] using hC x)



theorem ContinuousFKG.comonotone_nonneg {f g : ℝ → ℝ}
    (hf : Monotone f) (hg : Monotone g) (x y : ℝ) :
    0 ≤ (f x - f y) * (g x - g y) := by
  rcases le_total x y with h | h
  · have h1 : 0 ≤ -(f x - f y) := by linarith [hf h]
    have h2 : 0 ≤ -(g x - g y) := by linarith [hg h]
    have := mul_nonneg h1 h2
    linarith [this, neg_mul_neg (f x - f y) (g x - g y)]
  · have h1 : 0 ≤ f x - f y := sub_nonneg.mpr (hf h)
    have h2 : 0 ≤ g x - g y := sub_nonneg.mpr (hg h)
    exact mul_nonneg h1 h2





theorem chebyshev_correlation_prob (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f g : ℝ → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    {Cf Cg : ℝ} (hfC : ∀ x, |f x| ≤ Cf) (hgC : ∀ x, |g x| ≤ Cg)
    (hf : Monotone f) (hg : Monotone g) :
    (∫ x, f x ∂μ) * (∫ x, g x ∂μ) ≤ ∫ x, f x * g x ∂μ := by
  have hCf0 : 0 ≤ Cf := le_trans (abs_nonneg _) (hfC 0)
  have hCg0 : 0 ≤ Cg := le_trans (abs_nonneg _) (hgC 0)
  set ν := μ.prod μ with hν
  
  have hA : Integrable (fun z : ℝ × ℝ => f z.1 * g z.1) ν := by
    apply ContinuousFKG.integrable_of_bdd ν (C := Cf * Cg)
    · exact (hfm.comp measurable_fst).mul (hgm.comp measurable_fst)
    · intro z; rw [abs_mul]
      exact mul_le_mul (hfC _) (hgC _) (abs_nonneg _) hCf0
  have hB : Integrable (fun z : ℝ × ℝ => f z.1 * g z.2) ν := by
    apply ContinuousFKG.integrable_of_bdd ν (C := Cf * Cg)
    · exact (hfm.comp measurable_fst).mul (hgm.comp measurable_snd)
    · intro z; rw [abs_mul]
      exact mul_le_mul (hfC _) (hgC _) (abs_nonneg _) hCf0
  have hC' : Integrable (fun z : ℝ × ℝ => f z.2 * g z.1) ν := by
    apply ContinuousFKG.integrable_of_bdd ν (C := Cf * Cg)
    · exact (hfm.comp measurable_snd).mul (hgm.comp measurable_fst)
    · intro z; rw [abs_mul]
      exact mul_le_mul (hfC _) (hgC _) (abs_nonneg _) hCf0
  have hD : Integrable (fun z : ℝ × ℝ => f z.2 * g z.2) ν := by
    apply ContinuousFKG.integrable_of_bdd ν (C := Cf * Cg)
    · exact (hfm.comp measurable_snd).mul (hgm.comp measurable_snd)
    · intro z; rw [abs_mul]
      exact mul_le_mul (hfC _) (hgC _) (abs_nonneg _) hCf0
  
  have hHnn : 0 ≤ ∫ z, (f z.1 - f z.2) * (g z.1 - g z.2) ∂ν := by
    apply integral_nonneg
    intro z; exact ContinuousFKG.comonotone_nonneg hf hg z.1 z.2
  
  have hsplit : ∫ z, (f z.1 - f z.2) * (g z.1 - g z.2) ∂ν
      = (∫ z, f z.1 * g z.1 ∂ν) - (∫ z, f z.1 * g z.2 ∂ν)
        - (∫ z, f z.2 * g z.1 ∂ν) + (∫ z, f z.2 * g z.2 ∂ν) := by
    rw [show (fun z : ℝ × ℝ => (f z.1 - f z.2) * (g z.1 - g z.2))
        = (fun z => f z.1 * g z.1) - (fun z => f z.1 * g z.2)
          - (fun z => f z.2 * g z.1) + (fun z => f z.2 * g z.2) by funext z; simp; ring]
    rw [integral_add' (by exact (hA.sub hB).sub hC') hD,
        integral_sub' (hA.sub hB) hC', integral_sub' hA hB]
  rw [hsplit] at hHnn
  
  have eA : ∫ z, f z.1 * g z.1 ∂ν = ∫ x, f x * g x ∂μ := by
    rw [hν, integral_fun_fst (fun x => f x * g x)]; simp
  have eD : ∫ z, f z.2 * g z.2 ∂ν = ∫ x, f x * g x ∂μ := by
    rw [hν, integral_fun_snd (fun x => f x * g x)]; simp
  have eB : ∫ z, f z.1 * g z.2 ∂ν = (∫ x, f x ∂μ) * (∫ y, g y ∂μ) := by
    rw [hν, integral_prod_mul]
  have eC : ∫ z, f z.2 * g z.1 ∂ν = (∫ x, g x ∂μ) * (∫ y, f y ∂μ) := by
    rw [hν, show (fun z : ℝ × ℝ => f z.2 * g z.1) = (fun z : ℝ × ℝ => g z.1 * f z.2) by
      funext z; ring, integral_prod_mul]
  rw [eA, eB, eC, eD] at hHnn
  nlinarith [hHnn]



def HasFKG {β : Type*} [MeasurableSpace β] [Preorder β] (ν : Measure β) : Prop :=
  ∀ (f g : β → ℝ), Measurable f → Measurable g →
    (∃ Cf : ℝ, ∀ b, |f b| ≤ Cf) → (∃ Cg : ℝ, ∀ b, |g b| ≤ Cg) →
    Monotone f → Monotone g →
    (∫ b, f b ∂ν) * (∫ b, g b ∂ν) ≤ ∫ b, f b * g b ∂ν



theorem hasFKG_real (μ : Measure ℝ) [IsProbabilityMeasure μ] : HasFKG μ := by
  intro f g hfm hgm ⟨Cf, hfC⟩ ⟨Cg, hgC⟩ hfmono hgmono
  exact chebyshev_correlation_prob μ hfm hgm hfC hgC hfmono hgmono



theorem hasFKG_subsingleton {β : Type*} [MeasurableSpace β] [Preorder β] [Subsingleton β]
    (ν : Measure β) [IsProbabilityMeasure ν] : HasFKG ν := by
  intro f g hfm hgm _ _ _ _
  obtain ⟨b₀⟩ := nonempty_of_isProbabilityMeasure ν
  have hfc : f = fun _ => f b₀ := by funext b; rw [Subsingleton.elim b b₀]
  have hgc : g = fun _ => g b₀ := by funext b; rw [Subsingleton.elim b b₀]
  calc (∫ b, f b ∂ν) * (∫ b, g b ∂ν)
      = (∫ _b, f b₀ ∂ν) * (∫ _b, g b₀ ∂ν) := by rw [hfc, hgc]
    _ = (f b₀) * (g b₀) := by simp [integral_const]
    _ = ∫ _b, f b₀ * g b₀ ∂ν := by simp [integral_const]
    _ ≤ ∫ b, f b * g b ∂ν := by
        apply le_of_eq
        apply integral_congr_ae; apply Filter.Eventually.of_forall
        intro b; rw [Subsingleton.elim b₀ b]






theorem prod_fkg_step
    {β : Type*} [MeasurableSpace β] [Preorder β]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (ν : Measure β) [IsProbabilityMeasure ν]
    (hcheb : HasFKG μ) (hν : HasFKG ν) :
    HasFKG (μ.prod ν) := by
  intro f g hfm hgm ⟨Cf, hfC⟩ ⟨Cg, hgC⟩ hfmono hgmono
  
  have hCf0 : 0 ≤ Cf := by
    have h1 : (0 : ℝ) ≤ ∫ z, |f z| ∂(μ.prod ν) := integral_nonneg (fun z => abs_nonneg _)
    have h2 : ∫ z, |f z| ∂(μ.prod ν) ≤ ∫ _z, Cf ∂(μ.prod ν) :=
      integral_mono (ContinuousFKG.integrable_of_bdd _ hfm.abs
        (fun z => by rw [abs_abs]; exact hfC z)) (integrable_const Cf) (fun z => hfC z)
    rw [integral_const, probReal_univ, one_smul] at h2
    linarith
  
  have hfib_f : ∀ t : ℝ, Integrable (fun b => f (t, b)) ν := fun t =>
    ContinuousFKG.integrable_of_bdd ν (hfm.comp (measurable_const.prodMk measurable_id))
      (fun b => hfC (t, b))
  have hfib_g : ∀ t : ℝ, Integrable (fun b => g (t, b)) ν := fun t =>
    ContinuousFKG.integrable_of_bdd ν (hgm.comp (measurable_const.prodMk measurable_id))
      (fun b => hgC (t, b))
  
  set F : ℝ → ℝ := fun t => ∫ b, f (t, b) ∂ν with hF
  set G : ℝ → ℝ := fun t => ∫ b, g (t, b) ∂ν with hG
  have hFm : Measurable F := (hfm.stronglyMeasurable.integral_prod_right').measurable
  have hGm : Measurable G := (hgm.stronglyMeasurable.integral_prod_right').measurable
  have hFC : ∀ t, |F t| ≤ Cf := by
    intro t
    calc |F t| ≤ ∫ b, |f (t, b)| ∂ν := by rw [hF]; exact abs_integral_le_integral_abs
      _ ≤ ∫ b, Cf ∂ν := by
            apply integral_mono ((hfib_f t).abs) (integrable_const Cf)
            intro b; exact hfC (t, b)
      _ = Cf := by simp
  have hGC : ∀ t, |G t| ≤ Cg := by
    intro t
    calc |G t| ≤ ∫ b, |g (t, b)| ∂ν := by rw [hG]; exact abs_integral_le_integral_abs
      _ ≤ ∫ b, Cg ∂ν := by
            apply integral_mono ((hfib_g t).abs) (integrable_const Cg)
            intro b; exact hgC (t, b)
      _ = Cg := by simp
  have hFmono : Monotone F := by
    intro t1 t2 ht; rw [hF]
    apply integral_mono (hfib_f t1) (hfib_f t2)
    intro b; exact hfmono (Prod.mk_le_mk.mpr ⟨ht, le_refl b⟩)
  have hGmono : Monotone G := by
    intro t1 t2 ht; rw [hG]
    apply integral_mono (hfib_g t1) (hfib_g t2)
    intro b; exact hgmono (Prod.mk_le_mk.mpr ⟨ht, le_refl b⟩)
  
  have hfgi : Integrable (fun z : ℝ × β => f z * g z) (μ.prod ν) :=
    ContinuousFKG.integrable_of_bdd (μ.prod ν) (hfm.mul hgm) (C := Cf * Cg) (fun z => by
      rw [abs_mul]; exact mul_le_mul (hfC z) (hgC z) (abs_nonneg _) hCf0)
  have hfi : Integrable f (μ.prod ν) := ContinuousFKG.integrable_of_bdd (μ.prod ν) hfm hfC
  have hgi : Integrable g (μ.prod ν) := ContinuousFKG.integrable_of_bdd (μ.prod ν) hgm hgC
  
  have hmargf : ∫ z, f z ∂(μ.prod ν) = ∫ t, F t ∂μ := by rw [integral_prod f hfi]
  have hmargg : ∫ z, g z ∂(μ.prod ν) = ∫ t, G t ∂μ := by rw [integral_prod g hgi]
  set H : ℝ → ℝ := fun t => ∫ b, f (t, b) * g (t, b) ∂ν with hH
  have hmargfg : ∫ z, f z * g z ∂(μ.prod ν) = ∫ t, H t ∂μ := by
    rw [integral_prod (fun z => f z * g z) hfgi]
  
  have hinner : ∀ t, F t * G t ≤ H t := by
    intro t
    have := hν (fun b => f (t, b)) (fun b => g (t, b))
      (hfm.comp (measurable_const.prodMk measurable_id))
      (hgm.comp (measurable_const.prodMk measurable_id))
      ⟨Cf, fun b => hfC (t, b)⟩ ⟨Cg, fun b => hgC (t, b)⟩
      (fun _ _ hb => hfmono (Prod.mk_le_mk.mpr ⟨le_refl t, hb⟩))
      (fun _ _ hb => hgmono (Prod.mk_le_mk.mpr ⟨le_refl t, hb⟩))
    simpa [hF, hG, hH] using this
  have hHi : Integrable H μ := by simpa [hH] using hfgi.integral_prod_left
  have hFGi : Integrable (fun t => F t * G t) μ :=
    ContinuousFKG.integrable_of_bdd μ (hFm.mul hGm) (C := Cf * Cg) (fun t => by
      rw [abs_mul]; exact mul_le_mul (hFC t) (hGC t) (abs_nonneg _) hCf0)
  
  calc (∫ z, f z ∂(μ.prod ν)) * (∫ z, g z ∂(μ.prod ν))
      = (∫ t, F t ∂μ) * (∫ t, G t ∂μ) := by rw [hmargf, hmargg]
    _ ≤ ∫ t, F t * G t ∂μ := hcheb F G hFm hGm ⟨Cf, hFC⟩ ⟨Cg, hGC⟩ hFmono hGmono
    _ ≤ ∫ t, H t ∂μ := integral_mono hFGi hHi hinner
    _ = ∫ z, f z * g z ∂(μ.prod ν) := by rw [hmargfg]




theorem hasFKG_of_orderIso
    {β γ : Type*} [MeasurableSpace β] [Preorder β] [MeasurableSpace γ] [Preorder γ]
    (μ : Measure β) (ν : Measure γ) (e : β ≃ᵐ γ)
    (hmp : MeasurePreserving e μ ν) (hmonoinv : Monotone e.symm)
    (hν : HasFKG ν) : HasFKG μ := by
  intro f g hfm hgm ⟨Cf, hfC⟩ ⟨Cg, hgC⟩ hfmono hgmono
  have hfsm : Measurable e.symm := e.symm.measurable
  have hf' : Measurable (f ∘ e.symm) := hfm.comp hfsm
  have hg' : Measurable (g ∘ e.symm) := hgm.comp hfsm
  have hf'mono : Monotone (f ∘ e.symm) := hfmono.comp hmonoinv
  have hg'mono : Monotone (g ∘ e.symm) := hgmono.comp hmonoinv
  have key := hν (f ∘ e.symm) (g ∘ e.symm) hf' hg'
    ⟨Cf, fun c => hfC _⟩ ⟨Cg, fun c => hgC _⟩ hf'mono hg'mono
  have cov_f : ∫ b, f b ∂μ = ∫ c, (f ∘ e.symm) c ∂ν := by
    rw [← hmp.integral_comp' (f ∘ e.symm)]; simp [Function.comp]
  have cov_g : ∫ b, g b ∂μ = ∫ c, (g ∘ e.symm) c ∂ν := by
    rw [← hmp.integral_comp' (g ∘ e.symm)]; simp [Function.comp]
  have cov_fg : ∫ b, f b * g b ∂μ = ∫ c, (f ∘ e.symm) c * (g ∘ e.symm) c ∂ν := by
    rw [← hmp.integral_comp' (fun c => (f ∘ e.symm) c * (g ∘ e.symm) c)]; simp [Function.comp]
  rw [cov_f, cov_g, cov_fg]; exact key



theorem piFinSuccAbove_reflect (n : ℕ) (x y : Fin (n + 1) → ℝ)
    (h : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0) x
        ≤ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0) y) :
    x ≤ y := by
  rw [Prod.mk_le_mk] at h
  obtain ⟨h0, hs⟩ := h
  intro i
  refine Fin.cases ?_ ?_ i
  · exact h0
  · intro j; simpa [Fin.succAbove_zero] using hs j


theorem piFinSuccAbove_symm_mono (n : ℕ) :
    Monotone (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm := by
  intro p q hpq
  apply piFinSuccAbove_reflect n
  rw [MeasurableEquiv.apply_symm_apply, MeasurableEquiv.apply_symm_apply]
  exact hpq


noncomputable def unitMeasure : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure unitMeasure := by
  constructor
  rw [unitMeasure, Measure.restrict_apply_univ, Real.volume_Icc]; norm_num



theorem hasFKG_pi_unitMeasure (n : ℕ) :
    HasFKG (Measure.pi (fun _ : Fin n => unitMeasure)) := by
  induction n with
  | zero =>
      
      exact hasFKG_subsingleton _
  | succ n ih =>
      
      have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => unitMeasure) 0
      
      
      have hstep : HasFKG (((fun _ : Fin (n + 1) => unitMeasure) 0).prod
          (Measure.pi fun j : Fin n =>
            (fun _ : Fin (n + 1) => unitMeasure) ((0 : Fin (n + 1)).succAbove j))) :=
        prod_fkg_step unitMeasure _ (hasFKG_real unitMeasure) ih
      exact hasFKG_of_orderIso _ _ _ hmp (piFinSuccAbove_symm_mono n) hstep









theorem continuous_fkg (n : ℕ)
    {f g : (Fin n → ℝ) → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    {Cf Cg : ℝ} (hfC : ∀ x, |f x| ≤ Cf) (hgC : ∀ x, |g x| ≤ Cg)
    (hf : Monotone f) (hg : Monotone g) :
    (∫ x, f x ∂(Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1))))
      * (∫ x, g x ∂(Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1))))
    ≤ ∫ x, f x * g x ∂(Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1))) :=
  hasFKG_pi_unitMeasure n f g hfm hgm ⟨Cf, hfC⟩ ⟨Cg, hgC⟩ hf hg

end Probability
end StatMech
