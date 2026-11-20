/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































import Code.Probability.ContinuousFKG

open MeasureTheory
open scoped BigOperators ENNReal

namespace StatMech
namespace Probability

set_option linter.unusedSectionVars false





noncomputable def cube (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => unitMeasure)

instance (n : ℕ) : IsProbabilityMeasure (cube n) := by
  unfold cube; infer_instance



theorem cube_eq (n : ℕ) :
    cube n = Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  rfl









theorem fkg_of_factor {α : Type*} [MeasurableSpace α] [Preorder α] (n : ℕ)
    (p : (Fin n → ℝ) → α) (hpm : Measurable p) (hpmono : Monotone p)
    {f₀ g₀ : α → ℝ} (hf₀m : Measurable f₀) (hg₀m : Measurable g₀)
    {Cf Cg : ℝ} (hf₀C : ∀ a, |f₀ a| ≤ Cf) (hg₀C : ∀ a, |g₀ a| ≤ Cg)
    (hf₀ : Monotone f₀) (hg₀ : Monotone g₀) :
    (∫ x, f₀ (p x) ∂(cube n)) * (∫ x, g₀ (p x) ∂(cube n))
      ≤ ∫ x, f₀ (p x) * g₀ (p x) ∂(cube n) := by
  rw [cube_eq]
  exact continuous_fkg n (hf₀m.comp hpm) (hg₀m.comp hpm)
    (fun x => hf₀C _) (fun x => hg₀C _) (hf₀.comp hpmono) (hg₀.comp hpmono)



def restrictCoords {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ℝ) : {i // i ∈ S} → ℝ :=
  fun i => x (i : Fin n)


theorem restrictCoords_mono {n : ℕ} (S : Finset (Fin n)) :
    Monotone (restrictCoords S) := fun _ _ h _ => h _


theorem measurable_restrictCoords {n : ℕ} (S : Finset (Fin n)) :
    Measurable (restrictCoords S) := by
  apply measurable_pi_lambda
  intro i; exact measurable_pi_apply _











theorem fkg_of_subset_coords {n : ℕ} (S : Finset (Fin n))
    {f₀ g₀ : ({i // i ∈ S} → ℝ) → ℝ} (hf₀m : Measurable f₀) (hg₀m : Measurable g₀)
    {Cf Cg : ℝ} (hf₀C : ∀ a, |f₀ a| ≤ Cf) (hg₀C : ∀ a, |g₀ a| ≤ Cg)
    (hf₀ : Monotone f₀) (hg₀ : Monotone g₀) :
    (∫ x, f₀ (restrictCoords S x) ∂(cube n)) * (∫ x, g₀ (restrictCoords S x) ∂(cube n))
      ≤ ∫ x, f₀ (restrictCoords S x) * g₀ (restrictCoords S x) ∂(cube n) :=
  fkg_of_factor n (restrictCoords S) (measurable_restrictCoords S)
    (restrictCoords_mono S) hf₀m hg₀m hf₀C hg₀C hf₀ hg₀












theorem fkg_second_block_fiber {m n : ℕ}
    {f g : (Fin m → ℝ) × (Fin n → ℝ) → ℝ}
    (hfm : Measurable f) (hgm : Measurable g)
    {Cf Cg : ℝ} (hfC : ∀ z, |f z| ≤ Cf) (hgC : ∀ z, |g z| ≤ Cg)
    (hf : ∀ U, Monotone (fun V => f (U, V))) (hg : ∀ U, Monotone (fun V => g (U, V)))
    (U : Fin m → ℝ) :
    (∫ V, f (U, V) ∂(cube n)) * (∫ V, g (U, V) ∂(cube n))
      ≤ ∫ V, f (U, V) * g (U, V) ∂(cube n) := by
  rw [cube_eq]
  exact continuous_fkg n
    (hfm.comp (measurable_const.prodMk measurable_id))
    (hgm.comp (measurable_const.prodMk measurable_id))
    (fun V => hfC _) (fun V => hgC _) (hf U) (hg U)













theorem fkg_second_block {m n : ℕ}
    {f g : (Fin m → ℝ) × (Fin n → ℝ) → ℝ}
    (hfm : Measurable f) (hgm : Measurable g)
    {Cf Cg : ℝ} (hfC : ∀ z, |f z| ≤ Cf) (hgC : ∀ z, |g z| ≤ Cg)
    (hf : ∀ U, Monotone (fun V => f (U, V))) (hg : ∀ U, Monotone (fun V => g (U, V))) :
    (∫ U, (∫ V, f (U, V) ∂(cube n)) * (∫ V, g (U, V) ∂(cube n)) ∂(cube m))
      ≤ ∫ z, f z * g z ∂((cube m).prod (cube n)) := by
  set μm := cube m
  set μn := cube n
  
  have hCf0 : 0 ≤ Cf := le_trans (abs_nonneg _) (hfC ⟨0, 0⟩)
  
  have hfgi : Integrable (fun z : (Fin m → ℝ) × (Fin n → ℝ) => f z * g z) (μm.prod μn) :=
    ContinuousFKG.integrable_of_bdd (μm.prod μn) (hfm.mul hgm) (C := Cf * Cg) (fun z => by
      rw [abs_mul]; exact mul_le_mul (hfC z) (hgC z) (abs_nonneg _) hCf0)
  
  set F : (Fin m → ℝ) → ℝ := fun U => ∫ V, f (U, V) ∂μn with hF
  set G : (Fin m → ℝ) → ℝ := fun U => ∫ V, g (U, V) ∂μn with hG
  set H : (Fin m → ℝ) → ℝ := fun U => ∫ V, f (U, V) * g (U, V) ∂μn with hH
  have hFm : Measurable F := (hfm.stronglyMeasurable.integral_prod_right').measurable
  have hGm : Measurable G := (hgm.stronglyMeasurable.integral_prod_right').measurable
  
  have hfib_f : ∀ U, Integrable (fun V => f (U, V)) μn := fun U =>
    ContinuousFKG.integrable_of_bdd μn (hfm.comp (measurable_const.prodMk measurable_id))
      (fun V => hfC (U, V))
  have hfib_g : ∀ U, Integrable (fun V => g (U, V)) μn := fun U =>
    ContinuousFKG.integrable_of_bdd μn (hgm.comp (measurable_const.prodMk measurable_id))
      (fun V => hgC (U, V))
  have hFC : ∀ U, |F U| ≤ Cf := by
    intro U
    calc |F U| ≤ ∫ V, |f (U, V)| ∂μn := by rw [hF]; exact abs_integral_le_integral_abs
      _ ≤ ∫ V, Cf ∂μn :=
            integral_mono ((hfib_f U).abs) (integrable_const Cf) (fun V => hfC (U, V))
      _ = Cf := by simp
  have hGC : ∀ U, |G U| ≤ Cg := by
    intro U
    calc |G U| ≤ ∫ V, |g (U, V)| ∂μn := by rw [hG]; exact abs_integral_le_integral_abs
      _ ≤ ∫ V, Cg ∂μn :=
            integral_mono ((hfib_g U).abs) (integrable_const Cg) (fun V => hgC (U, V))
      _ = Cg := by simp
  
  have hFGi : Integrable (fun U => F U * G U) μm :=
    ContinuousFKG.integrable_of_bdd μm (hFm.mul hGm) (C := Cf * Cg) (fun U => by
      rw [abs_mul]; exact mul_le_mul (hFC U) (hGC U) (abs_nonneg _) hCf0)
  have hHi : Integrable H μm := by simpa [hH] using hfgi.integral_prod_left
  
  calc (∫ U, F U * G U ∂μm)
      ≤ ∫ U, H U ∂μm :=
        integral_mono hFGi hHi
          (fun U => fkg_second_block_fiber hfm hgm hfC hgC hf hg U)
    _ = ∫ z, f z * g z ∂(μm.prod μn) := by rw [integral_prod (fun z => f z * g z) hfgi]

end Probability
end StatMech
