/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































import Mathlib
import Code.SLE.Defs

open scoped UpperHalfPlane NNReal
open Filter Topology Complex Bornology

namespace StatMech.SLE











theorem tendsto_cocompact_iff_norm (l : Filter ℂ) (f : ℂ → ℂ) :
    Tendsto f l (cocompact ℂ) ↔ Tendsto (fun z => ‖f z‖) l atTop := by
  rw [← Metric.cobounded_eq_cocompact (α := ℂ), ← comap_norm_atTop (E := ℂ), tendsto_comap_iff]
  rfl


theorem eventually_ne_zero_cocompact : ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 := by
  have hz : Tendsto (fun z : ℂ => ‖z‖) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
  filter_upwards [hz.eventually_gt_atTop 0] with z hz
  intro h; rw [h] at hz; simp at hz


theorem tendsto_inv_cocompact : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (nhds 0) := by
  have hz : Tendsto (fun z : ℂ => ‖z‖) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_inv]
  exact hz.inv_tendsto_atTop



theorem tendsto_div_cocompact {r : ℂ} (hr : r ≠ 0) :
    Tendsto (fun z : ℂ => z / r) (cocompact ℂ) (cocompact ℂ) := by
  have : (fun z : ℂ => z / r) = (fun z => r⁻¹ * z) := by funext z; rw [div_eq_inv_mul]
  rw [this]
  exact Filter.tendsto_cocompact_mul_left₀ (inv_ne_zero hr)



theorem tendsto_translate_cocompact (c : ℂ) :
    Tendsto (fun z : ℂ => z + c) (cocompact ℂ) (cocompact ℂ) := by
  rw [tendsto_cocompact_iff_norm]
  have hz : Tendsto (fun z : ℂ => ‖z‖) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
  have hlow : Tendsto (fun z : ℂ => ‖z‖ - ‖c‖) (cocompact ℂ) atTop := by
    simpa using hz.atTop_add (tendsto_const_nhds (x := -‖c‖))
  refine tendsto_atTop_mono (fun z => ?_) hlow
  have : ‖z‖ ≤ ‖z + c‖ + ‖c‖ := by
    calc ‖z‖ = ‖(z + c) - c‖ := by ring_nf
      _ ≤ ‖z + c‖ + ‖c‖ := norm_sub_le _ _
  linarith





theorem tendsto_cocompact_of_sub {g : ℂ → ℂ}
    (h0 : Tendsto (fun z => g z - z) (cocompact ℂ) (nhds 0)) :
    Tendsto g (cocompact ℂ) (cocompact ℂ) := by
  rw [tendsto_cocompact_iff_norm]
  have hz : Tendsto (fun z : ℂ => ‖z‖) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
  have hd : Tendsto (fun z => ‖g z - z‖) (cocompact ℂ) (nhds 0) := by simpa using h0.norm
  have hlow : Tendsto (fun z => ‖z‖ - ‖g z - z‖) (cocompact ℂ) atTop := by
    have : Tendsto (fun z => ‖z‖ + (- ‖g z - z‖)) (cocompact ℂ) atTop :=
      Filter.Tendsto.atTop_add hz (by simpa using hd.neg)
    simpa [sub_eq_add_neg] using this
  refine tendsto_atTop_mono (fun z => ?_) hlow
  have : ‖z‖ ≤ ‖g z‖ + ‖g z - z‖ := by
    calc ‖z‖ = ‖g z - (g z - z)‖ := by ring_nf
      _ ≤ ‖g z‖ + ‖g z - z‖ := norm_sub_le _ _
  linarith





theorem tendsto_div_self {g : ℂ → ℂ}
    (h0 : Tendsto (fun z => g z - z) (cocompact ℂ) (nhds 0)) :
    Tendsto (fun z => z / g z) (cocompact ℂ) (nhds 1) := by
  have hgz : Tendsto (fun z : ℂ => g z / z) (cocompact ℂ) (nhds 1) := by
    have hsplit : (fun z : ℂ => g z / z) =ᶠ[cocompact ℂ] (fun z => 1 + (g z - z) * z⁻¹) := by
      filter_upwards [eventually_ne_zero_cocompact] with z hz
      field_simp; ring
    rw [tendsto_congr' hsplit]
    have : Tendsto (fun z : ℂ => (g z - z) * z⁻¹) (cocompact ℂ) (nhds 0) := by
      simpa using h0.mul tendsto_inv_cocompact
    simpa using (tendsto_const_nhds (x := (1:ℂ))).add this
  have heq : (fun z : ℂ => z / g z) =ᶠ[cocompact ℂ] (fun z => (g z / z)⁻¹) := by
    have hgne : ∀ᶠ z in cocompact ℂ, g z ≠ 0 :=
      (tendsto_cocompact_of_sub h0).eventually eventually_ne_zero_cocompact
    filter_upwards [eventually_ne_zero_cocompact, hgne] with z hz hgz0
    rw [inv_div]
  rw [tendsto_congr' heq]
  simpa using hgz.inv₀ (by norm_num)














theorem hasHalfPlaneCapacity_neg_example : HasHalfPlaneCapacity (fun z => z - z⁻¹) (-1) := by
  constructor
  · have hfun : (fun z : ℂ => (z - z⁻¹) - z) = (fun z => (-1 : ℂ) * z⁻¹) := by
      funext z; ring
    rw [hfun]; simpa using tendsto_inv_cocompact.const_mul (-1 : ℂ)
  · have hfun : (fun z : ℂ => z * ((z - z⁻¹) - z)) =ᶠ[cocompact ℂ] (fun _ => ((-1 : ℝ) : ℂ)) := by
      filter_upwards [eventually_ne_zero_cocompact] with z hz
      push_cast; field_simp; ring
    rw [tendsto_congr' hfun]; exact tendsto_const_nhds













theorem HasHalfPlaneCapacity.comp {g₁ g₂ : ℂ → ℂ} {a₁ a₂ : ℝ}
    (h₁ : HasHalfPlaneCapacity g₁ a₁) (h₂ : HasHalfPlaneCapacity g₂ a₂) :
    HasHalfPlaneCapacity (g₂ ∘ g₁) (a₁ + a₂) := by
  obtain ⟨h₁0, h₁a⟩ := h₁
  obtain ⟨h₂0, h₂a⟩ := h₂
  have hg₁cc : Tendsto g₁ (cocompact ℂ) (cocompact ℂ) := tendsto_cocompact_of_sub h₁0
  refine ⟨?_, ?_⟩
  · 
    have e1 : Tendsto (fun z => g₂ (g₁ z) - g₁ z) (cocompact ℂ) (nhds 0) := h₂0.comp hg₁cc
    have hfun : (fun z => (g₂ ∘ g₁) z - z) = (fun z => (g₂ (g₁ z) - g₁ z) + (g₁ z - z)) := by
      funext z; simp [Function.comp]
    rw [hfun]; simpa using e1.add h₁0
  · 
    have part2 : Tendsto (fun z => z * (g₁ z - z)) (cocompact ℂ) (nhds (a₁ : ℂ)) := h₁a
    have inner : Tendsto (fun z => g₁ z * (g₂ (g₁ z) - g₁ z)) (cocompact ℂ) (nhds (a₂ : ℂ)) :=
      h₂a.comp hg₁cc
    have hdiv : Tendsto (fun z => z / g₁ z) (cocompact ℂ) (nhds 1) := tendsto_div_self h₁0
    have part1 : Tendsto (fun z => z * (g₂ (g₁ z) - g₁ z)) (cocompact ℂ) (nhds (a₂ : ℂ)) := by
      have hmul := hdiv.mul inner
      simp only [one_mul] at hmul
      refine hmul.congr' ?_
      filter_upwards [eventually_ne_zero_cocompact,
        hg₁cc.eventually eventually_ne_zero_cocompact] with z hz hg₁z
      field_simp
    have hsum := part1.add part2
    have hfun : (fun z => z * ((g₂ ∘ g₁) z - z))
        = (fun z => z * (g₂ (g₁ z) - g₁ z) + z * (g₁ z - z)) := by
      funext z; simp only [Function.comp]; ring
    rw [hfun]
    have hcast : ((a₁ + a₂ : ℝ) : ℂ) = (a₂ : ℂ) + (a₁ : ℂ) := by push_cast; ring
    rw [hcast]; exact hsum
















theorem HasHalfPlaneCapacity.le_of_comp {g h g' : ℂ → ℂ} {a b a' : ℝ}
    (hg : HasHalfPlaneCapacity g a) (hh : HasHalfPlaneCapacity h b)
    (hb : 0 ≤ b) (hfac : g' = h ∘ g) (hg' : HasHalfPlaneCapacity g' a') :
    a ≤ a' := by
  have hcomp : HasHalfPlaneCapacity g' (a + b) := hfac ▸ hg.comp hh
  have : a' = a + b := hg'.unique hcomp
  rw [this]; linarith












theorem HasHalfPlaneCapacity.scale {g : ℂ → ℂ} {a : ℝ} {r : ℝ} (hr : r ≠ 0)
    (hg : HasHalfPlaneCapacity g a) :
    HasHalfPlaneCapacity (fun z => (r : ℂ) * g (z / r)) (r ^ 2 * a) := by
  obtain ⟨h0, ha⟩ := hg
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hcc : Tendsto (fun z : ℂ => z / (r : ℂ)) (cocompact ℂ) (cocompact ℂ) :=
    tendsto_div_cocompact hrc
  refine ⟨?_, ?_⟩
  · 
    have hfun : (fun z => (r : ℂ) * g (z / r) - z)
        = (fun z => (r : ℂ) * (g (z / (r : ℂ)) - z / (r : ℂ))) := by
      funext z; field_simp
    rw [hfun]
    have e1 : Tendsto (fun z => g (z / (r : ℂ)) - z / (r : ℂ)) (cocompact ℂ) (nhds 0) := by
      simpa [Function.comp] using h0.comp hcc
    simpa using e1.const_mul (r : ℂ)
  · 
    have e2 : Tendsto (fun z => (z / (r : ℂ)) * (g (z / (r : ℂ)) - z / (r : ℂ)))
        (cocompact ℂ) (nhds (a : ℂ)) := by
      simpa [Function.comp] using ha.comp hcc
    have hfun : (fun z => z * ((r : ℂ) * g (z / r) - z))
        = (fun z => (r : ℂ) ^ 2 * ((z / (r : ℂ)) * (g (z / (r : ℂ)) - z / (r : ℂ)))) := by
      funext z; field_simp
    rw [hfun]
    have hcast : (((r ^ 2 * a : ℝ)) : ℂ) = (r : ℂ) ^ 2 * (a : ℂ) := by push_cast; ring
    rw [hcast]
    exact e2.const_mul ((r : ℂ) ^ 2)










theorem HasHalfPlaneCapacity.translate {g : ℂ → ℂ} {a : ℝ} (c : ℂ)
    (hg : HasHalfPlaneCapacity g a) :
    HasHalfPlaneCapacity (fun z => g (z - c) + c) a := by
  obtain ⟨h0, ha⟩ := hg
  have hcc : Tendsto (fun z : ℂ => z - c) (cocompact ℂ) (cocompact ℂ) := by
    simpa [sub_eq_add_neg] using tendsto_translate_cocompact (-c)
  have e0 : Tendsto (fun z => g (z - c) - (z - c)) (cocompact ℂ) (nhds 0) := by
    simpa [Function.comp] using h0.comp hcc
  refine ⟨?_, ?_⟩
  · have hfun : (fun z => (g (z - c) + c) - z) = (fun z => g (z - c) - (z - c)) := by
      funext z; ring
    rw [hfun]; exact e0
  · have e2 : Tendsto (fun z => (z - c) * (g (z - c) - (z - c))) (cocompact ℂ) (nhds (a : ℂ)) := by
      simpa [Function.comp] using ha.comp hcc
    have e3 : Tendsto (fun z => c * (g (z - c) - (z - c))) (cocompact ℂ) (nhds 0) := by
      simpa using e0.const_mul c
    have hsum := e2.add e3
    have hfun : (fun z => z * ((g (z - c) + c) - z))
        = (fun z => (z - c) * (g (z - c) - (z - c)) + c * (g (z - c) - (z - c))) := by
      funext z; ring
    rw [hfun]; simpa using hsum













theorem hasHalfPlaneCapacity_halfDisk (c : ℝ) :
    HasHalfPlaneCapacity (fun z => z + (c : ℂ) / z) c := by
  refine ⟨?_, ?_⟩
  · have hfun : (fun z : ℂ => (z + (c : ℂ) / z) - z) = (fun z => (c : ℂ) * z⁻¹) := by
      funext z; rw [div_eq_mul_inv]; ring
    rw [hfun]; simpa using tendsto_inv_cocompact.const_mul (c : ℂ)
  · have hfun : (fun z : ℂ => z * ((z + (c : ℂ) / z) - z)) =ᶠ[cocompact ℂ] (fun _ => (c : ℂ)) := by
      filter_upwards [eventually_ne_zero_cocompact] with z hz
      field_simp; ring
    rw [tendsto_congr' hfun]; exact tendsto_const_nhds



theorem halfDisk_capacity_eq {c a : ℝ}
    (h : HasHalfPlaneCapacity (fun z => z + (c : ℂ) / z) a) : a = c :=
  h.unique (hasHalfPlaneCapacity_halfDisk c)





theorem halfDisk_scale_consistent {r : ℝ} (hr : r ≠ 0) :
    HasHalfPlaneCapacity (fun z => (r : ℂ) * ((z / r) + (1 : ℂ) / (z / r))) (r ^ 2 * 1) := by
  have h := (hasHalfPlaneCapacity_halfDisk 1).scale hr
  refine ⟨?_, ?_⟩
  · exact h.1
  · exact h.2





theorem halfDisk_scale_eq_formula {r : ℝ} (hr : r ≠ 0) {z : ℂ} (hz : z ≠ 0) :
    (r : ℂ) * ((z / r) + (1 : ℂ) / (z / r)) = z + ((r ^ 2 : ℝ) : ℂ) / z := by
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  push_cast
  field_simp











theorem hasHalfPlaneCapacity_empty : HasHalfPlaneCapacity id 0 :=
  hasHalfPlaneCapacity_id




theorem HasHalfPlaneCapacity.comp_id {g : ℂ → ℂ} {a : ℝ} (hg : HasHalfPlaneCapacity g a) :
    HasHalfPlaneCapacity (g ∘ id) (0 + a) :=
  hasHalfPlaneCapacity_id.comp hg



theorem HasHalfPlaneCapacity.id_comp {g : ℂ → ℂ} {a : ℝ} (hg : HasHalfPlaneCapacity g a) :
    HasHalfPlaneCapacity (id ∘ g) (a + 0) :=
  hg.comp hasHalfPlaneCapacity_id

end StatMech.SLE
