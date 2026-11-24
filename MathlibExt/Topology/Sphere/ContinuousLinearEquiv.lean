/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author : Avocado
-/
module

public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Pi
public import Mathlib.Topology.Algebra.Module.Equiv.Prod
public import Mathlib.Topology.Algebra.Module.Equiv.Submodule

@[expose] public section

namespace ContinuousLinearEquiv

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Homeomorphism between unit spheres induced by a continuous linear
equivalence `e : E ≃L[ℝ] F`. The forward map is `x ↦ ‖e x‖⁻¹ • e x`,
the inverse is `y ↦ ‖e.symm y‖⁻¹ • e.symm y`. Uses radial machinery. -/
noncomputable def unitSphereHomeomorph (e : E ≃L[ℝ] F) :
    Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : F) 1 where
  toFun x :=
    have hx_ne : x.1 ≠ 0 := by
      intro h0
      have h_zero : ‖x.1‖ = 0 := by simp [h0]
      have h_one : ‖x.1‖ = 1 := norm_eq_of_mem_sphere x
      linarith
    have he_ne : e x.1 ≠ 0 := fun h0 => hx_ne ((e.map_eq_zero_iff).mp h0)
    have hpos : 0 < ‖e x.1‖ := norm_pos_iff.mpr he_ne
    ⟨‖e x.1‖⁻¹ • e x.1, by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ (ne_of_gt hpos)]⟩
  invFun y :=
    have hy_ne : y.1 ≠ 0 := by
      intro h0
      have h_zero : ‖y.1‖ = 0 := by simp [h0]
      have h_one : ‖y.1‖ = 1 := norm_eq_of_mem_sphere y
      linarith
    have he_ne : e.symm y.1 ≠ 0 := fun h0 =>
      hy_ne (by
        have : y.1 = e (e.symm y.1) := (e.apply_symm_apply y.1).symm
        rw [this, h0, map_zero])
    have hpos : 0 < ‖e.symm y.1‖ := norm_pos_iff.mpr he_ne
    ⟨‖e.symm y.1‖⁻¹ • e.symm y.1, by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ (ne_of_gt hpos)]⟩
  left_inv x := by
    have h1 : ‖x.1‖ = 1 := norm_eq_of_mem_sphere x
    have hx_ne : x.1 ≠ 0 := by
      intro h0
      have : ‖x.1‖ = 0 := by simp [h0]
      linarith
    have he_ne : e x.1 ≠ 0 := fun h0 => hx_ne ((e.map_eq_zero_iff).mp h0)
    have hpos : 0 < ‖e x.1‖ := norm_pos_iff.mpr he_ne
    apply Subtype.ext
    change ‖e.symm (‖e x.1‖⁻¹ • e x.1)‖⁻¹ • e.symm (‖e x.1‖⁻¹ • e x.1) = x.1
    have h_eq : e.symm (‖e x.1‖⁻¹ • e x.1) = ‖e x.1‖⁻¹ • x.1 := by
      rw [map_smul, e.symm_apply_apply]
    rw [h_eq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos),
      h1, mul_one, inv_inv, smul_smul, mul_inv_cancel₀ (ne_of_gt hpos), one_smul]
  right_inv y := by
    have h1 : ‖y.1‖ = 1 := norm_eq_of_mem_sphere y
    have hy_ne : y.1 ≠ 0 := by
      intro h0
      have : ‖y.1‖ = 0 := by simp [h0]
      linarith
    have he_ne : e.symm y.1 ≠ 0 := fun h0 =>
      hy_ne (by
        have : y.1 = e (e.symm y.1) := (e.apply_symm_apply y.1).symm
        rw [this, h0, map_zero])
    have hpos : 0 < ‖e.symm y.1‖ := norm_pos_iff.mpr he_ne
    apply Subtype.ext
    change ‖e (‖e.symm y.1‖⁻¹ • e.symm y.1)‖⁻¹ • e (‖e.symm y.1‖⁻¹ • e.symm y.1) = y.1
    have h_eq : e (‖e.symm y.1‖⁻¹ • e.symm y.1) = ‖e.symm y.1‖⁻¹ • y.1 := by
      rw [map_smul, e.apply_symm_apply]
    rw [h_eq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos),
      h1, mul_one, inv_inv, smul_smul, mul_inv_cancel₀ (ne_of_gt hpos), one_smul]
  continuous_toFun := by
    apply Continuous.subtype_mk
    have h_e : Continuous (fun x : Metric.sphere (0 : E) 1 => e x.1) :=
      e.continuous_toFun.comp continuous_subtype_val
    have h_ne : ∀ x : Metric.sphere (0 : E) 1, e x.1 ≠ 0 := by
      intro x
      have hx_ne : x.1 ≠ 0 := by
        have h1 : ‖x.1‖ = 1 := norm_eq_of_mem_sphere x
        intro h0
        have : ‖x.1‖ = 0 := by simp [h0]
        linarith
      exact fun h0 => hx_ne ((e.map_eq_zero_iff).mp h0)
    have h_mem : ∀ x : Metric.sphere (0 : E) 1, e x.1 ∈ ({0}ᶜ : Set F) := fun x =>
      Set.mem_compl_singleton_iff.mpr (h_ne x)
    have h_sub : Continuous (fun x : Metric.sphere (0 : E) 1 =>
        (⟨e x.1, h_mem x⟩ : ({0}ᶜ : Set F))) :=
      Continuous.subtype_mk h_e h_mem
    have h_cont : Continuous (fun x : Metric.sphere (0 : E) 1 =>
        (((homeomorphUnitSphereProd (E := F)) ⟨e x.1, h_mem x⟩).1 : F)) :=
      continuous_subtype_val.comp
        (continuous_fst.comp
          ((homeomorphUnitSphereProd (E := F)).continuous_toFun.comp h_sub))
    have h_eq : (fun x : Metric.sphere (0 : E) 1 => ‖e x.1‖⁻¹ • e x.1) =
        (fun x => (((homeomorphUnitSphereProd (E := F)) ⟨e x.1, h_mem x⟩).1 : F)) := by
      funext x
      exact (homeomorphUnitSphereProd_apply_fst_coe (E := F) ⟨e x.1, h_mem x⟩).symm
    rw [h_eq]
    exact h_cont
  continuous_invFun := by
    apply Continuous.subtype_mk
    have h_e : Continuous (fun y : Metric.sphere (0 : F) 1 => e.symm y.1) :=
      e.symm.continuous_toFun.comp continuous_subtype_val
    have h_ne : ∀ y : Metric.sphere (0 : F) 1, e.symm y.1 ≠ 0 := by
      intro y
      have hy_ne : y.1 ≠ 0 := by
        have h1 : ‖y.1‖ = 1 := norm_eq_of_mem_sphere y
        intro h0
        have : ‖y.1‖ = 0 := by simp [h0]
        linarith
      exact fun h0 =>
        hy_ne (by
          have : y.1 = e (e.symm y.1) := (e.apply_symm_apply y.1).symm
          rw [this, h0, map_zero])
    have h_mem : ∀ y : Metric.sphere (0 : F) 1, e.symm y.1 ∈ ({0}ᶜ : Set E) := fun y =>
      Set.mem_compl_singleton_iff.mpr (h_ne y)
    have h_sub : Continuous (fun y : Metric.sphere (0 : F) 1 =>
        (⟨e.symm y.1, h_mem y⟩ : ({0}ᶜ : Set E))) :=
      Continuous.subtype_mk h_e h_mem
    have h_cont : Continuous (fun y : Metric.sphere (0 : F) 1 =>
        (((homeomorphUnitSphereProd (E := E)) ⟨e.symm y.1, h_mem y⟩).1 : E)) :=
      continuous_subtype_val.comp
        (continuous_fst.comp
          ((homeomorphUnitSphereProd (E := E)).continuous_toFun.comp h_sub))
    have h_eq : (fun y : Metric.sphere (0 : F) 1 => ‖e.symm y.1‖⁻¹ • e.symm y.1) =
        (fun y => (((homeomorphUnitSphereProd (E := E)) ⟨e.symm y.1, h_mem y⟩).1 : E)) := by
      funext y
      exact (homeomorphUnitSphereProd_apply_fst_coe (E := E) ⟨e.symm y.1, h_mem y⟩).symm
    rw [h_eq]
    exact h_cont

/-- The forward map of `unitSphereHomeomorph` is the normalized image. -/
@[simp]
theorem unitSphereHomeomorph_apply_coe (e : E ≃L[ℝ] F)
    (x : Metric.sphere (0 : E) 1) :
    (unitSphereHomeomorph e x : F) = ‖e x.1‖⁻¹ • e x.1 :=
  rfl

/-- The inverse map is the normalized preimage via `e.symm`. -/
@[simp]
theorem unitSphereHomeomorph_symm_apply_coe (e : E ≃L[ℝ] F)
    (y : Metric.sphere (0 : F) 1) :
    ((unitSphereHomeomorph e).symm y : E) = ‖e.symm y.1‖⁻¹ • e.symm y.1 :=
  rfl

/-- The unit sphere homeomorphism induced by the identity is the identity. -/
@[simp] theorem unitSphereHomeomorph_refl
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    unitSphereHomeomorph (ContinuousLinearEquiv.refl ℝ E) =
      Homeomorph.refl (Metric.sphere (0 : E) 1) := by
  apply Homeomorph.ext
  intro x
  apply Subtype.ext
  simp [unitSphereHomeomorph_apply_coe, ContinuousLinearEquiv.refl_apply,
    norm_eq_of_mem_sphere]

/-- Pointwise composition law for the normalized sphere homeomorphisms. -/
theorem unitSphereHomeomorph_trans_apply_coe
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (e : E ≃L[ℝ] F) (f : F ≃L[ℝ] G)
    (x : Metric.sphere (0 : E) 1) :
    (unitSphereHomeomorph (e.trans f) x : G) =
      (unitSphereHomeomorph f (unitSphereHomeomorph e x) : G) := by
  have hx_ne : x.1 ≠ 0 := by
    intro h0
    have : ‖x.1‖ = 0 := by simp [h0]
    have : ‖x.1‖ = 1 := norm_eq_of_mem_sphere x
    linarith
  have he_ne : e x.1 ≠ 0 := fun h0 => hx_ne ((e.map_eq_zero_iff).mp h0)
  have hpos_e : 0 < ‖e x.1‖ := norm_pos_iff.mpr he_ne
  have hpos_inv_e : 0 < (‖e x.1‖⁻¹ : ℝ) := inv_pos.mpr hpos_e
  have hf_ne : f (e x.1) ≠ 0 := fun h0 => he_ne ((f.map_eq_zero_iff).mp h0)
  have h_left : (unitSphereHomeomorph (e.trans f) x : G) =
      ‖f (e x.1)‖⁻¹ • f (e x.1) := by
    simp [unitSphereHomeomorph_apply_coe, ContinuousLinearEquiv.trans_apply]
  have h_f_smul : f (‖e x.1‖⁻¹ • e x.1) = ‖e x.1‖⁻¹ • f (e x.1) := by
    rw [map_smul]
  have h_norm : ‖f (‖e x.1‖⁻¹ • e x.1)‖ = ‖e x.1‖⁻¹ * ‖f (e x.1)‖ := by
    rw [h_f_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hpos_inv_e]
  have h_right : (unitSphereHomeomorph f (unitSphereHomeomorph e x) : G) =
      ‖f (‖e x.1‖⁻¹ • e x.1)‖⁻¹ • f (‖e x.1‖⁻¹ • e x.1) := by
    have h1 : (unitSphereHomeomorph f (unitSphereHomeomorph e x) : G) =
        ‖f ((unitSphereHomeomorph e x).1)‖⁻¹ • f ((unitSphereHomeomorph e x).1) :=
      unitSphereHomeomorph_apply_coe f (unitSphereHomeomorph e x)
    have h2 : ((unitSphereHomeomorph e x).1 : F) = ‖e x.1‖⁻¹ • e x.1 :=
      unitSphereHomeomorph_apply_coe e x
    rw [h1, h2]
  rw [h_left, h_right, h_norm, h_f_smul, smul_smul]
  have h_scalar : (‖e x.1‖⁻¹ * ‖f (e x.1)‖)⁻¹ * ‖e x.1‖⁻¹ = ‖f (e x.1)‖⁻¹ := by
    field_simp
  rw [h_scalar]

/-- Composition law for the unit sphere homeomorphisms. -/
theorem unitSphereHomeomorph_trans
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (e : E ≃L[ℝ] F) (f : F ≃L[ℝ] G) :
    unitSphereHomeomorph (e.trans f) =
      (unitSphereHomeomorph e).trans (unitSphereHomeomorph f) := by
  apply Homeomorph.ext
  intro x
  apply Subtype.ext
  exact unitSphereHomeomorph_trans_apply_coe e f x

/-- The inverse of the sphere homeomorphism is the sphere homeomorphism of the inverse. -/
@[simp] theorem unitSphereHomeomorph_symm (e : E ≃L[ℝ] F) :
    (unitSphereHomeomorph e).symm = unitSphereHomeomorph e.symm := by
  apply Homeomorph.ext
  intro y
  apply Subtype.ext
  simp [unitSphereHomeomorph_symm_apply_coe, unitSphereHomeomorph_apply_coe]

end ContinuousLinearEquiv
