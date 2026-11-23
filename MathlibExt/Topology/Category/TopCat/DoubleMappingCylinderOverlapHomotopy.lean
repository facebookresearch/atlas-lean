/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.DoubleMappingCylinderOpenCharts
public import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Analysis.Convex.Basic

/-!
# The actual open-overlap projection is a homotopy equivalence

The computed middle chart identifies the original overlap coordinates.
The shared mapping-cylinder interpolation contracts only its interval
coordinate. Convexity proves that the entire family stays in the actual
open overlap. The forward map is the original overlap projection.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContinuousMap

universe u

namespace TopCat.DoubleMappingCylinderOverlapContraction

private def center : TopCat.I.{u} :=
  (TopCat.I.homeomorph.{u}).symm (⟨(1 / 2 : ℝ), by norm_num⟩ : unitInterval)

private theorem center_height : (TopCat.I.homeomorph center : ℝ) = 1 / 2 := by
  simp only [center, Homeomorph.apply_symm_apply]

private theorem interpolate_mem (s : unitInterval) (t : TopCat.I.{u})
    (ht : (TopCat.I.homeomorph t : ℝ) ∈ Set.Ioo (1 / 3) (2 / 3)) :
    (TopCat.I.homeomorph (mappingCylinderInterpolate center s t) : ℝ) ∈
      Set.Ioo (1 / 3) (2 / 3) := by
  have hm : (TopCat.I.homeomorph center : ℝ) ∈ Set.Ioo (1 / 3) (2 / 3) := by
    rw [center_height]
    norm_num
  have hc := (convex_Ioo (𝕜 := ℝ) (β := ℝ) (1 / 3) (2 / 3)) ht hm
    (sub_nonneg.mpr s.property.2) s.property.1 (by ring : 1 - (s : ℝ) + s = 1)
  rw [mappingCylinderInterpolate_height]
  simpa only [smul_eq_mul] using hc

private abbrev M {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :=
  doubleMappingCylinderMiddleRegion i f (doubleMappingCylinderOverlap i f)

private theorem time_mem {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H)
    (p : M i f) :
    (TopCat.I.homeomorph p.val.2 : ℝ) ∈ Set.Ioo (1 / 3) (2 / 3) := by
  have h := (mem_doubleMappingCylinderOverlap i f _).mp p.property
  rw [← doubleMappingCylinderMiddle_apply, doubleMappingCylinderHeight_middle] at h
  exact h

private theorem center_mem {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) (x : X) :
    doubleMappingCylinderCylinderMap i f (mappingCylinderCylinder i (x, center)) ∈
      doubleMappingCylinderOverlap i f := by
  apply (mem_doubleMappingCylinderOverlap i f _).mpr
  rw [← doubleMappingCylinderMiddle_apply, doubleMappingCylinderHeight_middle,
    center_height]
  norm_num

private def first {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) : M i f ⟶ X :=
  TopCat.ofHom ⟨fun p => p.val.1, continuous_fst.comp continuous_subtype_val⟩

private def sectionCenter {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) : X ⟶ M i f :=
  TopCat.ofHom ⟨fun x => ⟨(x, center), center_mem i f x⟩,
    (continuous_id.prodMk continuous_const).subtype_mk _⟩

private def middleContraction {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    TopCat.Homotopy (𝟙 (M i f)) (first i f ≫ sectionCenter i f) where
  toFun z := ⟨(z.2.val.1, mappingCylinderInterpolate center z.1 z.2.val.2), by
    apply (mem_doubleMappingCylinderOverlap i f _).mpr
    rw [← doubleMappingCylinderMiddle_apply, doubleMappingCylinderHeight_middle]
    exact interpolate_mem z.1 z.2.val.2 (time_mem i f z.2)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)).prodMk
      ((continuous_mappingCylinderInterpolate center).comp
        (continuous_fst.prodMk
          (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))))
  map_zero_left p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact mappingCylinderInterpolate_zero center p.val.2
  map_one_left p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact mappingCylinderInterpolate_one center p.val.2

private def middleEquivalence {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    M i f ≃ₕ X where
  toFun := (first i f).hom
  invFun := (sectionCenter i f).hom
  left_inv := ⟨(middleContraction i f).symm.cast
    (TopCat.hom_comp (first i f) (sectionCenter i f))
    (TopCat.hom_id (X := M i f))⟩
  right_inv := ⟨ContinuousMap.Homotopy.refl (ContinuousMap.id X)⟩

/-- The same original overlap projection has a derived actual homotopy
inverse. The given computed chart and shared interpolation are used once;
no overlap model, equivalence, weakness or contraction witness is input. -/
public def _root_.TopCat.doubleMappingCylinderOverlapHomotopyEquiv
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    {e : TopCat.of (doubleMappingCylinderOverlap i f : Set (doubleMappingCylinder i f)) ≃ₕ X //
      e.toFun = (doubleMappingCylinderOverlapProjection i f).hom ∧
        e.invFun = (doubleMappingCylinderMidpoint i f).hom} := by
  let a := doubleMappingCylinderOverlapIso i f
  let e := (TopCat.homeoOfIso a).symm.toHomotopyEquiv.trans (middleEquivalence i f)
  refine ⟨e, ?_, ?_⟩
  · apply ContinuousMap.ext
    intro z
    change (a.inv z).val.1 = doubleMappingCylinderOverlapProjection i f z
    have h := doubleMappingCylinderOverlapProjection_middle i f (a.inv z)
    have hz : a.hom (a.inv z) = z := ConcreteCategory.congr_hom a.inv_hom_id z
    exact ((congrArg (doubleMappingCylinderOverlapProjection i f).hom hz).symm.trans h).symm
  · apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    change (a.hom (sectionCenter i f x)).val = (doubleMappingCylinderMidpoint i f x).val
    have h₀ := congrArg Subtype.val
      (doubleMappingCylinderOverlapIso_hom_apply i f (sectionCenter i f x))
    have hm : doubleMappingCylinderMidpoint i f ≫
        AlgebraicTopology.subspaceIncl
          (doubleMappingCylinderOverlap i f : Set (doubleMappingCylinder i f)) =
        mappingCylinderEndpoint X center ≫ doubleMappingCylinderMiddle i f :=
      doubleMappingCylinderMidpoint_inclusion i f
    have hL : (doubleMappingCylinderMidpoint i f ≫ AlgebraicTopology.subspaceIncl
        (doubleMappingCylinderOverlap i f : Set (doubleMappingCylinder i f))).hom x =
        (doubleMappingCylinderMidpoint i f x).val :=
      congrArg (fun k : C(X, doubleMappingCylinder i f) => k x)
        (TopCat.hom_comp (doubleMappingCylinderMidpoint i f)
          (AlgebraicTopology.subspaceIncl
            (doubleMappingCylinderOverlap i f : Set (doubleMappingCylinder i f))))
    have hR : (mappingCylinderEndpoint X center ≫ doubleMappingCylinderMiddle i f).hom x =
        doubleMappingCylinderMiddle i f (x, center) :=
      (congrArg (fun k : C(X, doubleMappingCylinder i f) => k x)
        (TopCat.hom_comp (mappingCylinderEndpoint X center)
            (doubleMappingCylinderMiddle i f))).trans
          (congrArg (fun p : mappingCylinderDomain X => doubleMappingCylinderMiddle i f p)
            (mappingCylinderEndpoint_apply X center x))
    have h₁ : (doubleMappingCylinderMidpoint i f x).val =
        doubleMappingCylinderMiddle i f (x, center) :=
      hL.symm.trans ((congrArg (fun k : X ⟶ doubleMappingCylinder i f => k.hom x) hm).trans hR)
    exact h₀.trans h₁.symm

end TopCat.DoubleMappingCylinderOverlapContraction

end
