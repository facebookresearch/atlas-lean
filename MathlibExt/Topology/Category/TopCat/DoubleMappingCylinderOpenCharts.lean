/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.DoubleMappingCylinder
public import MathlibExt.Topology.Category.TopCat.PushoutOpenRestriction
public import MathlibExt.Topology.Category.TopCat.PushoutOpenComplement
public import MathlibExt.Topology.Category.TopCat.PushoutHomotopyDescent

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Actual open collar charts of the original double mapping cylinder

The middle away from the two endpoints is identified with its actual open
preimage using the existing pushout-complement homeomorphism twice. The
overlap, its midpoint and its X projection therefore retain the original
coordinates and whole inclusion map. The H/B endpoint avoidance is derived
from the actual height, not supplied as a cover or weak-comparison witness.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology AlgebraicTopology

universe u

namespace TopCat

/-- The actual middle preimage of an open subset, retaining both original
coprojections. This is a pure subspace predicate. -/
public abbrev doubleMappingCylinderMiddleRegion
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H)
    (O : TopologicalSpace.Opens (doubleMappingCylinder i f)) : TopCat.{u} :=
  TopCat.of {p : mappingCylinderDomain X |
    doubleMappingCylinderCylinderMap i f (mappingCylinderCylinder i p) ∈ O}

private abbrev cylinderRegion
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H)
    (O : TopologicalSpace.Opens (doubleMappingCylinder i f)) : TopCat.{u} :=
  TopCat.of ((doubleMappingCylinderCylinderMap i f) ⁻¹' (O : Set (doubleMappingCylinder i f)))

private theorem doubleMappingCylinder_named_isPushout
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    IsPushout (mappingCylinderSource i) f
      (doubleMappingCylinderCylinderMap i f) (doubleMappingCylinderH i f) := by
  rw [doubleMappingCylinderCylinderMap_eq, doubleMappingCylinderH_eq]
  exact IsPushout.of_hasPushout (mappingCylinderSource i) f

private theorem mappingCylinder_named_isPushout
    {X B : TopCat.{u}} (i : X ⟶ B) :
    IsPushout (mappingCylinderEndpoint X 1) i
      (mappingCylinderCylinder i) (mappingCylinderTarget i) := by
  rw [mappingCylinderCylinder_eq, mappingCylinderTarget_eq]
  exact IsPushout.of_hasPushout (mappingCylinderEndpoint X 1) i

private def middleRegionToCylinderRegion
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H)
    (O : TopologicalSpace.Opens (doubleMappingCylinder i f)) :
    doubleMappingCylinderMiddleRegion i f O ⟶ cylinderRegion i f O :=
  subspaceMap (mappingCylinderCylinder i) (fun _ h => h)

private def cylinderRegionToOpen
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H)
    (O : TopologicalSpace.Opens (doubleMappingCylinder i f)) :
    cylinderRegion i f O ⟶ TopCat.of (O : Set (doubleMappingCylinder i f)) :=
  subspaceMap (doubleMappingCylinderCylinderMap i f) (fun _ h => h)

private theorem cylinderRegionToOpen_isIso
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H)
    (O : TopologicalSpace.Opens (doubleMappingCylinder i f))
    (hH : ∀ h : H, doubleMappingCylinderH i f h ∉ O) :
    IsIso (cylinderRegionToOpen i f O) := by
  let sq := (doubleMappingCylinder_named_isPushout i f).flip
  have hr : (doubleMappingCylinderH i f) ⁻¹' (O : Set (doubleMappingCylinder i f)) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    exact hH
  have hl : (doubleMappingCylinderCylinderMap i f) ⁻¹' (O : Set (doubleMappingCylinder i f)) ⊆
      (Set.range (mappingCylinderSource i))ᶜ := by
    intro z hz hRange
    obtain ⟨x, rfl⟩ := hRange
    have he : doubleMappingCylinderCylinderMap i f (mappingCylinderSource i x) =
        doubleMappingCylinderH i f (f x) :=
      ConcreteCategory.congr_hom (doubleMappingCylinder_named_isPushout i f).w x
    exact hH (f x) (he ▸ hz)
  have hh := isHomeomorph_restrictPreimage_inr_of_isPushout sq O.isOpen hr hl
  have hm : IsHomeomorph (cylinderRegionToOpen i f O).hom := by
    unfold cylinderRegionToOpen
    exact hh
  exact (TopCat.isIso_iff_isHomeomorph (cylinderRegionToOpen i f O)).mpr hm

private theorem middleRegionToCylinderRegion_isIso
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H)
    (O : TopologicalSpace.Opens (doubleMappingCylinder i f))
    (hB : ∀ b : B, doubleMappingCylinderB i f b ∉ O) :
    IsIso (middleRegionToCylinderRegion i f O) := by
  let S : Set (mappingCylinder i) := (doubleMappingCylinderCylinderMap i f) ⁻¹'
      (O : Set (doubleMappingCylinder i f))
  let sq := (mappingCylinder_named_isPushout i).flip
  have hS : IsOpen S := O.isOpen.preimage (doubleMappingCylinderCylinderMap i f).hom.continuous
  have hr : (mappingCylinderTarget i) ⁻¹' S = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro b hb
    change doubleMappingCylinderCylinderMap i f (mappingCylinderTarget i b) ∈ O at hb
    exact hB b ((doubleMappingCylinderB_apply i f b).symm ▸ hb)
  have hl : (mappingCylinderCylinder i) ⁻¹' S ⊆
      (Set.range (mappingCylinderEndpoint X 1))ᶜ := by
    intro p hp hRange
    obtain ⟨x, rfl⟩ := hRange
    have hc : doubleMappingCylinderCylinderMap i f
        (mappingCylinderCylinder i (mappingCylinderEndpoint X 1 x)) =
        doubleMappingCylinderB i f (i x) :=
      (congrArg (doubleMappingCylinderCylinderMap i f).hom
        (ConcreteCategory.congr_hom (mappingCylinder_end_square i) x)).trans
          (doubleMappingCylinderB_apply i f (i x)).symm
    exact hB (i x) (hc ▸ hp)
  have hh := isHomeomorph_restrictPreimage_inr_of_isPushout sq hS hr hl
  have hm : IsHomeomorph (middleRegionToCylinderRegion i f O).hom := by
    unfold middleRegionToCylinderRegion
    exact hh
  exact (TopCat.isIso_iff_isHomeomorph (middleRegionToCylinderRegion i f O)).mpr hm

/-- The original middle is the actual open subspace away from both
endpoints. Its hom is the SAME original middle restriction. -/
public def doubleMappingCylinderMiddleRegionIso
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H)
    (O : TopologicalSpace.Opens (doubleMappingCylinder i f))
    (hH : ∀ h : H, doubleMappingCylinderH i f h ∉ O)
    (hB : ∀ b : B, doubleMappingCylinderB i f b ∉ O) :
    doubleMappingCylinderMiddleRegion i f O ≅ TopCat.of (O : Set (doubleMappingCylinder i f)) :=
  @asIso _ _ _ _ (middleRegionToCylinderRegion i f O)
      (middleRegionToCylinderRegion_isIso i f O hB) ≪≫
    @asIso _ _ _ _ (cylinderRegionToOpen i f O) (cylinderRegionToOpen_isIso i f O hH)

public theorem doubleMappingCylinderMiddleRegionIso_hom_apply
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H)
    (O : TopologicalSpace.Opens (doubleMappingCylinder i f))
    (hH : ∀ h : H, doubleMappingCylinderH i f h ∉ O)
    (hB : ∀ b : B, doubleMappingCylinderB i f b ∉ O)
    (p : doubleMappingCylinderMiddleRegion i f O) :
    (doubleMappingCylinderMiddleRegionIso i f O hH hB).hom p =
      ⟨doubleMappingCylinderMiddle i f p.1,
          (doubleMappingCylinderMiddle_apply i f p.1).symm ▸ p.2⟩ := by
  apply Subtype.ext
  exact (doubleMappingCylinderMiddle_apply i f p.1).symm

@[reassoc]
public theorem doubleMappingCylinderMiddleRegionIso_hom_inclusion
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H)
    (O : TopologicalSpace.Opens (doubleMappingCylinder i f))
    (hH : ∀ h : H, doubleMappingCylinderH i f h ∉ O)
    (hB : ∀ b : B, doubleMappingCylinderB i f b ∉ O) :
    (doubleMappingCylinderMiddleRegionIso i f O hH hB).hom ≫
        subspaceIncl (O : Set (doubleMappingCylinder i f)) =
      subspaceIncl {p : mappingCylinderDomain X |
        doubleMappingCylinderCylinderMap i f (mappingCylinderCylinder i p) ∈ O} ≫
          doubleMappingCylinderMiddle i f := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  exact congrArg Subtype.val (doubleMappingCylinderMiddleRegionIso_hom_apply i f O hH hB p)

/-- The actual overlap of the two original open collar subsets. -/
public abbrev doubleMappingCylinderOverlap
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    TopologicalSpace.Opens (doubleMappingCylinder i f) :=
  doubleMappingCylinderOpenH i f ⊓ doubleMappingCylinderOpenB i f

public theorem mem_doubleMappingCylinderOverlap
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) (d : doubleMappingCylinder i f) :
    d ∈ doubleMappingCylinderOverlap i f ↔
      1 / 3 < doubleMappingCylinderHeight i f d ∧ doubleMappingCylinderHeight i f d < 2 / 3 := by
  change (d ∈ doubleMappingCylinderOpenH i f ∧ d ∈ doubleMappingCylinderOpenB i f) ↔ _
  rw [mem_doubleMappingCylinderOpenH, mem_doubleMappingCylinderOpenB]
  exact and_comm

private theorem overlap_avoids_H
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) (h : H) :
    doubleMappingCylinderH i f h ∉ doubleMappingCylinderOverlap i f := by
  intro hh
  have ht := (mem_doubleMappingCylinderOverlap i f _).mp hh
  rw [doubleMappingCylinderHeight_H] at ht
  norm_num at ht

private theorem overlap_avoids_B
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) (b : B) :
    doubleMappingCylinderB i f b ∉ doubleMappingCylinderOverlap i f := by
  intro hb
  have ht := (mem_doubleMappingCylinderOverlap i f _).mp hb
  rw [doubleMappingCylinderHeight_B] at ht
  norm_num at ht

/-- The actual overlap chart is computed with endpoint avoidance derived
from height; no caller homeomorphism or comparison is required. -/
public def doubleMappingCylinderOverlapIso
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    doubleMappingCylinderMiddleRegion i f (doubleMappingCylinderOverlap i f) ≅
      TopCat.of (doubleMappingCylinderOverlap i f : Set (doubleMappingCylinder i f)) :=
  doubleMappingCylinderMiddleRegionIso i f (doubleMappingCylinderOverlap i f)
    (overlap_avoids_H i f) (overlap_avoids_B i f)

/-- Specialized actual overlap computation, retaining the original middle
and the actual open subspace carrier. -/
public theorem doubleMappingCylinderOverlapIso_hom_apply
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H)
    (p : doubleMappingCylinderMiddleRegion i f (doubleMappingCylinderOverlap i f)) :
    (doubleMappingCylinderOverlapIso i f).hom p =
      ⟨doubleMappingCylinderMiddle i f p.1,
          (doubleMappingCylinderMiddle_apply i f p.1).symm ▸ p.2⟩ :=
  doubleMappingCylinderMiddleRegionIso_hom_apply i f (doubleMappingCylinderOverlap i f)
    (overlap_avoids_H i f) (overlap_avoids_B i f) p

@[reassoc]
public theorem doubleMappingCylinderOverlapIso_hom_inclusion
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    (doubleMappingCylinderOverlapIso i f).hom ≫
        subspaceIncl (doubleMappingCylinderOverlap i f : Set (doubleMappingCylinder i f)) =
      subspaceIncl {p : mappingCylinderDomain X |
        doubleMappingCylinderCylinderMap i f (mappingCylinderCylinder i p) ∈
          doubleMappingCylinderOverlap i f} ≫ doubleMappingCylinderMiddle i f :=
  doubleMappingCylinderMiddleRegionIso_hom_inclusion i f (doubleMappingCylinderOverlap i f)
    (overlap_avoids_H i f) (overlap_avoids_B i f)

private def midpointTime : TopCat.I.{u} :=
  (TopCat.I.homeomorph.{u}).symm (⟨(1 / 2 : ℝ), by norm_num⟩ : unitInterval)

private theorem midpoint_in_overlap
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) (x : X) :
    doubleMappingCylinderCylinderMap i f (mappingCylinderCylinder i (x, midpointTime)) ∈
      doubleMappingCylinderOverlap i f := by
  apply (mem_doubleMappingCylinderOverlap i f _).mpr
  rw [← doubleMappingCylinderMiddle_apply, doubleMappingCylinderHeight_middle,
    midpointTime, (TopCat.I.homeomorph.{u}).apply_symm_apply]
  norm_num

private def midpointRegion
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    X ⟶ doubleMappingCylinderMiddleRegion i f (doubleMappingCylinderOverlap i f) :=
  TopCat.ofHom ⟨fun x => ⟨(x, midpointTime), midpoint_in_overlap i f x⟩,
    (continuous_id.prodMk continuous_const).subtype_mk _⟩

private theorem midpointRegion_inclusion
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    midpointRegion i f ≫ subspaceIncl {p : mappingCylinderDomain X |
      doubleMappingCylinderCylinderMap i f (mappingCylinderCylinder i p) ∈
        doubleMappingCylinderOverlap i f} = mappingCylinderEndpoint X midpointTime := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  have hL : (midpointRegion i f ≫ subspaceIncl {p : mappingCylinderDomain X |
      doubleMappingCylinderCylinderMap i f (mappingCylinderCylinder i p) ∈
        doubleMappingCylinderOverlap i f}).hom x = (x, midpointTime) := by
    rw [TopCat.hom_comp]
    unfold midpointRegion
    rfl
  exact hL.trans (mappingCylinderEndpoint_apply X midpointTime x).symm

private def middleRegionFirst
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H)
    (O : TopologicalSpace.Opens (doubleMappingCylinder i f)) :
    doubleMappingCylinderMiddleRegion i f O ⟶ X :=
  TopCat.ofHom ⟨fun p => p.1.1, continuous_fst.comp continuous_subtype_val⟩

/-- The midpoint o₀(x) in the actual original overlap. -/
public def doubleMappingCylinderMidpoint
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    X ⟶ TopCat.of (doubleMappingCylinderOverlap i f : Set (doubleMappingCylinder i f)) :=
  midpointRegion i f ≫ (doubleMappingCylinderOverlapIso i f).hom

/-- The actual overlap's original X-coordinate, through its computed
middle homeomorphism. -/
public def doubleMappingCylinderOverlapProjection
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    TopCat.of (doubleMappingCylinderOverlap i f : Set (doubleMappingCylinder i f)) ⟶ X :=
  (doubleMappingCylinderOverlapIso i f).inv ≫
    middleRegionFirst i f (doubleMappingCylinderOverlap i f)

public theorem doubleMappingCylinderOverlapProjection_middle
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H)
    (p : doubleMappingCylinderMiddleRegion i f (doubleMappingCylinderOverlap i f)) :
    doubleMappingCylinderOverlapProjection i f ((doubleMappingCylinderOverlapIso i f).hom p) =
      p.1.1 := by
  have he := ConcreteCategory.congr_hom (doubleMappingCylinderOverlapIso i f).hom_inv_id p
  change ((doubleMappingCylinderOverlapIso i f).inv
    ((doubleMappingCylinderOverlapIso i f).hom p)).1.1 = p.1.1
  exact congrArg (fun z => z.1.1) he

@[reassoc]
public theorem doubleMappingCylinderMidpoint_projection
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    doubleMappingCylinderMidpoint i f ≫ doubleMappingCylinderOverlapProjection i f = 𝟙 X := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact doubleMappingCylinderOverlapProjection_middle i f ((midpointRegion i f).hom x)

/-- The actual midpoint is the original middle map at height one half.
This is a computed full inclusion characteristic, not a supplied chart. -/
@[reassoc]
public theorem doubleMappingCylinderMidpoint_inclusion
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    doubleMappingCylinderMidpoint i f ≫
        subspaceIncl (doubleMappingCylinderOverlap i f : Set (doubleMappingCylinder i f)) =
      mappingCylinderEndpoint X
        ((TopCat.I.homeomorph.{u}).symm (⟨(1 / 2 : ℝ), by norm_num⟩ : unitInterval)) ≫
          doubleMappingCylinderMiddle i f := by
  unfold doubleMappingCylinderMidpoint
  rw [Category.assoc, doubleMappingCylinderOverlapIso_hom_inclusion,
    ← Category.assoc, midpointRegion_inclusion]
  rfl

/-- The whole original H image is outside the B-side open collar. -/
public theorem doubleMappingCylinderH_disjoint_openB
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) (h : H) :
    doubleMappingCylinderH i f h ∉ doubleMappingCylinderOpenB i f := by
  rw [mem_doubleMappingCylinderOpenB, doubleMappingCylinderHeight_H]
  norm_num

private theorem openH_avoids_B
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) (b : B) :
    doubleMappingCylinderB i f b ∉ doubleMappingCylinderOpenH i f := by
  rw [mem_doubleMappingCylinderOpenH, doubleMappingCylinderHeight_B]
  norm_num

private theorem H_mem_openH
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) (h : H) :
    doubleMappingCylinderH i f h ∈ doubleMappingCylinderOpenH i f := by
  rw [mem_doubleMappingCylinderOpenH, doubleMappingCylinderHeight_H]
  norm_num

private theorem B_mem_openB
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) (b : B) :
    doubleMappingCylinderB i f b ∈ doubleMappingCylinderOpenB i f := by
  rw [mem_doubleMappingCylinderOpenB, doubleMappingCylinderHeight_B]
  norm_num

private def HRestrictedPushout
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) : RestrictedPushout.{u} :=
  RestrictedPushout.of (doubleMappingCylinder_named_isPushout i f)
    (doubleMappingCylinderOpenH i f : Set (doubleMappingCylinder i f))

private def HCylinderIso
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    doubleMappingCylinderMiddleRegion i f (doubleMappingCylinderOpenH i f) ≅
      (HRestrictedPushout i f).obj₂ :=
  @asIso _ _ _ _ (middleRegionToCylinderRegion i f (doubleMappingCylinderOpenH i f))
    (middleRegionToCylinderRegion_isIso i f (doubleMappingCylinderOpenH i f) (openH_avoids_B i f))

private def HCylinderToH
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) : (HRestrictedPushout i f).obj₂ ⟶ H :=
  (HCylinderIso i f).inv ≫ middleRegionFirst i f (doubleMappingCylinderOpenH i f) ≫ f

private def HPreimageToH
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) : (HRestrictedPushout i f).obj₃ ⟶ H :=
  subspaceIncl ((doubleMappingCylinderH i f) ⁻¹'
      (doubleMappingCylinderOpenH i f : Set (doubleMappingCylinder i f)))

private theorem cylinder_zero_mem_openH
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) (x : X) :
    doubleMappingCylinderCylinderMap i f (mappingCylinderCylinder i (x, (0 : TopCat.I.{u}))) ∈
      doubleMappingCylinderOpenH i f := by
  rw [← doubleMappingCylinderMiddle_apply, mem_doubleMappingCylinderOpenH,
    doubleMappingCylinderHeight_middle, TopCat.I.homeomorph_zero]
  norm_num

private theorem HRetraction_square
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    (HRestrictedPushout i f).tU ≫ HCylinderToH i f =
      (HRestrictedPushout i f).lU ≫ HPreimageToH i f := by
  let P := HRestrictedPushout i f
  let e := HCylinderIso i f
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  let p : doubleMappingCylinderMiddleRegion i f (doubleMappingCylinderOpenH i f) :=
    ⟨(x.1, (0 : TopCat.I.{u})), cylinder_zero_mem_openH i f x.1⟩
  have hp : e.hom p = P.tU x := by
    apply Subtype.ext
    exact (mappingCylinderSource_apply i x.1).symm
  have he : e.inv (P.tU x) = p := by
    rw [← hp]
    exact ConcreteCategory.congr_hom e.hom_inv_id p
  change f ((e.inv (P.tU x)).1.1) = f x.1
  rw [he]

/-- Retraction from the ACTUAL H-side open collar to its original H.
It is descended from the actual restricted pushout, not given as data. -/
public def doubleMappingCylinderOpenHRetraction
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    TopCat.of (doubleMappingCylinderOpenH i f : Set (doubleMappingCylinder i f)) ⟶ H :=
  ((HRestrictedPushout i f).isPushout (doubleMappingCylinderOpenH i f).isOpen).desc
    (HCylinderToH i f) (HPreimageToH i f) (HRetraction_square i f)

/-- The original H inclusion into the H-side open collar. -/
public def doubleMappingCylinderHToOpenH
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    H ⟶ TopCat.of (doubleMappingCylinderOpenH i f : Set (doubleMappingCylinder i f)) :=
  TopCat.ofHom ⟨fun h => ⟨doubleMappingCylinderH i f h, H_mem_openH i f h⟩,
    (doubleMappingCylinderH i f).hom.continuous.subtype_mk _⟩

@[reassoc]
public theorem doubleMappingCylinderHToOpenH_inclusion
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    doubleMappingCylinderHToOpenH i f ≫
        subspaceIncl (doubleMappingCylinderOpenH i f : Set (doubleMappingCylinder i f)) =
      doubleMappingCylinderH i f := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro h
  rfl

@[reassoc]
public theorem doubleMappingCylinderHToOpenH_retraction
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    doubleMappingCylinderHToOpenH i f ≫ doubleMappingCylinderOpenHRetraction i f = 𝟙 H := by
  let P := HRestrictedPushout i f
  let sq := P.isPushout (doubleMappingCylinderOpenH i f).isOpen
  have hfac := sq.inr_desc (HCylinderToH i f) (HPreimageToH i f) (HRetraction_square i f)
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro h
  let p : P.obj₃ := ⟨h, H_mem_openH i f h⟩
  have hp : P.bU p = doubleMappingCylinderHToOpenH i f h := by
    apply Subtype.ext
    rfl
  change doubleMappingCylinderOpenHRetraction i f (doubleMappingCylinderHToOpenH i f h) = h
  exact (congrArg (doubleMappingCylinderOpenHRetraction i f).hom hp.symm).trans
    (ConcreteCategory.congr_hom hfac p)

public theorem doubleMappingCylinderOpenHRetraction_middle
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H)
    (p : doubleMappingCylinderMiddleRegion i f (doubleMappingCylinderOpenH i f)) :
    doubleMappingCylinderOpenHRetraction i f
        ⟨doubleMappingCylinderMiddle i f p.1,
            (doubleMappingCylinderMiddle_apply i f p.1).symm ▸ p.2⟩ =
      f p.1.1 := by
  let P := HRestrictedPushout i f
  let e := HCylinderIso i f
  let sq := P.isPushout (doubleMappingCylinderOpenH i f).isOpen
  have hfac := sq.inl_desc (HCylinderToH i f) (HPreimageToH i f) (HRetraction_square i f)
  have hp : P.rU (e.hom p) =
      ⟨doubleMappingCylinderMiddle i f p.1,
          (doubleMappingCylinderMiddle_apply i f p.1).symm ▸ p.2⟩ := by
    apply Subtype.ext
    exact (doubleMappingCylinderMiddle_apply i f p.1).symm
  have he : HCylinderToH i f (e.hom p) = f p.1.1 := by
    change f ((e.inv (e.hom p)).1.1) = f p.1.1
    exact congrArg (fun z => f z.1.1) (ConcreteCategory.congr_hom e.hom_inv_id p)
  exact (congrArg (doubleMappingCylinderOpenHRetraction i f).hom hp.symm).trans
    ((ConcreteCategory.congr_hom hfac (e.hom p)).trans he)

private theorem actualTopCatComp_apply {A B C : TopCat.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (x : A) :
    (f ≫ g) x = g (f x) := by
  exact TopCat.comp_app f g x

/-- The actual H-collar retraction preserves the original pushout projection. -/
public theorem doubleMappingCylinderOpenHRetraction_projection
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    subspaceIncl (doubleMappingCylinderOpenH i f : Set (doubleMappingCylinder i f)) ≫
        doubleMappingCylinderProjection i f =
      doubleMappingCylinderOpenHRetraction i f ≫ pushout.inr i f := by
  let P := HRestrictedPushout i f
  let sq := P.isPushout (doubleMappingCylinderOpenH i f).isOpen
  apply sq.hom_ext
  · apply (cancel_epi (HCylinderIso i f).hom).mp
    apply TopCat.ext
    intro p
    let z : TopCat.of (doubleMappingCylinderOpenH i f : Set (doubleMappingCylinder i f)) :=
      ⟨doubleMappingCylinderMiddle i f p.val,
        (doubleMappingCylinderMiddle_apply i f p.val).symm ▸ p.property⟩
    have hz : P.rU ((HCylinderIso i f).hom p) = z := by
      apply Subtype.ext
      exact (doubleMappingCylinderMiddle_apply i f p.val).symm
    have hret := doubleMappingCylinderOpenHRetraction_middle i f p
    have hproj := ConcreteCategory.congr_hom (doubleMappingCylinderProjection_middle i f) p.val
    have hfirst : (mappingCylinderFirst X).hom p.val = p.val.1 := mappingCylinderFirst_apply X p.val
    simp only [TopCat.hom_comp, ContinuousMap.comp_apply] at hproj
    rw [hfirst] at hproj
    have hpush := ConcreteCategory.congr_hom (pushout.condition (f := i) (g := f)) p.val.1
    simp only [TopCat.hom_comp, ContinuousMap.comp_apply] at hpush
    have result : (doubleMappingCylinderProjection i f).hom z.val =
        (pushout.inr i f).hom ((doubleMappingCylinderOpenHRetraction i f).hom z) :=
      hproj.trans (hpush.trans (congrArg (pushout.inr i f).hom hret.symm))
    let c : doubleMappingCylinderMiddleRegion i f (doubleMappingCylinderOpenH i f) ⟶
        TopCat.of (doubleMappingCylinderOpenH i f : Set (doubleMappingCylinder i f)) :=
      (HCylinderIso i f).hom ≫ P.rU
    have hc : c p = z := hz
    let q : TopCat.of (doubleMappingCylinderOpenH i f : Set (doubleMappingCylinder i f)) ⟶ pushout i f :=
      subspaceIncl (doubleMappingCylinderOpenH i f : Set (doubleMappingCylinder i f)) ≫ doubleMappingCylinderProjection
        i f
    let v : TopCat.of (doubleMappingCylinderOpenH i f : Set (doubleMappingCylinder i f)) ⟶ pushout i f :=
      doubleMappingCylinderOpenHRetraction i f ≫ pushout.inr i f
    have hq : q z = v z := by
      simpa only [q, v, TopCat.hom_comp, ContinuousMap.comp_apply, subspaceIncl, TopCat.hom_ofHom, ContinuousMap.coe_mk]
        using result
    exact (actualTopCatComp_apply c q p).trans
      ((congrArg q hc).trans (hq.trans ((congrArg v hc).symm.trans (actualTopCatComp_apply c v p).symm)))
  · apply TopCat.ext
    intro x
    have hz : P.bU x = doubleMappingCylinderHToOpenH i f x.val := by
      apply Subtype.ext
      rfl
    have hret := ConcreteCategory.congr_hom (doubleMappingCylinderHToOpenH_retraction i f) x.val
    have hproj := ConcreteCategory.congr_hom (doubleMappingCylinderProjection_H i f) x.val
    simp only [TopCat.hom_comp, ContinuousMap.comp_apply] at hret hproj
    have result : (doubleMappingCylinderProjection i f).hom (doubleMappingCylinderH i f x.val) =
        (pushout.inr i f).hom ((doubleMappingCylinderOpenHRetraction i f).hom
          (doubleMappingCylinderHToOpenH i f x.val)) :=
      hproj.trans (congrArg (pushout.inr i f).hom hret.symm)
    let c : P.obj₃ ⟶ TopCat.of (doubleMappingCylinderOpenH i f : Set (doubleMappingCylinder i f)) := P.bU
    let q : TopCat.of (doubleMappingCylinderOpenH i f : Set (doubleMappingCylinder i f)) ⟶ pushout i f :=
      subspaceIncl (doubleMappingCylinderOpenH i f : Set (doubleMappingCylinder i f)) ≫ doubleMappingCylinderProjection
        i f
    let v : TopCat.of (doubleMappingCylinderOpenH i f : Set (doubleMappingCylinder i f)) ⟶ pushout i f :=
      doubleMappingCylinderOpenHRetraction i f ≫ pushout.inr i f
    have hv : q (doubleMappingCylinderHToOpenH i f x.val) = v (doubleMappingCylinderHToOpenH i f x.val) := by
      simpa only [q, v, TopCat.hom_comp, ContinuousMap.comp_apply,
        doubleMappingCylinderHToOpenH, subspaceIncl, TopCat.hom_ofHom, ContinuousMap.coe_mk] using result
    exact (actualTopCatComp_apply c q x).trans
      ((congrArg q hz).trans (hv.trans ((congrArg v hz).symm.trans (actualTopCatComp_apply c v x).symm)))

private theorem cylinderTarget_mem_openB
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) (b : B) :
    mappingCylinderTarget i b ∈ (doubleMappingCylinderCylinderMap i f) ⁻¹'
      (doubleMappingCylinderOpenB i f : Set (doubleMappingCylinder i f)) := by
  change doubleMappingCylinderCylinderMap i f (mappingCylinderTarget i b) ∈
    doubleMappingCylinderOpenB i f
  rw [← doubleMappingCylinderB_apply]
  exact B_mem_openB i f b

private def VCylinderIso
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    cylinderRegion i f (doubleMappingCylinderOpenB i f) ≅
      TopCat.of (doubleMappingCylinderOpenB i f : Set (doubleMappingCylinder i f)) :=
  @asIso _ _ _ _ (cylinderRegionToOpen i f (doubleMappingCylinderOpenB i f))
    (cylinderRegionToOpen_isIso i f (doubleMappingCylinderOpenB i f)
      (doubleMappingCylinderH_disjoint_openB i f))

/-- Retraction of the ACTUAL B-side open collar to its original B. -/
public def doubleMappingCylinderOpenBRetraction
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    TopCat.of (doubleMappingCylinderOpenB i f : Set (doubleMappingCylinder i f)) ⟶ B :=
  (VCylinderIso i f).inv ≫
    subspaceIncl ((doubleMappingCylinderCylinderMap i f) ⁻¹'
        (doubleMappingCylinderOpenB i f : Set (doubleMappingCylinder i f))) ≫
      mappingCylinderProjection i

/-- The original B inclusion into the B-side open collar. -/
public def doubleMappingCylinderBToOpenB
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    B ⟶ TopCat.of (doubleMappingCylinderOpenB i f : Set (doubleMappingCylinder i f)) :=
  TopCat.ofHom ⟨fun b => ⟨doubleMappingCylinderB i f b, B_mem_openB i f b⟩,
    (doubleMappingCylinderB i f).hom.continuous.subtype_mk _⟩

@[reassoc]
public theorem doubleMappingCylinderBToOpenB_inclusion
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    doubleMappingCylinderBToOpenB i f ≫
        subspaceIncl (doubleMappingCylinderOpenB i f : Set (doubleMappingCylinder i f)) =
      doubleMappingCylinderB i f := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro b
  rfl

@[reassoc]
public theorem doubleMappingCylinderBToOpenB_retraction
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    doubleMappingCylinderBToOpenB i f ≫ doubleMappingCylinderOpenBRetraction i f = 𝟙 B := by
  let e := VCylinderIso i f
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro b
  let p : cylinderRegion i f (doubleMappingCylinderOpenB i f) :=
    ⟨mappingCylinderTarget i b, cylinderTarget_mem_openB i f b⟩
  have hp : e.hom p = doubleMappingCylinderBToOpenB i f b := by
    apply Subtype.ext
    exact (doubleMappingCylinderB_apply i f b).symm
  have he : e.inv (doubleMappingCylinderBToOpenB i f b) = p := by
    rw [← hp]
    exact ConcreteCategory.congr_hom e.hom_inv_id p
  change mappingCylinderProjection i (e.inv (doubleMappingCylinderBToOpenB i f b)).1 = b
  rw [he]
  exact ConcreteCategory.congr_hom (mappingCylinderProjection_target i) b

public theorem doubleMappingCylinderOpenBRetraction_middle
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H)
    (p : doubleMappingCylinderMiddleRegion i f (doubleMappingCylinderOpenB i f)) :
    doubleMappingCylinderOpenBRetraction i f
        ⟨doubleMappingCylinderMiddle i f p.1,
            (doubleMappingCylinderMiddle_apply i f p.1).symm ▸ p.2⟩ =
      i p.1.1 := by
  let e := VCylinderIso i f
  let z : cylinderRegion i f (doubleMappingCylinderOpenB i f) :=
      ⟨mappingCylinderCylinder i p.1, p.2⟩
  have hp : e.hom z =
      ⟨doubleMappingCylinderMiddle i f p.1,
          (doubleMappingCylinderMiddle_apply i f p.1).symm ▸ p.2⟩ := by
    apply Subtype.ext
    exact (doubleMappingCylinderMiddle_apply i f p.1).symm
  have he : e.inv
      ⟨doubleMappingCylinderMiddle i f p.1,
          (doubleMappingCylinderMiddle_apply i f p.1).symm ▸ p.2⟩ = z := by
    rw [← hp]
    exact ConcreteCategory.congr_hom e.hom_inv_id z
  change mappingCylinderProjection i (e.inv _).1 = i p.1.1
  rw [he]
  exact mappingCylinderProjection_cylinder_apply i p.1.1 p.1.2

/-- The two actual inclusions of the overlap in its open collar sides. -/
public def doubleMappingCylinderOverlapToOpenH
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    TopCat.of (doubleMappingCylinderOverlap i f : Set (doubleMappingCylinder i f)) ⟶
      TopCat.of (doubleMappingCylinderOpenH i f : Set (doubleMappingCylinder i f)) :=
  subspaceInclOfSubset (show (doubleMappingCylinderOverlap i f : Set (doubleMappingCylinder i f)) ⊆
    (doubleMappingCylinderOpenH i f : Set (doubleMappingCylinder i f)) from inf_le_left)

/-- The inclusion of the collar overlap into the original open B chart. -/
public def doubleMappingCylinderOverlapToOpenB
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    TopCat.of (doubleMappingCylinderOverlap i f : Set (doubleMappingCylinder i f)) ⟶
      TopCat.of (doubleMappingCylinderOpenB i f : Set (doubleMappingCylinder i f)) :=
  subspaceInclOfSubset (show (doubleMappingCylinderOverlap i f : Set (doubleMappingCylinder i f)) ⊆
    (doubleMappingCylinderOpenB i f : Set (doubleMappingCylinder i f)) from inf_le_right)

@[reassoc]
public theorem doubleMappingCylinderOverlapToOpenH_inclusion
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    doubleMappingCylinderOverlapToOpenH i f ≫
        subspaceIncl (doubleMappingCylinderOpenH i f : Set (doubleMappingCylinder i f)) =
      subspaceIncl (doubleMappingCylinderOverlap i f : Set (doubleMappingCylinder i f)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro o
  rfl

@[reassoc]
public theorem doubleMappingCylinderOverlapToOpenB_inclusion
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    doubleMappingCylinderOverlapToOpenB i f ≫
        subspaceIncl (doubleMappingCylinderOpenB i f : Set (doubleMappingCylinder i f)) =
      subspaceIncl (doubleMappingCylinderOverlap i f : Set (doubleMappingCylinder i f)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro o
  rfl

@[reassoc]
public theorem doubleMappingCylinderOverlap_H_square
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    doubleMappingCylinderOverlapToOpenH i f ≫ doubleMappingCylinderOpenHRetraction i f =
      doubleMappingCylinderOverlapProjection i f ≫ f := by
  let e := doubleMappingCylinderOverlapIso i f
  apply (cancel_epi e.hom).mp
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  let pH : doubleMappingCylinderMiddleRegion i f (doubleMappingCylinderOpenH i f) :=
    ⟨p.1, p.2.1⟩
  have hPoint : doubleMappingCylinderOverlapToOpenH i f (e.hom p) =
      ⟨doubleMappingCylinderMiddle i f pH.1,
        (doubleMappingCylinderMiddle_apply i f pH.1).symm ▸ pH.2⟩ := by
    apply Subtype.ext
    have hVal : (e.hom p).1 = doubleMappingCylinderMiddle i f p.1 :=
      congrArg (fun z : (doubleMappingCylinderOverlap i f : Set (doubleMappingCylinder i f)) => z.1)
        (doubleMappingCylinderOverlapIso_hom_apply i f p)
    have hIncl : (doubleMappingCylinderOverlapToOpenH i f (e.hom p)).1 = (e.hom p).1 := by
      unfold doubleMappingCylinderOverlapToOpenH
      rfl
    exact hIncl.trans hVal
  change doubleMappingCylinderOpenHRetraction i f
      (doubleMappingCylinderOverlapToOpenH i f (e.hom p)) =
    f (doubleMappingCylinderOverlapProjection i f (e.hom p))
  rw [hPoint, doubleMappingCylinderOpenHRetraction_middle,
    doubleMappingCylinderOverlapProjection_middle]

@[reassoc]
public theorem doubleMappingCylinderOverlap_B_square
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    doubleMappingCylinderOverlapToOpenB i f ≫ doubleMappingCylinderOpenBRetraction i f =
      doubleMappingCylinderOverlapProjection i f ≫ i := by
  let e := doubleMappingCylinderOverlapIso i f
  apply (cancel_epi e.hom).mp
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  let pB : doubleMappingCylinderMiddleRegion i f (doubleMappingCylinderOpenB i f) :=
    ⟨p.1, p.2.2⟩
  have hPoint : doubleMappingCylinderOverlapToOpenB i f (e.hom p) =
      ⟨doubleMappingCylinderMiddle i f pB.1,
        (doubleMappingCylinderMiddle_apply i f pB.1).symm ▸ pB.2⟩ := by
    apply Subtype.ext
    have hVal : (e.hom p).1 = doubleMappingCylinderMiddle i f p.1 :=
      congrArg (fun z : (doubleMappingCylinderOverlap i f : Set (doubleMappingCylinder i f)) => z.1)
        (doubleMappingCylinderOverlapIso_hom_apply i f p)
    have hIncl : (doubleMappingCylinderOverlapToOpenB i f (e.hom p)).1 = (e.hom p).1 := by
      unfold doubleMappingCylinderOverlapToOpenB
      rfl
    exact hIncl.trans hVal
  change doubleMappingCylinderOpenBRetraction i f
      (doubleMappingCylinderOverlapToOpenB i f (e.hom p)) =
    i (doubleMappingCylinderOverlapProjection i f (e.hom p))
  rw [hPoint, doubleMappingCylinderOpenBRetraction_middle,
    doubleMappingCylinderOverlapProjection_middle]

private theorem HCylinderIso_inv_tU
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) (x : (HRestrictedPushout i f).obj₁) :
    (HCylinderIso i f).inv ((HRestrictedPushout i f).tU x) =
      ⟨(x.1, (0 : TopCat.I.{u})), cylinder_zero_mem_openH i f x.1⟩ := by
  let e := HCylinderIso i f
  let p : doubleMappingCylinderMiddleRegion i f (doubleMappingCylinderOpenH i f) :=
    ⟨(x.1, (0 : TopCat.I.{u})), cylinder_zero_mem_openH i f x.1⟩
  have hp : e.hom p = (HRestrictedPushout i f).tU x := by
    apply Subtype.ext
    exact (mappingCylinderSource_apply i x.1).symm
  rw [← hp]
  exact ConcreteCategory.congr_hom e.hom_inv_id p

private theorem HRegion_height
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H)
    (p : doubleMappingCylinderMiddleRegion i f (doubleMappingCylinderOpenH i f)) :
    (TopCat.I.homeomorph p.1.2 : ℝ) < 2 / 3 := by
  have h := (mem_doubleMappingCylinderOpenH i f _).mp p.2
  rw [← doubleMappingCylinderMiddle_apply, doubleMappingCylinderHeight_middle] at h
  exact h

private def contractHRegion
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) (s : unitInterval)
    (p : doubleMappingCylinderMiddleRegion i f (doubleMappingCylinderOpenH i f)) :
    doubleMappingCylinderMiddleRegion i f (doubleMappingCylinderOpenH i f) :=
  ⟨(p.1.1, mappingCylinderInterpolate (0 : TopCat.I.{u}) s p.1.2), by
    apply (mem_doubleMappingCylinderOpenH i f _).mpr
    rw [← doubleMappingCylinderMiddle_apply, doubleMappingCylinderHeight_middle,
      mappingCylinderInterpolate_height, TopCat.I.homeomorph_zero]
    have h := HRegion_height i f p
    have hm := mul_nonneg s.2.1 (TopCat.I.homeomorph p.1.2).2.1
    change (1 - (s : ℝ)) * (TopCat.I.homeomorph p.1.2 : ℝ) + (s : ℝ) * (0 : ℝ) < 2 / 3
    nlinarith⟩

private theorem continuous_contractHRegion
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    Continuous (fun z : unitInterval ×
      doubleMappingCylinderMiddleRegion i f (doubleMappingCylinderOpenH i f) =>
      contractHRegion i f z.1 z.2) := by
  exact ((continuous_fst.comp (continuous_subtype_val.comp continuous_snd)).prodMk
    ((continuous_mappingCylinderInterpolate (0 : TopCat.I.{u})).comp
      (continuous_fst.prodMk
        (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))))).subtype_mk _

private theorem contractHRegion_zero
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H)
    (p : doubleMappingCylinderMiddleRegion i f (doubleMappingCylinderOpenH i f)) :
    contractHRegion i f 0 p = p := by
  apply Subtype.ext
  exact congrArg (Prod.mk p.1.1) (mappingCylinderInterpolate_zero (0 : TopCat.I.{u}) p.1.2)

private theorem contractHRegion_one_val
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H)
    (p : doubleMappingCylinderMiddleRegion i f (doubleMappingCylinderOpenH i f)) :
    (contractHRegion i f 1 p).1 = (p.1.1, (0 : TopCat.I.{u})) :=
  congrArg (Prod.mk p.1.1) (mappingCylinderInterpolate_one (0 : TopCat.I.{u}) p.1.2)

private theorem doubleMiddle_zero_apply
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) (x : X) :
    doubleMappingCylinderMiddle i f (x, (0 : TopCat.I.{u})) =
      doubleMappingCylinderH i f (f x) := by
  have hL : (mappingCylinderEndpoint X 0 ≫ doubleMappingCylinderMiddle i f).hom x =
      doubleMappingCylinderMiddle i f (mappingCylinderEndpoint X 0 x) :=
    congrArg (fun k : C(X, doubleMappingCylinder i f) => k x)
      (TopCat.hom_comp (mappingCylinderEndpoint X 0) (doubleMappingCylinderMiddle i f))
  have hR : (f ≫ doubleMappingCylinderH i f).hom x = doubleMappingCylinderH i f (f x) :=
    congrArg (fun k : C(X, doubleMappingCylinder i f) => k x)
      (TopCat.hom_comp f (doubleMappingCylinderH i f))
  have hs := congrArg (fun k : X ⟶ doubleMappingCylinder i f => k.hom x)
    (doubleMappingCylinder_zero i f)
  exact (congrArg (fun p : mappingCylinderDomain X => doubleMappingCylinderMiddle i f p)
    (mappingCylinderEndpoint_apply X 0 x)).symm.trans (hL.symm.trans (hs.trans hR))

private def HSideCylinderHomotopy
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    TopCat.Homotopy (HRestrictedPushout i f).rU
      (HCylinderToH i f ≫ doubleMappingCylinderHToOpenH i f) where
  toFun z := (HRestrictedPushout i f).rU
    ((HCylinderIso i f).hom (contractHRegion i f z.1 ((HCylinderIso i f).inv z.2)))
  continuous_toFun := (HRestrictedPushout i f).rU.hom.continuous.comp
    ((HCylinderIso i f).hom.hom.continuous.comp
      ((continuous_contractHRegion i f).comp
        (continuous_fst.prodMk ((HCylinderIso i f).inv.hom.continuous.comp continuous_snd))))
  map_zero_left z := by
    rw [contractHRegion_zero]
    exact congrArg (HRestrictedPushout i f).rU.hom
      (ConcreteCategory.congr_hom (HCylinderIso i f).inv_hom_id z)
  map_one_left z := by
    apply Subtype.ext
    let p := (HCylinderIso i f).inv z
    change doubleMappingCylinderCylinderMap i f
      (mappingCylinderCylinder i (contractHRegion i f 1 p).1) =
        doubleMappingCylinderH i f (f p.1.1)
    rw [contractHRegion_one_val]
    exact ((doubleMappingCylinderMiddle_apply i f (p.1.1, (0 : TopCat.I.{u}))).symm).trans
      (doubleMiddle_zero_apply i f p.1.1)

private theorem HPreimage_inclusion_eq
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    (HRestrictedPushout i f).bU = HPreimageToH i f ≫ doubleMappingCylinderHToOpenH i f := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro h
  apply Subtype.ext
  rfl

private def HSideOriginalHHomotopy
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    TopCat.Homotopy (HRestrictedPushout i f).bU
      (HPreimageToH i f ≫ doubleMappingCylinderHToOpenH i f) :=
  (TopCat.Homotopy.refl (HRestrictedPushout i f).bU).cast rfl
    (congrArg (fun k => k.hom) (HPreimage_inclusion_eq i f))

private theorem HSideHomotopy_compatible
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H)
    (s : unitInterval) (x : (HRestrictedPushout i f).obj₁) :
    HSideCylinderHomotopy i f (s, (HRestrictedPushout i f).tU x) =
      HSideOriginalHHomotopy i f (s, (HRestrictedPushout i f).lU x) := by
  let P := HRestrictedPushout i f
  let p : doubleMappingCylinderMiddleRegion i f (doubleMappingCylinderOpenH i f) :=
    ⟨(x.1, (0 : TopCat.I.{u})), cylinder_zero_mem_openH i f x.1⟩
  have hp : contractHRegion i f s p = p := by
    apply Subtype.ext
    exact congrArg (Prod.mk x.1) (mappingCylinderInterpolate_fixed (0 : TopCat.I.{u}) s)
  have he : (HCylinderIso i f).hom p = P.tU x := by
    apply Subtype.ext
    exact (mappingCylinderSource_apply i x.1).symm
  change P.rU ((HCylinderIso i f).hom
    (contractHRegion i f s ((HCylinderIso i f).inv (P.tU x)))) = _
  rw [HCylinderIso_inv_tU, hp, he]
  exact ConcreteCategory.congr_hom P.w x

/-- A genuine strong deformation of the original H-side open collar.
Every point of the whole original H image is fixed for every time. -/
public def doubleMappingCylinderOpenHHomotopy
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    ContinuousMap.HomotopyRel
        (𝟙
          (TopCat.of (doubleMappingCylinderOpenH i f : Set (doubleMappingCylinder i f))) : TopCat.of
          (doubleMappingCylinderOpenH i f : Set (doubleMappingCylinder i f)) ⟶
          TopCat.of (doubleMappingCylinderOpenH i f : Set (doubleMappingCylinder i f))).hom
      (doubleMappingCylinderOpenHRetraction i f ≫ doubleMappingCylinderHToOpenH i f).hom
      (Set.range (doubleMappingCylinderHToOpenH i f)) := by
  let P := HRestrictedPushout i f
  let sq := P.isPushout (doubleMappingCylinderOpenH i f).isOpen
  let HC := HSideCylinderHomotopy i f
  let HH := HSideOriginalHHomotopy i f
  have h₀ : P.tU ≫ P.rU = P.lU ≫ P.bU := P.w
  have h₁ : P.tU ≫ (HCylinderToH i f ≫ doubleMappingCylinderHToOpenH i f) =
      P.lU ≫ (HPreimageToH i f ≫ doubleMappingCylinderHToOpenH i f) := by
    rw [← Category.assoc, HRetraction_square, Category.assoc]
  let K := TopCat.Homotopy.descOfIsPushout sq HC HH h₀ h₁ (HSideHomotopy_compatible i f)
  let r : P.obj₄ ⟶ H :=
    sq.desc (HCylinderToH i f) (HPreimageToH i f) (HRetraction_square i f)
  have hrL : P.rU ≫ r = HCylinderToH i f := sq.inl_desc _ _ _
  have hrR : P.bU ≫ r = HPreimageToH i f := sq.inr_desc _ _ _
  have hk₀ : sq.desc P.rU P.bU h₀ = 𝟙 P.obj₄ := by
    apply sq.hom_ext
    · exact (sq.inl_desc _ _ _).trans (Category.comp_id P.rU).symm
    · exact (sq.inr_desc _ _ _).trans (Category.comp_id P.bU).symm
  have hk₁ : sq.desc (HCylinderToH i f ≫ doubleMappingCylinderHToOpenH i f)
      (HPreimageToH i f ≫ doubleMappingCylinderHToOpenH i f) h₁ =
      r ≫ doubleMappingCylinderHToOpenH i f := by
    apply sq.hom_ext
    · exact (sq.inl_desc _ _ _).trans
        ((congrArg (fun k : P.obj₂ ⟶ H => k ≫ doubleMappingCylinderHToOpenH i f) hrL).symm.trans
          (Category.assoc P.rU r (doubleMappingCylinderHToOpenH i f)))
    · exact (sq.inr_desc _ _ _).trans
        ((congrArg (fun k : P.obj₃ ⟶ H => k ≫ doubleMappingCylinderHToOpenH i f) hrR).symm.trans
          (Category.assoc P.bU r (doubleMappingCylinderHToOpenH i f)))
  let K' := K.cast (congrArg (fun k => k.hom) hk₀) (congrArg (fun k => k.hom) hk₁)
  refine { toHomotopy := K', prop' := ?_ }
  intro s z hz
  obtain ⟨h, rfl⟩ := hz
  let p : P.obj₃ := ⟨h, H_mem_openH i f h⟩
  have hp : P.bU p = doubleMappingCylinderHToOpenH i f h := by
    apply Subtype.ext
    rfl
  change K'.toFun (s, (doubleMappingCylinderHToOpenH i f h : P.obj₄)) =
    doubleMappingCylinderHToOpenH i f h
  have hCast : K'.toFun = K.toFun := rfl
  rw [hCast]
  have hVal : K.toFun (s, P.bU p) = P.bU p :=
    TopCat.Homotopy.descOfIsPushout_apply_inr sq HC HH h₀ h₁
      (HSideHomotopy_compatible i f) s p
  exact (congrArg (fun z : P.obj₄ => K.toFun (s, z)) hp.symm).trans (hVal.trans hp)

/-- The H-side retraction is weak, derived from the actual deformation
and its strict original-H retraction. H may have arbitrary components. -/
public theorem doubleMappingCylinderOpenHRetraction_mem_weakHomotopyEquivalences
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    TopCat.weakHomotopyEquivalences (doubleMappingCylinderOpenHRetraction i f) := by
  let r := doubleMappingCylinderOpenHRetraction i f
  let a := doubleMappingCylinderHToOpenH i f
  let HR : TopCat.Homotopy (a ≫ r) (𝟙 H) :=
    (TopCat.Homotopy.refl (𝟙 H)).cast
      (congrArg (fun k : H ⟶ H => k.hom) (doubleMappingCylinderHToOpenH_retraction i f).symm) rfl
  exact weakHomotopyEquivalences.of_homotopyInverse r a
    (doubleMappingCylinderOpenHHomotopy i f).symm.toHomotopy HR

private theorem naturalHomotopy_preserves_openB
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) (s : unitInterval)
    (z : mappingCylinder i)
    (hz : doubleMappingCylinderCylinderMap i f z ∈ doubleMappingCylinderOpenB i f) :
    doubleMappingCylinderCylinderMap i f (mappingCylinderNaturalHomotopy i (s, z)) ∈
      doubleMappingCylinderOpenB i f := by
  let sq := mappingCylinder_named_isPushout i
  obtain hp | hb := Types.eq_or_eq_of_isPushout (sq.map (forget TopCat)) z
  · obtain ⟨p, hp⟩ := hp
    change mappingCylinderCylinder i p = z at hp
    rw [← hp, mappingCylinderNaturalHomotopy_cylinder]
    apply (mem_doubleMappingCylinderOpenB i f _).mpr
    rw [← doubleMappingCylinderMiddle_apply, doubleMappingCylinderHeight_middle,
      mappingCylinderInterpolate_height, TopCat.I.homeomorph_one]
    have ht := (mem_doubleMappingCylinderOpenB i f _).mp (hp.symm ▸ hz)
    rw [← doubleMappingCylinderMiddle_apply, doubleMappingCylinderHeight_middle] at ht
    have hm := mul_nonneg s.2.1 (sub_nonneg.mpr (TopCat.I.homeomorph p.2).2.2)
    change 1 / 3 < (1 - (s : ℝ)) * (TopCat.I.homeomorph p.2 : ℝ) + (s : ℝ) * (1 : ℝ)
    nlinarith
  · obtain ⟨b, hb⟩ := hb
    change mappingCylinderTarget i b = z at hb
    rw [← hb, mappingCylinderNaturalHomotopy_target]
    exact cylinderTarget_mem_openB i f b

/-- The actual B-collar retraction preserves the original pushout projection. -/
public theorem doubleMappingCylinderOpenBRetraction_projection
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    subspaceIncl (doubleMappingCylinderOpenB i f : Set (doubleMappingCylinder i f)) ≫
        doubleMappingCylinderProjection i f =
      doubleMappingCylinderOpenBRetraction i f ≫ pushout.inl i f := by
  let e := VCylinderIso i f
  apply (cancel_epi e.hom).mp
  apply TopCat.ext
  intro p
  have he : e.inv (e.hom p) = p := ConcreteCategory.congr_hom e.hom_inv_id p
  have hproj := ConcreteCategory.congr_hom (doubleMappingCylinderProjection_cylinder i f) p.val
  simp only [TopCat.hom_comp, ContinuousMap.comp_apply] at hproj
  have hret : doubleMappingCylinderOpenBRetraction i f (e.hom p) = mappingCylinderProjection i p.val := by
    change mappingCylinderProjection i (e.inv (e.hom p)).val = _
    rw [he]
  have hval : (e.hom p).val = doubleMappingCylinderCylinderMap i f p.val := rfl
  let q : TopCat.of (doubleMappingCylinderOpenB i f : Set (doubleMappingCylinder i f)) ⟶ pushout i f :=
    subspaceIncl (doubleMappingCylinderOpenB i f : Set (doubleMappingCylinder i f)) ≫ doubleMappingCylinderProjection i
      f
  let v : TopCat.of (doubleMappingCylinderOpenB i f : Set (doubleMappingCylinder i f)) ⟶ pushout i f :=
    doubleMappingCylinderOpenBRetraction i f ≫ pushout.inl i f
  have result : q (e.hom p) = v (e.hom p) := by
    simpa only [q, v, TopCat.hom_comp, ContinuousMap.comp_apply, subspaceIncl,
      TopCat.hom_ofHom, ContinuousMap.coe_mk, hval, hret] using hproj
  exact (actualTopCatComp_apply e.hom q p).trans (result.trans (actualTopCatComp_apply e.hom v p).symm)

private theorem VCylinderIso_inv_B
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) (b : B) :
    (VCylinderIso i f).inv (doubleMappingCylinderBToOpenB i f b) =
      ⟨mappingCylinderTarget i b, cylinderTarget_mem_openB i f b⟩ := by
  let e := VCylinderIso i f
  let p : cylinderRegion i f (doubleMappingCylinderOpenB i f) :=
    ⟨mappingCylinderTarget i b, cylinderTarget_mem_openB i f b⟩
  have hp : e.hom p = doubleMappingCylinderBToOpenB i f b := by
    apply Subtype.ext
    exact (doubleMappingCylinderB_apply i f b).symm
  rw [← hp]
  exact ConcreteCategory.congr_hom e.hom_inv_id p

/-- The B-side open collar has an actual strong deformation to its
original B. It restricts the SAME original cylinder contraction and fixes
all B points, without assuming cofibrancy or connectedness of B/H. -/
public def doubleMappingCylinderOpenBHomotopy
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    ContinuousMap.HomotopyRel
        (𝟙
          (TopCat.of (doubleMappingCylinderOpenB i f : Set (doubleMappingCylinder i f))) : TopCat.of
          (doubleMappingCylinderOpenB i f : Set (doubleMappingCylinder i f)) ⟶
          TopCat.of (doubleMappingCylinderOpenB i f : Set (doubleMappingCylinder i f))).hom
      (doubleMappingCylinderOpenBRetraction i f ≫ doubleMappingCylinderBToOpenB i f).hom
      (Set.range (doubleMappingCylinderBToOpenB i f)) := by
  let e := VCylinderIso i f
  let K := mappingCylinderNaturalHomotopy i
  let KV :
      TopCat.Homotopy
      (𝟙 (TopCat.of (doubleMappingCylinderOpenB i f : Set (doubleMappingCylinder i f))))
      (doubleMappingCylinderOpenBRetraction i f ≫ doubleMappingCylinderBToOpenB i f) :=
    { toFun := fun z => e.hom
        ⟨K (z.1, (e.inv z.2).1),
            naturalHomotopy_preserves_openB i f z.1 (e.inv z.2).1 (e.inv z.2).2⟩
      continuous_toFun := e.hom.hom.continuous.comp
        ((K.continuous_toFun.comp
          (continuous_fst.prodMk (continuous_subtype_val.comp
            (e.inv.hom.continuous.comp continuous_snd)))).subtype_mk _)
      map_zero_left := by
        intro v
        let p : cylinderRegion i f (doubleMappingCylinderOpenB i f) :=
          ⟨K (0, (e.inv v).1), naturalHomotopy_preserves_openB i f 0 (e.inv v).1 (e.inv v).2⟩
        have hp : p = e.inv v := by
          apply Subtype.ext
          exact K.map_zero_left (e.inv v).1
        change e.hom p = v
        rw [hp]
        exact ConcreteCategory.congr_hom e.inv_hom_id v
      map_one_left := by
        intro v
        apply Subtype.ext
        change doubleMappingCylinderCylinderMap i f (K (1, (e.inv v).1)) =
          doubleMappingCylinderB i f (mappingCylinderProjection i (e.inv v).1)
        have hK := K.map_one_left (e.inv v).1
        have hEnd' : (mappingCylinderProjection i ≫ mappingCylinderTarget i).hom (e.inv v).1 =
            mappingCylinderTarget i (mappingCylinderProjection i (e.inv v).1) :=
          congrArg (fun k : C(mappingCylinder i, mappingCylinder i) => k (e.inv v).1)
            (TopCat.hom_comp (mappingCylinderProjection i) (mappingCylinderTarget i))
        exact (congrArg (fun z : mappingCylinder i => doubleMappingCylinderCylinderMap i f z)
          (hK.trans hEnd')).trans
            (doubleMappingCylinderB_apply i f (mappingCylinderProjection i (e.inv v).1)).symm }
  refine { toHomotopy := KV, prop' := ?_ }
  intro s v hv
  obtain ⟨b, rfl⟩ := hv
  let pS : cylinderRegion i f (doubleMappingCylinderOpenB i f) :=
    ⟨K (s, (e.inv (doubleMappingCylinderBToOpenB i f b)).1),
      naturalHomotopy_preserves_openB i f s
        (e.inv (doubleMappingCylinderBToOpenB i f b)).1
        (e.inv (doubleMappingCylinderBToOpenB i f b)).2⟩
  let pB : cylinderRegion i f (doubleMappingCylinderOpenB i f) :=
    ⟨mappingCylinderTarget i b, cylinderTarget_mem_openB i f b⟩
  have hCarrier : pS.1 = pB.1 :=
    (congrArg (fun z : cylinderRegion i f (doubleMappingCylinderOpenB i f) => K (s, z.1))
      (VCylinderIso_inv_B i f b)).trans (mappingCylinderNaturalHomotopy_target i s b)
  have hSame : pS = pB := Subtype.ext hCarrier
  have hTarget : e.hom pB = doubleMappingCylinderBToOpenB i f b := by
    apply Subtype.ext
    exact (doubleMappingCylinderB_apply i f b).symm
  change e.hom pS = doubleMappingCylinderBToOpenB i f b
  exact (congrArg (fun z : cylinderRegion i f (doubleMappingCylinderOpenB i f) => e.hom z)
    hSame).trans hTarget

/-- The actual B-side retraction is weak by its original deformation and
strict B retraction, with no extra model or weak-comparison premise. -/
public theorem doubleMappingCylinderOpenBRetraction_mem_weakHomotopyEquivalences
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    TopCat.weakHomotopyEquivalences (doubleMappingCylinderOpenBRetraction i f) := by
  let r := doubleMappingCylinderOpenBRetraction i f
  let a := doubleMappingCylinderBToOpenB i f
  let HR : TopCat.Homotopy (a ≫ r) (𝟙 B) :=
    (TopCat.Homotopy.refl (𝟙 B)).cast
      (congrArg (fun k : B ⟶ B => k.hom) (doubleMappingCylinderBToOpenB_retraction i f).symm) rfl
  exact weakHomotopyEquivalences.of_homotopyInverse r a
    (doubleMappingCylinderOpenBHomotopy i f).symm.toHomotopy HR

end TopCat

end
