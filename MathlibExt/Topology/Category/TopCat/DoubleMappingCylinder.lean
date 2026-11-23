/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.MappingCylinderCofibration
public import MathlibExt.Topology.Category.TopCat.WeakHomotopyEquivalenceHomotopy
public import Mathlib.Topology.Homotopy.Equiv

/-!
# One original double-mapping-cylinder comparison

For i:X→B and f:X→H the actual cylinder is pushed out along f. It carries
the original B, H and X×I maps and collapses to the actual pushout of i and f.
For a genuine cofibration i, the existing relative cylinder HEP gives a
computed inverse and both homotopies relative to the entire original H.

The actual height and its two overlapping open subsets are the collar used
by the coefficient and fundamental-group proofs. No pushout equivalence,
inverse, homotopy family, open-cover comparison or coefficient QI is input.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped TopCat.modelCategory

universe u

namespace TopCat

/-- The literal double mapping cylinder, retaining the original maps. -/
public abbrev doubleMappingCylinder {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    TopCat.{u} :=
  pushout (mappingCylinderSource i) f

/-- The original cylinder embeds through its pushout coprojection. -/
public def doubleMappingCylinderCylinderMap {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    mappingCylinder i ⟶ doubleMappingCylinder i f :=
  pushout.inl (mappingCylinderSource i) f

/-- The original H leg, with no connectedness condition on H. -/
public def doubleMappingCylinderH {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    H ⟶ doubleMappingCylinder i f :=
  pushout.inr (mappingCylinderSource i) f

/-- The original B leg at the other end of the same cylinder. -/
public def doubleMappingCylinderB {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    B ⟶ doubleMappingCylinder i f :=
  mappingCylinderTarget i ≫ doubleMappingCylinderCylinderMap i f

/-- The original X×I map, not a separately chosen collar chart. -/
public def doubleMappingCylinderMiddle {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    mappingCylinderDomain X ⟶ doubleMappingCylinder i f :=
  mappingCylinderCylinder i ≫ doubleMappingCylinderCylinderMap i f

/-- The middle chart retains both actual coprojections pointwise. -/
public theorem doubleMappingCylinderMiddle_apply
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) (p : mappingCylinderDomain X) :
    doubleMappingCylinderMiddle i f p =
      doubleMappingCylinderCylinderMap i f (mappingCylinderCylinder i p) := by
  unfold doubleMappingCylinderMiddle
  rw [TopCat.comp_app]

/-- The B leg retains both actual coprojections pointwise. -/
public theorem doubleMappingCylinderB_apply
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) (b : B) :
    doubleMappingCylinderB i f b =
      doubleMappingCylinderCylinderMap i f (mappingCylinderTarget i b) := by
  unfold doubleMappingCylinderB
  rw [TopCat.comp_app]

public theorem doubleMappingCylinderCylinderMap_eq
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    doubleMappingCylinderCylinderMap i f = pushout.inl (mappingCylinderSource i) f := by
  unfold doubleMappingCylinderCylinderMap
  rfl

public theorem doubleMappingCylinderH_eq
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    doubleMappingCylinderH i f = pushout.inr (mappingCylinderSource i) f := by
  unfold doubleMappingCylinderH
  rfl

private theorem mappingCylinderSource_eq_endpoint
    {X B : TopCat.{u}} (i : X ⟶ B) :
    mappingCylinderSource i = mappingCylinderEndpoint X 0 ≫ mappingCylinderCylinder i := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  rw [TopCat.comp_app, mappingCylinderEndpoint_apply]
  exact mappingCylinderSource_apply i x

@[reassoc]
public theorem doubleMappingCylinder_zero {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    mappingCylinderEndpoint X 0 ≫ doubleMappingCylinderMiddle i f =
      f ≫ doubleMappingCylinderH i f := by
  rw [doubleMappingCylinderMiddle, ← Category.assoc, ← mappingCylinderSource_eq_endpoint]
  exact pushout.condition (f := mappingCylinderSource i) (g := f)

@[reassoc]
public theorem doubleMappingCylinder_one {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    mappingCylinderEndpoint X 1 ≫ doubleMappingCylinderMiddle i f =
      i ≫ doubleMappingCylinderB i f := by
  rw [doubleMappingCylinderMiddle, ← Category.assoc, mappingCylinder_end_square,
    Category.assoc]
  rfl

/-- Collapse to the actual pushout W=pushout i f, with its original B/H legs. -/
public def doubleMappingCylinderProjection {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    doubleMappingCylinder i f ⟶ pushout i f :=
  pushout.desc (mappingCylinderProjection i ≫ pushout.inl i f) (pushout.inr i f) (by
    rw [← Category.assoc, mappingCylinderProjection_source]
    exact pushout.condition (f := i) (g := f))

@[reassoc]
public theorem doubleMappingCylinderProjection_cylinder
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    doubleMappingCylinderCylinderMap i f ≫ doubleMappingCylinderProjection i f =
      mappingCylinderProjection i ≫ pushout.inl i f :=
  pushout.inl_desc _ _ _

@[reassoc]
public theorem doubleMappingCylinderProjection_H
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    doubleMappingCylinderH i f ≫ doubleMappingCylinderProjection i f = pushout.inr i f :=
  pushout.inr_desc _ _ _

@[reassoc]
public theorem doubleMappingCylinderProjection_B
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    doubleMappingCylinderB i f ≫ doubleMappingCylinderProjection i f = pushout.inl i f := by
  rw [doubleMappingCylinderB, Category.assoc, doubleMappingCylinderProjection_cylinder,
    ← Category.assoc, mappingCylinderProjection_target, Category.id_comp]

@[reassoc]
public theorem doubleMappingCylinderProjection_middle
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    doubleMappingCylinderMiddle i f ≫ doubleMappingCylinderProjection i f =
      mappingCylinderFirst X ≫ i ≫ pushout.inl i f := by
  rw [doubleMappingCylinderMiddle, Category.assoc, doubleMappingCylinderProjection_cylinder,
    ← Category.assoc, mappingCylinderProjection_cylinder, Category.assoc]

/-- Actual relative comparison data. The inverse preserves H strictly and
BOTH inverse homotopies preserve every point of that whole original H leg. -/
public structure DoubleMappingCylinderPairEquivalence
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) where
  /-- The map from the ordinary pushout to the double cylinder preserving the whole H leg. -/
  inverse : pushout i f ⟶ doubleMappingCylinder i f
  inverse_H : pushout.inr i f ≫ inverse = doubleMappingCylinderH i f
  /-- The homotopy from the cylinder identity to projection followed by inverse,
  fixed on the original H image. -/
  cylinderHomotopy : ContinuousMap.HomotopyRel
    (𝟙 (doubleMappingCylinder i f) : doubleMappingCylinder i f ⟶
      doubleMappingCylinder i f).hom (doubleMappingCylinderProjection i f ≫ inverse).hom
    (Set.range (doubleMappingCylinderH i f))
  /-- The homotopy from the pushout identity to inverse followed by projection,
  fixed on the original H image. -/
  pushoutHomotopy : ContinuousMap.HomotopyRel
    (𝟙 (pushout i f) : pushout i f ⟶ pushout i f).hom
      (inverse ≫ doubleMappingCylinderProjection i f).hom
    (Set.range (pushout.inr i f))

private theorem nonempty_doubleMappingCylinderPairEquivalence
    {X B H : TopCat.{u}} (i : X ⟶ B) [Cofibration i] (f : X ⟶ H) :
    Nonempty (DoubleMappingCylinderPairEquivalence i f) := by
  let C := mappingCylinder i
  let D := doubleMappingCylinder i f
  let W := pushout i f
  let e := mappingCylinderPairEquivalence i
  let c := doubleMappingCylinderCylinderMap i f
  let h := doubleMappingCylinderH i f
  let q := doubleMappingCylinderProjection i f
  let a := pushout.inl i f
  let j := pushout.inr i f
  have hrSquare : i ≫ (e.inverse ≫ c) = f ≫ h := by
    rw [← Category.assoc, e.inverse_source]
    exact pushout.condition (f := mappingCylinderSource i) (g := f)
  let r : W ⟶ D := pushout.desc (e.inverse ≫ c) h hrSquare
  have hra : a ≫ r = e.inverse ≫ c := pushout.inl_desc _ _ _
  have hrj : j ≫ r = h := pushout.inr_desc _ _ _
  have hcq : c ≫ q = mappingCylinderProjection i ≫ a :=
    doubleMappingCylinderProjection_cylinder i f
  have hhq : h ≫ q = j := doubleMappingCylinderProjection_H i f
  let HC0 := (TopCat.Homotopy.refl c).comp e.cylinderHomotopy.toHomotopy
  let HC : TopCat.Homotopy c (mappingCylinderProjection i ≫ (e.inverse ≫ c)) :=
    HC0.cast
      ((TopCat.hom_comp (𝟙 C) c).symm.trans
        (congrArg (fun k : C ⟶ D => k.hom) (Category.id_comp c)))
      ((TopCat.hom_comp (mappingCylinderProjection i ≫ e.inverse) c).symm.trans
        (congrArg (fun k : C ⟶ D => k.hom)
          (Category.assoc (mappingCylinderProjection i) e.inverse c)))
  let HH : TopCat.Homotopy h h := TopCat.Homotopy.refl h
  have hc₀ : mappingCylinderSource i ≫ c = f ≫ h :=
    pushout.condition (f := mappingCylinderSource i) (g := f)
  have hc₁ : mappingCylinderSource i ≫
      (mappingCylinderProjection i ≫ (e.inverse ≫ c)) = f ≫ h := by
    rw [← Category.assoc, mappingCylinderProjection_source, ← Category.assoc,
      e.inverse_source]
    exact hc₀
  have hcCompatible (t : unitInterval) (x : X) :
      HC (t, mappingCylinderSource i x) = HH (t, f x) := by
    simp only [HC, HC0, ContinuousMap.Homotopy.cast_apply]
    change c (e.cylinderHomotopy (t, mappingCylinderSource i x)) = h (f x)
    exact (congrArg (fun z : C => c z) (e.cylinderHomotopy.eq_fst t ⟨x, rfl⟩)).trans
      (ConcreteCategory.congr_hom hc₀ x)
  let HD0 := TopCat.Homotopy.pushoutDesc HC HH hc₀ hc₁ hcCompatible
  have hd₀ : pushout.desc c h hc₀ = 𝟙 D := by
    apply pushout.hom_ext
    · rw [pushout.inl_desc, Category.comp_id]
      exact doubleMappingCylinderCylinderMap_eq i f
    · rw [pushout.inr_desc, Category.comp_id]
      exact doubleMappingCylinderH_eq i f
  have hd₁ : pushout.desc (mappingCylinderProjection i ≫ (e.inverse ≫ c)) h hc₁ = q ≫ r := by
    have hcEnd : c ≫ (q ≫ r) = mappingCylinderProjection i ≫ (e.inverse ≫ c) :=
      (Category.assoc c q r).symm.trans
        ((congrArg (fun k : C ⟶ W => k ≫ r) hcq).trans
          ((Category.assoc (mappingCylinderProjection i) a r).trans
            (congrArg (fun k : B ⟶ D => mappingCylinderProjection i ≫ k) hra)))
    have hhEnd : h ≫ (q ≫ r) = h :=
      (Category.assoc h q r).symm.trans
        ((congrArg (fun k : H ⟶ W => k ≫ r) hhq).trans hrj)
    apply pushout.hom_ext
    · rw [pushout.inl_desc]
      exact hcEnd.symm.trans
        (congrArg (fun k : C ⟶ D => k ≫ (q ≫ r))
          (doubleMappingCylinderCylinderMap_eq i f))
    · rw [pushout.inr_desc]
      exact hhEnd.symm.trans
        (congrArg (fun k : H ⟶ D => k ≫ (q ≫ r)) (doubleMappingCylinderH_eq i f))
  let HD : TopCat.Homotopy (𝟙 D) (q ≫ r) :=
    HD0.cast (congrArg (fun k : D ⟶ D => k.hom) hd₀)
      (congrArg (fun k : D ⟶ D => k.hom) hd₁)
  let HB0 := (TopCat.Homotopy.refl a).comp e.targetHomotopy.toHomotopy
  let HB : TopCat.Homotopy a (e.inverse ≫ (mappingCylinderProjection i ≫ a)) :=
    HB0.cast
      ((TopCat.hom_comp (𝟙 B) a).symm.trans
        (congrArg (fun k : B ⟶ W => k.hom) (Category.id_comp a)))
      ((TopCat.hom_comp (e.inverse ≫ mappingCylinderProjection i) a).symm.trans
        (congrArg (fun k : B ⟶ W => k.hom)
          (Category.assoc e.inverse (mappingCylinderProjection i) a)))
  let HJ : TopCat.Homotopy j j := TopCat.Homotopy.refl j
  have hb₀ : i ≫ a = f ≫ j := pushout.condition (f := i) (g := f)
  have hb₁ : i ≫ (e.inverse ≫ (mappingCylinderProjection i ≫ a)) = f ≫ j := by
    rw [← Category.assoc, e.inverse_source, ← Category.assoc,
      mappingCylinderProjection_source]
    exact hb₀
  have hbCompatible (t : unitInterval) (x : X) : HB (t, i x) = HJ (t, f x) := by
    simp only [HB, HB0, ContinuousMap.Homotopy.cast_apply]
    change a (e.targetHomotopy (t, i x)) = j (f x)
    exact (congrArg (fun z : B => a z) (e.targetHomotopy.eq_fst t ⟨x, rfl⟩)).trans
      (ConcreteCategory.congr_hom hb₀ x)
  let HW0 := TopCat.Homotopy.pushoutDesc HB HJ hb₀ hb₁ hbCompatible
  have hw₀ : pushout.desc a j hb₀ = 𝟙 W := by
    apply pushout.hom_ext
    · rw [pushout.inl_desc, Category.comp_id]
    · rw [pushout.inr_desc, Category.comp_id]
  have hw₁ : pushout.desc (e.inverse ≫ (mappingCylinderProjection i ≫ a)) j hb₁ = r ≫ q := by
    have haEnd : a ≫ (r ≫ q) = e.inverse ≫ (mappingCylinderProjection i ≫ a) :=
      (Category.assoc a r q).symm.trans
        ((congrArg (fun k : B ⟶ D => k ≫ q) hra).trans
          ((Category.assoc e.inverse c q).trans
            (congrArg (fun k : C ⟶ W => e.inverse ≫ k) hcq)))
    have hjEnd : j ≫ (r ≫ q) = j :=
      (Category.assoc j r q).symm.trans
        ((congrArg (fun k : H ⟶ D => k ≫ q) hrj).trans hhq)
    apply pushout.hom_ext
    · rw [pushout.inl_desc]
      exact haEnd.symm
    · rw [pushout.inr_desc]
      exact hjEnd.symm
  let HW : TopCat.Homotopy (𝟙 W) (r ≫ q) :=
    HW0.cast (congrArg (fun k : W ⟶ W => k.hom) hw₀)
      (congrArg (fun k : W ⟶ W => k.hom) hw₁)
  refine ⟨{
    inverse := r
    inverse_H := hrj
    cylinderHomotopy := {
      toHomotopy := HD
      prop' := ?_ }
    pushoutHomotopy := {
      toHomotopy := HW
      prop' := ?_ } }⟩
  · intro t z hz
    obtain ⟨y, rfl⟩ := hz
    change HD (t, h y) = h y
    simp only [HD, ContinuousMap.Homotopy.cast_apply]
    have hPoint : h y = pushout.inr (mappingCylinderSource i) f y :=
      congrArg (fun k : H ⟶ D => k y) (doubleMappingCylinderH_eq i f)
    exact (congrArg (fun z : D => HD0 (t, z)) hPoint).trans
      (TopCat.Homotopy.pushoutDesc_apply_inr HC HH hc₀ hc₁ hcCompatible t y)
  · intro t z hz
    obtain ⟨y, rfl⟩ := hz
    change HW (t, j y) = j y
    simp only [HW, ContinuousMap.Homotopy.cast_apply]
    exact TopCat.Homotopy.pushoutDesc_apply_inr HB HJ hb₀ hb₁ hbCompatible t y

/-- The relative comparison is DERIVED from the genuine cofibration i,
with the actual collapse and no caller inverse or homotopy data. -/
public def doubleMappingCylinderPairEquivalence
    {X B H : TopCat.{u}} (i : X ⟶ B) [Cofibration i] (f : X ⟶ H) :
    DoubleMappingCylinderPairEquivalence i f :=
  Classical.choice (nonempty_doubleMappingCylinderPairEquivalence i f)

/-- The actual collapse to the actual cobase change is weak, for arbitrary
H. The two inverse families are derived from HEP and retained above. -/
public theorem doubleMappingCylinderProjection_mem_weakHomotopyEquivalences
    {X B H : TopCat.{u}} (i : X ⟶ B) [Cofibration i] (f : X ⟶ H) :
    TopCat.weakHomotopyEquivalences (doubleMappingCylinderProjection i f) := by
  let q := doubleMappingCylinderProjection i f
  let e := doubleMappingCylinderPairEquivalence i f
  exact weakHomotopyEquivalences.of_homotopyInverse q e.inverse
    e.cylinderHomotopy.symm.toHomotopy e.pushoutHomotopy.symm.toHomotopy

private def cylinderHeight (X : TopCat.{u}) :
    mappingCylinderDomain X ⟶ TopCat.of (ULift.{u} ℝ) :=
  TopCat.ofHom ⟨fun p => ULift.up (TopCat.I.homeomorph p.2 : ℝ),
    continuous_uliftUp.comp
      (continuous_subtype_val.comp (TopCat.I.homeomorph.continuous.comp continuous_snd))⟩

private def realConstant (X : TopCat.{u}) (r : ℝ) : X ⟶ TopCat.of (ULift.{u} ℝ) :=
  TopCat.ofHom ⟨fun _ => ULift.up r, continuous_const⟩

private theorem cylinderHeight_apply (X : TopCat.{u}) (p : mappingCylinderDomain X) :
    cylinderHeight X p = ULift.up (TopCat.I.homeomorph p.2 : ℝ) := by
  unfold cylinderHeight
  rfl

private theorem realConstant_apply (X : TopCat.{u}) (r : ℝ) (x : X) :
    realConstant X r x = ULift.up r := by
  unfold realConstant
  rfl

private def mappingCylinderHeight {X B : TopCat.{u}} (i : X ⟶ B) :
    mappingCylinder i ⟶ TopCat.of (ULift.{u} ℝ) :=
  pushout.desc (cylinderHeight X) (realConstant B 1) (by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    have hL : (mappingCylinderEndpoint X 1 ≫ cylinderHeight X).hom x =
        ULift.up (TopCat.I.homeomorph (1 : TopCat.I.{u}) : ℝ) :=
      (congrArg (fun k : C(X, ULift.{u} ℝ) => k x)
        (TopCat.hom_comp (mappingCylinderEndpoint X 1) (cylinderHeight X))).trans
          ((congrArg (fun p : mappingCylinderDomain X => cylinderHeight X p)
            (mappingCylinderEndpoint_apply X 1 x)).trans
              (cylinderHeight_apply X (x, (1 : TopCat.I.{u}))))
    have hR : (i ≫ realConstant B 1).hom x = ULift.up (1 : ℝ) :=
      (congrArg (fun k : C(X, ULift.{u} ℝ) => k x)
        (TopCat.hom_comp i (realConstant B 1))).trans
          (realConstant_apply B 1 (i x))
    have ht : (ULift.up (TopCat.I.homeomorph (1 : TopCat.I.{u}) : ℝ) : ULift.{u} ℝ) =
        ULift.up (1 : ℝ) := by
      rw [TopCat.I.homeomorph_one]
      rfl
    exact hL.trans (ht.trans hR.symm))

private theorem mappingCylinderHeight_cylinder {X B : TopCat.{u}} (i : X ⟶ B) :
    mappingCylinderCylinder i ≫ mappingCylinderHeight i = cylinderHeight X := by
  rw [mappingCylinderCylinder_eq]
  unfold mappingCylinderHeight
  exact pushout.inl_desc _ _ _

private theorem mappingCylinderHeight_target {X B : TopCat.{u}} (i : X ⟶ B) :
    mappingCylinderTarget i ≫ mappingCylinderHeight i = realConstant B 1 := by
  rw [mappingCylinderTarget_eq]
  unfold mappingCylinderHeight
  exact pushout.inr_desc _ _ _

private theorem mappingCylinderHeight_source {X B : TopCat.{u}} (i : X ⟶ B) :
    mappingCylinderSource i ≫ mappingCylinderHeight i = realConstant X 0 := by
  rw [mappingCylinderSource_eq_endpoint, Category.assoc, mappingCylinderHeight_cylinder]
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  have hL : (mappingCylinderEndpoint X 0 ≫ cylinderHeight X).hom x =
      ULift.up (TopCat.I.homeomorph (0 : TopCat.I.{u}) : ℝ) :=
    (congrArg (fun k : C(X, ULift.{u} ℝ) => k x)
      (TopCat.hom_comp (mappingCylinderEndpoint X 0) (cylinderHeight X))).trans
        ((congrArg (fun p : mappingCylinderDomain X => cylinderHeight X p)
          (mappingCylinderEndpoint_apply X 0 x)).trans
            (cylinderHeight_apply X (x, (0 : TopCat.I.{u}))))
  have hR : (realConstant X 0).hom x = ULift.up (0 : ℝ) := realConstant_apply X 0 x
  have ht : (ULift.up (TopCat.I.homeomorph (0 : TopCat.I.{u}) : ℝ) : ULift.{u} ℝ) =
      ULift.up (0 : ℝ) := by
    rw [TopCat.I.homeomorph_zero]
    rfl
  exact hL.trans (ht.trans hR.symm)

private def doubleMappingCylinderHeightLifted
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    doubleMappingCylinder i f ⟶ TopCat.of (ULift.{u} ℝ) :=
  pushout.desc (mappingCylinderHeight i) (realConstant H 0) (by
    rw [mappingCylinderHeight_source]
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    rfl)

private theorem doubleMappingCylinderHeightLifted_cylinder
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    doubleMappingCylinderCylinderMap i f ≫ doubleMappingCylinderHeightLifted i f =
      mappingCylinderHeight i :=
  pushout.inl_desc _ _ _

/-- The scalar height of the SAME actual double mapping cylinder. The
categorical descent uses ULift ℝ internally and preserves the original
arbitrary space universe. -/
public def doubleMappingCylinderHeight {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    C(doubleMappingCylinder i f, ℝ) :=
  ⟨fun d => (doubleMappingCylinderHeightLifted i f d).down,
    continuous_uliftDown.comp (doubleMappingCylinderHeightLifted i f).hom.continuous⟩

public theorem doubleMappingCylinderHeight_middle
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) (x : X) (t : TopCat.I.{u}) :
    doubleMappingCylinderHeight i f (doubleMappingCylinderMiddle i f (x, t)) =
      (TopCat.I.homeomorph t : ℝ) := by
  have hm : doubleMappingCylinderMiddle i f ≫ doubleMappingCylinderHeightLifted i f =
      cylinderHeight X := by
    rw [doubleMappingCylinderMiddle, Category.assoc,
      doubleMappingCylinderHeightLifted_cylinder, mappingCylinderHeight_cylinder]
  exact congrArg ULift.down (ConcreteCategory.congr_hom hm (x, t))

public theorem doubleMappingCylinderHeight_B
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) (b : B) :
    doubleMappingCylinderHeight i f (doubleMappingCylinderB i f b) = 1 := by
  have hm : doubleMappingCylinderB i f ≫ doubleMappingCylinderHeightLifted i f =
      realConstant B 1 := by
    rw [doubleMappingCylinderB, Category.assoc,
      doubleMappingCylinderHeightLifted_cylinder, mappingCylinderHeight_target]
  exact congrArg ULift.down (ConcreteCategory.congr_hom hm b)

public theorem doubleMappingCylinderHeight_H
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) (h : H) :
    doubleMappingCylinderHeight i f (doubleMappingCylinderH i f h) = 0 := by
  have hm : doubleMappingCylinderH i f ≫ doubleMappingCylinderHeightLifted i f =
      realConstant H 0 := pushout.inr_desc _ _ _
  exact congrArg ULift.down (ConcreteCategory.congr_hom hm h)

/-- The original H-side open collar, including height zero. -/
public def doubleMappingCylinderOpenH
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    TopologicalSpace.Opens (doubleMappingCylinder i f) :=
  ⟨(doubleMappingCylinderHeight i f) ⁻¹' Set.Iio (2 / 3 : ℝ),
    isOpen_Iio.preimage (doubleMappingCylinderHeight i f).continuous⟩

/-- The original B-side open collar, including height one. -/
public def doubleMappingCylinderOpenB
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    TopologicalSpace.Opens (doubleMappingCylinder i f) :=
  ⟨(doubleMappingCylinderHeight i f) ⁻¹' Set.Ioi (1 / 3 : ℝ),
    isOpen_Ioi.preimage (doubleMappingCylinderHeight i f).continuous⟩

public theorem mem_doubleMappingCylinderOpenH
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) (d : doubleMappingCylinder i f) :
    d ∈ doubleMappingCylinderOpenH i f ↔ doubleMappingCylinderHeight i f d < 2 / 3 := Iff.rfl

public theorem mem_doubleMappingCylinderOpenB
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) (d : doubleMappingCylinder i f) :
    d ∈ doubleMappingCylinderOpenB i f ↔ 1 / 3 < doubleMappingCylinderHeight i f d := Iff.rfl

/-- These are the two overlapping original open subsets of the same D. -/
public theorem doubleMappingCylinderOpen_cover
    {X B H : TopCat.{u}} (i : X ⟶ B) (f : X ⟶ H) :
    (doubleMappingCylinderOpenH i f : Set (doubleMappingCylinder i f)) ∪
      doubleMappingCylinderOpenB i f = Set.univ := by
  apply Set.eq_univ_of_forall
  intro d
  change (doubleMappingCylinderHeight i f d : ℝ) < 2 / 3 ∨
    1 / 3 < (doubleMappingCylinderHeight i f d : ℝ)
  rcases lt_or_ge (doubleMappingCylinderHeight i f d : ℝ) (2 / 3) with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

end TopCat

end
