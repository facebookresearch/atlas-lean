/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.TrivialCofibrationExtension
public import MathlibExt.Topology.Category.TopCat.QuotientPushout
public import Mathlib.Topology.Category.TopCat.Limits.Products

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The actual mapping cylinder as a relative equivalence of a cofibration

The cylinder is the original pushout of the endpoint at one and the given
map. Its collapse and whole source triangles are literal. The existing
cofibration HEP extends the reverse cylinder path. That extension gives a
computed inverse fixed on the original source, and both inverse homotopies
are fixed on that entire source image.

The same cylinder is used by the double-mapping-cylinder collar; no second
path-object fibration, relative-equivalence witness, or collar is an input.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped TopCat.modelCategory

universe u

namespace TopCat

private def reverseCylinderTime (s : unitInterval) : unitInterval :=
  ⟨1 - (s : ℝ), ⟨sub_nonneg.mpr s.2.2, by linarith [s.2.1]⟩⟩

private def shrinkCylinderTime (s t : unitInterval) : unitInterval :=
  ⟨(1 - (s : ℝ)) * (t : ℝ), ⟨mul_nonneg (sub_nonneg.mpr s.2.2) t.2.1, by
    calc
      (1 - (s : ℝ)) * (t : ℝ) ≤ (1 - (s : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left t.2.2 (sub_nonneg.mpr s.2.2)
      _ ≤ 1 := by linarith [s.2.1]⟩⟩

private theorem continuous_reverseCylinderTime : Continuous reverseCylinderTime := by
  exact (continuous_const.sub continuous_subtype_val).subtype_mk _

private theorem continuous_shrinkCylinderTime :
    Continuous (fun p : unitInterval × unitInterval => shrinkCylinderTime p.1 p.2) := by
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

private theorem reverseCylinderTime_zero : reverseCylinderTime 0 = 1 := by
  apply Subtype.ext
  simp [reverseCylinderTime]

private theorem reverseCylinderTime_one : reverseCylinderTime 1 = 0 := by
  apply Subtype.ext
  simp [reverseCylinderTime]

private theorem shrinkCylinderTime_zero (t : unitInterval) : shrinkCylinderTime 0 t = t := by
  apply Subtype.ext
  simp [shrinkCylinderTime]

private theorem shrinkCylinderTime_one (t : unitInterval) : shrinkCylinderTime 1 t = 0 := by
  apply Subtype.ext
  simp [shrinkCylinderTime]

private theorem shrinkCylinderTime_right_zero (s : unitInterval) :
    shrinkCylinderTime s 0 = 0 := by
  apply Subtype.ext
  simp [shrinkCylinderTime]

private theorem shrinkCylinderTime_right_one (s : unitInterval) :
    shrinkCylinderTime s 1 = reverseCylinderTime s := by
  apply Subtype.ext
  simp [shrinkCylinderTime, reverseCylinderTime]

private theorem intervalHomeomorph_symm_zero :
    (TopCat.I.homeomorph.{u}).symm (0 : unitInterval) = (0 : TopCat.I.{u}) := by
  apply (TopCat.I.homeomorph.{u}).injective
  simp

private theorem intervalHomeomorph_symm_one :
    (TopCat.I.homeomorph.{u}).symm (1 : unitInterval) = (1 : TopCat.I.{u}) := by
  apply (TopCat.I.homeomorph.{u}).injective
  simp

private def cylinderInterpolationUnit
    (r t : TopCat.I.{u}) (s : unitInterval) : unitInterval :=
  ⟨(1 - (s : ℝ)) * (TopCat.I.homeomorph t : ℝ) +
      (s : ℝ) * (TopCat.I.homeomorph r : ℝ), ⟨by
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr s.2.2) (TopCat.I.homeomorph t).2.1)
      (mul_nonneg s.2.1 (TopCat.I.homeomorph r).2.1), by
    have ht := mul_le_mul_of_nonneg_left (TopCat.I.homeomorph t).2.2
      (sub_nonneg.mpr s.2.2)
    have hr := mul_le_mul_of_nonneg_left (TopCat.I.homeomorph r).2.2 s.2.1
    nlinarith⟩⟩

/-- The actual interval interpolation used on all three collar sectors.
Its target is the original large-universe interval. -/
public def mappingCylinderInterpolate
    (r : TopCat.I.{u}) (s : unitInterval) (t : TopCat.I.{u}) : TopCat.I.{u} :=
  (TopCat.I.homeomorph.{u}).symm (cylinderInterpolationUnit r t s)

public theorem mappingCylinderInterpolate_height
    (r : TopCat.I.{u}) (s : unitInterval) (t : TopCat.I.{u}) :
    (TopCat.I.homeomorph (mappingCylinderInterpolate r s t) : ℝ) =
      (1 - (s : ℝ)) * (TopCat.I.homeomorph t : ℝ) +
        (s : ℝ) * (TopCat.I.homeomorph r : ℝ) := by
  rw [mappingCylinderInterpolate, (TopCat.I.homeomorph.{u}).apply_symm_apply]
  rfl

public theorem continuous_mappingCylinderInterpolate (r : TopCat.I.{u}) :
    Continuous (fun p : unitInterval × TopCat.I.{u} => mappingCylinderInterpolate r p.1 p.2) := by
  apply (TopCat.I.homeomorph.{u}).symm.continuous.comp
  exact (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_subtype_val.comp (TopCat.I.homeomorph.continuous.comp continuous_snd))).add
    ((continuous_subtype_val.comp continuous_fst).mul continuous_const)).subtype_mk _

public theorem mappingCylinderInterpolate_zero (r t : TopCat.I.{u}) :
    mappingCylinderInterpolate r 0 t = t := by
  apply (TopCat.I.homeomorph.{u}).injective
  apply Subtype.ext
  simp [mappingCylinderInterpolate_height]

public theorem mappingCylinderInterpolate_one (r t : TopCat.I.{u}) :
    mappingCylinderInterpolate r 1 t = r := by
  apply (TopCat.I.homeomorph.{u}).injective
  apply Subtype.ext
  simp [mappingCylinderInterpolate_height]

public theorem mappingCylinderInterpolate_fixed (r : TopCat.I.{u}) (s : unitInterval) :
    mappingCylinderInterpolate r s r = r := by
  apply (TopCat.I.homeomorph.{u}).injective
  apply Subtype.ext
  rw [mappingCylinderInterpolate_height]
  ring

/-- The literal cylinder domain, with its actual product topology. -/
public abbrev mappingCylinderDomain (X : TopCat.{u}) : TopCat.{u} :=
  TopCat.of (X × TopCat.I.{u})

/-- The two actual endpoint maps into the cylinder domain. -/
public def mappingCylinderEndpoint (X : TopCat.{u}) (t : TopCat.I.{u}) :
    X ⟶ mappingCylinderDomain X :=
  TopCat.ofHom ⟨fun x => (x, t), continuous_id.prodMk continuous_const⟩

public theorem mappingCylinderEndpoint_apply
    (X : TopCat.{u}) (t : TopCat.I.{u}) (x : X) : mappingCylinderEndpoint X t x = (x, t) := by
  unfold mappingCylinderEndpoint
  rfl

/-- The original mapping cylinder pushout. -/
public abbrev mappingCylinder {X B : TopCat.{u}} (i : X ⟶ B) : TopCat.{u} :=
  pushout (mappingCylinderEndpoint X 1) i

/-- The actual cylinder map into the original mapping cylinder. -/
public def mappingCylinderCylinder {X B : TopCat.{u}} (i : X ⟶ B) :
    mappingCylinderDomain X ⟶ mappingCylinder i :=
  pushout.inl (mappingCylinderEndpoint X 1) i

/-- The actual target inclusion in the original mapping cylinder. -/
public def mappingCylinderTarget {X B : TopCat.{u}} (i : X ⟶ B) : B ⟶ mappingCylinder i :=
  pushout.inr (mappingCylinderEndpoint X 1) i

/-- The literal cylinder leg is the original pushout inclusion. -/
public theorem mappingCylinderCylinder_eq {X B : TopCat.{u}} (i : X ⟶ B) :
    mappingCylinderCylinder i = pushout.inl (mappingCylinderEndpoint X 1) i := by
  unfold mappingCylinderCylinder
  rfl

/-- The literal target leg is the original pushout inclusion. -/
public theorem mappingCylinderTarget_eq {X B : TopCat.{u}} (i : X ⟶ B) :
    mappingCylinderTarget i = pushout.inr (mappingCylinderEndpoint X 1) i := by
  unfold mappingCylinderTarget
  rfl

/-- The original source is the cylinder endpoint at zero. -/
public def mappingCylinderSource {X B : TopCat.{u}} (i : X ⟶ B) : X ⟶ mappingCylinder i :=
  mappingCylinderEndpoint X 0 ≫ mappingCylinderCylinder i

public theorem mappingCylinderSource_apply {X B : TopCat.{u}} (i : X ⟶ B) (x : X) :
    mappingCylinderSource i x = mappingCylinderCylinder i (x, (0 : TopCat.I.{u})) := by
  unfold mappingCylinderSource
  rw [TopCat.comp_app, mappingCylinderEndpoint_apply]

/-- The original product projection of the actual cylinder domain. -/
public def mappingCylinderFirst (X : TopCat.{u}) : mappingCylinderDomain X ⟶ X :=
  TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

/-- The actual cylinder projection keeps its original first coordinate. -/
public theorem mappingCylinderFirst_apply (X : TopCat.{u}) (p : mappingCylinderDomain X) :
    mappingCylinderFirst X p = p.1 := by
  unfold mappingCylinderFirst
  rfl

private theorem mappingCylinderEndpoint_first (X : TopCat.{u}) (t : TopCat.I.{u}) :
    mappingCylinderEndpoint X t ≫ mappingCylinderFirst X = 𝟙 X := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  rfl

/-- Collapse of the original cylinder onto its original target. -/
public def mappingCylinderProjection {X B : TopCat.{u}} (i : X ⟶ B) :
    mappingCylinder i ⟶ B :=
  pushout.desc (mappingCylinderFirst X ≫ i) (𝟙 B) (by
    rw [← Category.assoc, mappingCylinderEndpoint_first, Category.id_comp, Category.comp_id])

@[reassoc]
public theorem mappingCylinderProjection_cylinder {X B : TopCat.{u}} (i : X ⟶ B) :
    mappingCylinderCylinder i ≫ mappingCylinderProjection i = mappingCylinderFirst X ≫ i :=
  pushout.inl_desc _ _ _

@[reassoc]
public theorem mappingCylinderProjection_target {X B : TopCat.{u}} (i : X ⟶ B) :
    mappingCylinderTarget i ≫ mappingCylinderProjection i = 𝟙 B :=
  pushout.inr_desc _ _ _

@[reassoc]
public theorem mappingCylinderProjection_source {X B : TopCat.{u}} (i : X ⟶ B) :
    mappingCylinderSource i ≫ mappingCylinderProjection i = i := by
  rw [mappingCylinderSource, Category.assoc, mappingCylinderProjection_cylinder,
    ← Category.assoc, mappingCylinderEndpoint_first, Category.id_comp]

@[reassoc]
public theorem mappingCylinder_end_square {X B : TopCat.{u}} (i : X ⟶ B) :
    mappingCylinderEndpoint X 1 ≫ mappingCylinderCylinder i = i ≫ mappingCylinderTarget i := by
  rw [mappingCylinderCylinder_eq, mappingCylinderTarget_eq]
  exact pushout.condition (f := mappingCylinderEndpoint X 1) (g := i)

public theorem mappingCylinderProjection_cylinder_apply
    {X B : TopCat.{u}} (i : X ⟶ B) (x : X) (t : TopCat.I.{u}) :
    mappingCylinderProjection i (mappingCylinderCylinder i (x, t)) = i x :=
  ConcreteCategory.congr_hom (mappingCylinderProjection_cylinder i) (x, t)

private def reverseMappingCylinderPath {X B : TopCat.{u}} (i : X ⟶ B) :
    TopCat.Homotopy (i ≫ mappingCylinderTarget i) (mappingCylinderSource i) where
  toFun p := mappingCylinderCylinder i
    (p.2, (TopCat.I.homeomorph.{u}).symm (reverseCylinderTime p.1))
  continuous_toFun := (mappingCylinderCylinder i).hom.continuous.comp
    (continuous_snd.prodMk ((TopCat.I.homeomorph.{u}).symm.continuous.comp
      (continuous_reverseCylinderTime.comp continuous_fst)))
  map_zero_left x := by
    rw [reverseCylinderTime_zero, intervalHomeomorph_symm_one]
    exact ConcreteCategory.congr_hom (mappingCylinder_end_square i) x
  map_one_left x := by
    rw [reverseCylinderTime_one, intervalHomeomorph_symm_zero]
    rfl

private def shrinkMappingCylinderPath {X B : TopCat.{u}} (i : X ⟶ B) :
    TopCat.Homotopy (mappingCylinderCylinder i)
      (mappingCylinderFirst X ≫ mappingCylinderSource i) where
  toFun p := mappingCylinderCylinder i
    (p.2.1, (TopCat.I.homeomorph.{u}).symm
      (shrinkCylinderTime p.1 (TopCat.I.homeomorph p.2.2)))
  continuous_toFun := (mappingCylinderCylinder i).hom.continuous.comp
    ((continuous_fst.comp continuous_snd).prodMk
      ((TopCat.I.homeomorph.{u}).symm.continuous.comp
        (continuous_shrinkCylinderTime.comp
          (continuous_fst.prodMk (TopCat.I.homeomorph.continuous.comp
            (continuous_snd.comp continuous_snd))))))
  map_zero_left p := by
    rw [shrinkCylinderTime_zero, (TopCat.I.homeomorph.{u}).symm_apply_apply]
  map_one_left p := by
    rw [shrinkCylinderTime_one, intervalHomeomorph_symm_zero]
    rfl

/-- Derived pair-equivalence data. The inverse maps the entire original
source strictly to its original cylinder endpoint; BOTH homotopies are
fixed on their whole original source images. -/
public structure MappingCylinderPairEquivalence {X B : TopCat.{u}} (i : X ⟶ B) where
  /-- The map from B to the cylinder preserving the original source inclusion. -/
  inverse : B ⟶ mappingCylinder i
  inverse_source : i ≫ inverse = mappingCylinderSource i
  /-- The homotopy from the cylinder identity to projection followed by inverse,
  fixed on the original source image. -/
  cylinderHomotopy : ContinuousMap.HomotopyRel
    (𝟙 (mappingCylinder i) : mappingCylinder i ⟶ mappingCylinder i).hom
    (mappingCylinderProjection i ≫ inverse).hom
    (Set.range (mappingCylinderSource i))
  /-- The homotopy from the identity on B to inverse followed by projection,
  fixed on the image of the original inclusion. -/
  targetHomotopy : ContinuousMap.HomotopyRel
    (𝟙 B : B ⟶ B).hom (inverse ≫ mappingCylinderProjection i).hom (Set.range i)

private theorem nonempty_mappingCylinderPairEquivalence_of_hurewicz
    {X B : TopCat.{u}} (i : X ⟶ B) (hi : TopCat.IsHurewiczCofibration i) :
    Nonempty (MappingCylinderPairEquivalence i) := by
  let K := reverseMappingCylinderPath i
  obtain ⟨s, L, his, hL⟩ := exists_homotopyExtension_of_hurewicz
    i hi (mappingCylinderTarget i) (mappingCylinderSource i) K
  let C := mappingCylinder i
  let HY := shrinkMappingCylinderPath i
  have h₀ : mappingCylinderEndpoint X 1 ≫ mappingCylinderCylinder i =
      i ≫ mappingCylinderTarget i := mappingCylinder_end_square i
  have h₁ : mappingCylinderEndpoint X 1 ≫
      (mappingCylinderFirst X ≫ mappingCylinderSource i) = i ≫ s := by
    rw [← Category.assoc, mappingCylinderEndpoint_first, Category.id_comp, his]
  have hCompatible (t : unitInterval) (x : X) :
      HY (t, mappingCylinderEndpoint X 1 x) = L (t, i x) := by
    rw [hL]
    change mappingCylinderCylinder i
      (x, (TopCat.I.homeomorph.{u}).symm
        (shrinkCylinderTime t (TopCat.I.homeomorph (1 : TopCat.I.{u})))) =
      mappingCylinderCylinder i (x, (TopCat.I.homeomorph.{u}).symm (reverseCylinderTime t))
    rw [TopCat.I.homeomorph_one, shrinkCylinderTime_right_one]
  let H := TopCat.Homotopy.pushoutDesc HY L h₀ h₁ hCompatible
  have hStart : pushout.desc (mappingCylinderCylinder i) (mappingCylinderTarget i) h₀ = 𝟙 C := by
    apply pushout.hom_ext
    · rw [pushout.inl_desc, Category.comp_id, mappingCylinderCylinder_eq]
    · rw [pushout.inr_desc, Category.comp_id, mappingCylinderTarget_eq]
  have hEnd : pushout.desc (mappingCylinderFirst X ≫ mappingCylinderSource i) s h₁ =
      mappingCylinderProjection i ≫ s := by
    apply pushout.hom_ext
    · rw [pushout.inl_desc, ← Category.assoc, ← mappingCylinderCylinder_eq,
         mappingCylinderProjection_cylinder,
        Category.assoc, his]
    · rw [pushout.inr_desc, ← Category.assoc, ← mappingCylinderTarget_eq,
         mappingCylinderProjection_target,
        Category.id_comp]
  let HC : TopCat.Homotopy (𝟙 C) (mappingCylinderProjection i ≫ s) :=
    H.cast (congrArg (fun k : C ⟶ C => k.hom) hStart)
      (congrArg (fun k : C ⟶ C => k.hom) hEnd)
  let HR0 := (TopCat.Homotopy.refl (mappingCylinderProjection i)).comp L
  let HR : TopCat.Homotopy (𝟙 B) (s ≫ mappingCylinderProjection i) :=
    HR0.cast (congrArg (fun k : B ⟶ B => k.hom) (mappingCylinderProjection_target i)) rfl
  refine ⟨{
    inverse := s
    inverse_source := his
    cylinderHomotopy := {
      toHomotopy := HC
      prop' := ?_ }
    targetHomotopy := {
      toHomotopy := HR
      prop' := ?_ } }⟩
  · intro t z hz
    obtain ⟨x, rfl⟩ := hz
    change HC (t, mappingCylinderCylinder i (x, (0 : TopCat.I.{u}))) =
      mappingCylinderCylinder i (x, (0 : TopCat.I.{u}))
    simp only [HC, ContinuousMap.Homotopy.cast_apply]
    have hCylinder : H (t, mappingCylinderCylinder i (x, (0 : TopCat.I.{u}))) =
        HY (t, (x, (0 : TopCat.I.{u}))) := by
      have hPoint : mappingCylinderCylinder i (x, (0 : TopCat.I.{u})) =
          pushout.inl (mappingCylinderEndpoint X 1) i (x, (0 : TopCat.I.{u})) :=
        congrArg (fun k : mappingCylinderDomain X ⟶ C => k (x, (0 : TopCat.I.{u})))
          (mappingCylinderCylinder_eq i)
      exact (congrArg (fun z : C => H (t, z)) hPoint).trans
        (TopCat.Homotopy.pushoutDesc_apply_inl HY L h₀ h₁ hCompatible t _)
    refine hCylinder.trans ?_
    change mappingCylinderCylinder i
      (x, (TopCat.I.homeomorph.{u}).symm
        (shrinkCylinderTime t (TopCat.I.homeomorph (0 : TopCat.I.{u})))) = _
    rw [TopCat.I.homeomorph_zero, shrinkCylinderTime_right_zero, intervalHomeomorph_symm_zero]
  · intro t z hz
    obtain ⟨x, rfl⟩ := hz
    change HR (t, i x) = i x
    simp only [HR, HR0, ContinuousMap.Homotopy.cast_apply]
    change mappingCylinderProjection i (L (t, i x)) = i x
    rw [hL]
    exact mappingCylinderProjection_cylinder_apply i x
      ((TopCat.I.homeomorph.{u}).symm (reverseCylinderTime t))

/-- The relative cylinder inverse and BOTH relative families are computed
from the genuine cofibration HEP. No inverse or homotopy family is a caller
premise. -/
public def mappingCylinderPairEquivalenceOfHurewicz
    {X B : TopCat.{u}} (i : X ⟶ B) (hi : TopCat.IsHurewiczCofibration i) :
    MappingCylinderPairEquivalence i :=
  Classical.choice (nonempty_mappingCylinderPairEquivalence_of_hurewicz i hi)

/-- The original model-cofibration interface retains the computed Hurewicz cylinder equivalence. -/
public def mappingCylinderPairEquivalence
    {X B : TopCat.{u}} (i : X ⟶ B) [Cofibration i] : MappingCylinderPairEquivalence i :=
  mappingCylinderPairEquivalenceOfHurewicz i
    (cofibrations_le_hurewiczCofibrations i (mem_cofibrations i))

private def mappingCylinderNaturalHomotopyData
    {X B : TopCat.{u}} (i : X ⟶ B) :
    {K : TopCat.Homotopy (𝟙 (mappingCylinder i))
        (mappingCylinderProjection i ≫ mappingCylinderTarget i) //
      (∀ s : unitInterval, ∀ p : mappingCylinderDomain X,
        K (s, mappingCylinderCylinder i p) =
          mappingCylinderCylinder i (p.1, mappingCylinderInterpolate (1 : TopCat.I.{u}) s p.2)) ∧
      ∀ s : unitInterval, ∀ b : B,
        K (s, mappingCylinderTarget i b) = mappingCylinderTarget i b} := by
  let HY : TopCat.Homotopy (mappingCylinderCylinder i)
      ((mappingCylinderFirst X ≫ i) ≫ mappingCylinderTarget i) :=
    { toFun := fun z => mappingCylinderCylinder i
        (z.2.1, mappingCylinderInterpolate (1 : TopCat.I.{u}) z.1 z.2.2)
      continuous_toFun := (mappingCylinderCylinder i).hom.continuous.comp
        ((continuous_fst.comp continuous_snd).prodMk
          ((continuous_mappingCylinderInterpolate (1 : TopCat.I.{u})).comp
            (continuous_fst.prodMk (continuous_snd.comp continuous_snd))))
      map_zero_left := by
        intro p
        rw [mappingCylinderInterpolate_zero]
      map_one_left := by
        intro p
        rw [mappingCylinderInterpolate_one]
        exact ConcreteCategory.congr_hom (mappingCylinder_end_square i) p.1 }
  let HB : TopCat.Homotopy (mappingCylinderTarget i) (mappingCylinderTarget i) :=
    TopCat.Homotopy.refl (mappingCylinderTarget i)
  have h₀ : mappingCylinderEndpoint X 1 ≫ mappingCylinderCylinder i =
      i ≫ mappingCylinderTarget i := mappingCylinder_end_square i
  have h₁ : mappingCylinderEndpoint X 1 ≫
      ((mappingCylinderFirst X ≫ i) ≫ mappingCylinderTarget i) =
      i ≫ mappingCylinderTarget i := by
    rw [← Category.assoc, ← Category.assoc, mappingCylinderEndpoint_first, Category.id_comp]
  have hCompatible (s : unitInterval) (x : X) :
      HY (s, mappingCylinderEndpoint X 1 x) = HB (s, i x) := by
    change mappingCylinderCylinder i (x, mappingCylinderInterpolate (1 : TopCat.I.{u}) s 1) =
      mappingCylinderTarget i (i x)
    rw [mappingCylinderInterpolate_fixed]
    exact ConcreteCategory.congr_hom h₀ x
  let H := TopCat.Homotopy.pushoutDesc HY HB h₀ h₁ hCompatible
  have hStart : pushout.desc (mappingCylinderCylinder i) (mappingCylinderTarget i) h₀ =
      𝟙 (mappingCylinder i) := by
    apply pushout.hom_ext
    · rw [pushout.inl_desc, Category.comp_id, mappingCylinderCylinder_eq]
    · rw [pushout.inr_desc, Category.comp_id, mappingCylinderTarget_eq]
  have hEnd : pushout.desc ((mappingCylinderFirst X ≫ i) ≫ mappingCylinderTarget i)
      (mappingCylinderTarget i) h₁ = mappingCylinderProjection i ≫ mappingCylinderTarget i := by
    apply pushout.hom_ext
    · rw [pushout.inl_desc, ← Category.assoc, ← mappingCylinderCylinder_eq,
         mappingCylinderProjection_cylinder]
    · rw [pushout.inr_desc, ← Category.assoc, ← mappingCylinderTarget_eq,
         mappingCylinderProjection_target, Category.id_comp]
  let K := H.cast (congrArg (fun k => k.hom) hStart) (congrArg (fun k => k.hom) hEnd)
  refine ⟨K, ?_, ?_⟩
  · intro s p
    simp only [K, ContinuousMap.Homotopy.cast_apply]
    exact TopCat.Homotopy.pushoutDesc_apply_inl HY HB h₀ h₁ hCompatible s p
  · intro s b
    simp only [K, ContinuousMap.Homotopy.cast_apply]
    exact TopCat.Homotopy.pushoutDesc_apply_inr HY HB h₀ h₁ hCompatible s b

/-- The original cylinder contracts to B without any hypothesis on i.
The computed whole cylinder/target characteristics are stored with it. -/
public def mappingCylinderNaturalHomotopy
    {X B : TopCat.{u}} (i : X ⟶ B) :
    TopCat.Homotopy (𝟙 (mappingCylinder i))
      (mappingCylinderProjection i ≫ mappingCylinderTarget i) :=
  (mappingCylinderNaturalHomotopyData i).1

public theorem mappingCylinderNaturalHomotopy_cylinder
    {X B : TopCat.{u}} (i : X ⟶ B) (s : unitInterval) (p : mappingCylinderDomain X) :
    mappingCylinderNaturalHomotopy i (s, mappingCylinderCylinder i p) =
      mappingCylinderCylinder i (p.1, mappingCylinderInterpolate (1 : TopCat.I.{u}) s p.2) :=
  (mappingCylinderNaturalHomotopyData i).2.1 s p

public theorem mappingCylinderNaturalHomotopy_target
    {X B : TopCat.{u}} (i : X ⟶ B) (s : unitInterval) (b : B) :
    mappingCylinderNaturalHomotopy i (s, mappingCylinderTarget i b) =
      mappingCylinderTarget i b :=
  (mappingCylinderNaturalHomotopyData i).2.2 s b

end TopCat

end
