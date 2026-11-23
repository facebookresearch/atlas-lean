/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Homotopy.TopCat.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Homotopy-extension properties

This file defines the raw homotopy-extension property for continuous maps,
with an independent universe for the target.  Its restriction to morphisms
in `TopCat` gives the class of Hurewicz cofibrations.

The raw `I × X` formulation records only the initial face and the restriction
to the source.  It therefore avoids transporting dependent endpoint maps.
The resulting morphism property contains identities, is closed under
composition, and respects isomorphisms.

No embedding, closedness, NDR, pushout, delta-generated, or model-category
claim is made here.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory
open scoped unitInterval

universe u v w

namespace Topology

variable {A X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace A] [TopologicalSpace X]
variable [TopologicalSpace Y] [TopologicalSpace Z]

/-- Chosen extension of a homotopy on `A` to a homotopy on `X`.

The compatibility proof `h0` says that the prescribed homotopy starts at
the restriction of `f` along `i`. -/
structure HomotopyExtensionData
    (i : C(A, X)) (f : C(X, Y)) (H : C(unitInterval × A, Y))
    (h0 : ∀ a, H (0, a) = f (i a)) where
  /-- The extended continuously parametrized map. -/
  extension : C(unitInterval × X, Y)
  /-- The extension starts at the given ambient map. -/
  extension_zero (x : X) : extension (0, x) = f x
  /-- The extension restricts to the prescribed homotopy. -/
  extension_subspace (t : unitInterval) (a : A) :
    extension (t, i a) = H (t, a)

namespace HomotopyExtensionData

variable {i : C(A, X)} {f : C(X, Y)} {H : C(unitInterval × A, Y)}
variable {h0 : ∀ a, H (0, a) = f (i a)}

/-- The endpoint of a chosen homotopy extension. -/
def endpoint (d : HomotopyExtensionData i f H h0) : C(X, Y) where
  toFun x := d.extension (1, x)
  continuous_toFun := d.extension.continuous.comp
    (continuous_const.prodMk continuous_id)

/-- A chosen extension determines an ordinary homotopy of the ambient map. -/
def toHomotopy (d : HomotopyExtensionData i f H h0) :
    ContinuousMap.Homotopy f d.endpoint where
  toFun := d.extension
  continuous_toFun := d.extension.continuous
  map_zero_left := d.extension_zero
  map_one_left _ := rfl

/-- Postcompose chosen extension data with a map of target spaces. -/
def postcomp (d : HomotopyExtensionData i f H h0) (k : C(Y, Z)) :
    HomotopyExtensionData i (k.comp f) (k.comp H)
      (fun a => congrArg k (h0 a)) where
  extension := k.comp d.extension
  extension_zero x := congrArg k (d.extension_zero x)
  extension_subspace t a := congrArg k (d.extension_subspace t a)

@[simp]
theorem endpoint_apply (d : HomotopyExtensionData i f H h0) (x : X) :
    d.endpoint x = d.extension (1, x) :=
  rfl

@[simp]
theorem toHomotopy_apply (d : HomotopyExtensionData i f H h0)
    (p : unitInterval × X) :
    d.toHomotopy p = d.extension p :=
  rfl

@[simp]
theorem postcomp_extension_apply
    (d : HomotopyExtensionData i f H h0) (k : C(Y, Z))
    (p : unitInterval × X) :
    (d.postcomp k).extension p = k (d.extension p) :=
  rfl

end HomotopyExtensionData

/-- A continuous map has the homotopy-extension property when every
compatible homotopy into any target in universe `v` extends to its ambient
space. -/
def HasHomotopyExtensionProperty (i : C(A, X)) : Prop :=
  ∀ {Y : Type v} [TopologicalSpace Y]
    (f : C(X, Y)) (H : C(unitInterval × A, Y))
    (h0 : ∀ a, H (0, a) = f (i a)),
    Nonempty (HomotopyExtensionData i f H h0)

/-- The identity map has the homotopy-extension property. -/
theorem hasHomotopyExtensionProperty_id :
    HasHomotopyExtensionProperty.{u, v} (ContinuousMap.id X) := by
  intro Y _ f H h0
  exact ⟨
    { extension := H
      extension_zero := h0
      extension_subspace := fun _ _ => rfl }⟩

/-- Homotopy-extension properties are stable under composition.  The
homotopy is first extended across `i`, then across `j`. -/
theorem HasHomotopyExtensionProperty.comp
    {B : Type u} [TopologicalSpace B]
    {i : C(A, B)} {j : C(B, X)}
    (hi : HasHomotopyExtensionProperty.{u, v} i)
    (hj : HasHomotopyExtensionProperty.{u, v} j) :
    HasHomotopyExtensionProperty.{u, v} (j.comp i) := by
  intro Y _ f H h0
  have h0B (a : A) : H (0, a) = (f.comp j) (i a) := by
    simpa only [ContinuousMap.comp_apply] using h0 a
  obtain ⟨dB⟩ := hi (f.comp j) H h0B
  obtain ⟨dX⟩ := hj f dB.extension dB.extension_zero
  exact ⟨
    { extension := dX.extension
      extension_zero := dX.extension_zero
      extension_subspace := fun t a =>
        (dX.extension_subspace t (i a)).trans
          (dB.extension_subspace t a) }⟩

end Topology

namespace TopCat

/-- Hurewicz cofibrations in `TopCat`, defined by the raw homotopy-extension
property.  The general continuous-map predicate also supports targets in an
independent universe; this category-level wrapper uses the ambient universe
of `TopCat`. -/
def hurewiczCofibrations : MorphismProperty TopCat.{u} :=
  fun _ _ i => Topology.HasHomotopyExtensionProperty.{u, u} i.hom

/-- Predicate spelling of membership in `hurewiczCofibrations`. -/
abbrev IsHurewiczCofibration {X Y : TopCat.{u}} (i : X ⟶ Y) : Prop :=
  hurewiczCofibrations i

/-- An actual Hurewicz inclusion extends the prescribed original source homotopy. -/
public theorem exists_homotopyExtension_of_hurewicz
    {A B H : TopCat.{u}} (i : A ⟶ B) (hi : TopCat.IsHurewiczCofibration i)
    (f : B ⟶ H) (g : A ⟶ H) (K : TopCat.Homotopy (i ≫ f) g) :
    ∃ gB : B ⟶ H, ∃ L : TopCat.Homotopy f gB,
      i ≫ gB = g ∧ ∀ t : unitInterval, ∀ a : A, L (t, i a) = K (t, a) := by
  have h0 (a : A) : K.toContinuousMap (0, a) = f.hom (i.hom a) := K.map_zero_left a
  obtain ⟨d⟩ := hi f.hom K.toContinuousMap h0
  let gB : B ⟶ H := TopCat.ofHom d.endpoint
  let L : TopCat.Homotopy f gB := d.toHomotopy
  refine ⟨gB, L, ?_, ?_⟩
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro a
    change d.extension (1, i.hom a) = g.hom a
    exact (d.extension_subspace 1 a).trans (K.map_one_left a)
  · exact d.extension_subspace

/-- Identity morphisms are Hurewicz cofibrations. -/
theorem hurewiczCofibrations_id (X : TopCat.{u}) :
    hurewiczCofibrations (𝟙 X) := by
  exact Topology.hasHomotopyExtensionProperty_id

/-- A composite of Hurewicz cofibrations is Hurewicz. -/
theorem hurewiczCofibrations_comp
    {X Y Z : TopCat.{u}} (i : X ⟶ Y) (j : Y ⟶ Z)
    (hi : hurewiczCofibrations i) (hj : hurewiczCofibrations j) :
    hurewiczCofibrations (i ≫ j) := by
  exact Topology.HasHomotopyExtensionProperty.comp hi hj

instance hurewiczCofibrations_isMultiplicative :
    hurewiczCofibrations.IsMultiplicative where
  id_mem := hurewiczCofibrations_id
  comp_mem := hurewiczCofibrations_comp

/-- The forward map of an isomorphism is a Hurewicz cofibration. -/
theorem hurewiczCofibrations_iso {X Y : TopCat.{u}} (e : X ≅ Y) :
    hurewiczCofibrations e.hom := by
  intro Z _ f H h0
  let pre : C(unitInterval × Y, unitInterval × X) :=
    ContinuousMap.fst.prodMk (e.inv.hom.comp ContinuousMap.snd)
  refine ⟨
    { extension := H.comp pre
      extension_zero := ?_
      extension_subspace := ?_ }⟩
  · intro y
    calc
      H (0, e.inv y) = f (e.hom (e.inv y)) := h0 (e.inv y)
      _ = f y := congrArg f (TopCat.inv_hom_id_apply e y)
  · intro t x
    exact congrArg (fun z => H (t, z)) (TopCat.hom_inv_id_apply e x)

instance hurewiczCofibrations_respectsIso :
    hurewiczCofibrations.RespectsIso :=
  MorphismProperty.RespectsIso.mk hurewiczCofibrations
    (fun e f hf => hurewiczCofibrations_comp e.hom f
      (hurewiczCofibrations_iso e) hf)
    (fun e f hf => hurewiczCofibrations_comp f e.hom hf
      (hurewiczCofibrations_iso e))

end TopCat

end
