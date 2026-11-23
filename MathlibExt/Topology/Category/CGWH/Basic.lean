/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Compactness.WeakHausdorffSpace
public import Mathlib.Topology.Category.CompactlyGenerated

/-!
# Compactly generated weak Hausdorff spaces

This file defines the universe-polymorphic category `CGWH` of compactly
generated weak Hausdorff spaces.  It is an induced concrete category over
Mathlib's existing `CompactlyGenerated` carrier, so its morphisms are
continuous maps and it introduces no second topology or compact-generation
dictionary.

Only the basic carrier, fully faithful inclusions, and
homeomorphism/isomorphism adapters are provided here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory TopologicalSpace

/-- The category of `u`-compactly generated, `u`-weak-Hausdorff,
`v`-small topological spaces. -/
structure CGWH where
  /-- The underlying compactly generated space. -/
  toCompactlyGenerated : CompactlyGenerated.{u, v}
  /-- The underlying space is weak Hausdorff relative to the compact-probe
  universe. -/
  [is_weakHausdorff :
    UWeakHausdorffSpace.{u} toCompactlyGenerated]

namespace CGWH

/-- The underlying topological space of a CGWH object. -/
abbrev toTop (X : CGWH.{u, v}) : TopCat.{v} :=
  X.toCompactlyGenerated.toTop

instance : Inhabited CGWH.{u, v} :=
  ⟨{ toCompactlyGenerated :=
      CompactlyGenerated.of (ULift.{v} (Fin 37)) }⟩

instance : CoeSort CGWH.{u, v} (Type v) where
  coe X := X.toCompactlyGenerated

attribute [instance] CGWH.is_weakHausdorff

instance : Category.{v, v + 1} CGWH.{u, v} :=
  inferInstanceAs
    (Category (InducedCategory _ CGWH.toCompactlyGenerated))

instance : ConcreteCategory.{v} CGWH.{u, v} (fun X Y ↦ C(X, Y)) :=
  inferInstanceAs
    (ConcreteCategory
      (InducedCategory _ CGWH.toCompactlyGenerated) (fun X Y ↦ C(X, Y)))

instance (X : CGWH.{u, v}) : T1Space X :=
  UWeakHausdorffSpace.toT1Space X

variable (X : Type v) [TopologicalSpace X]
  [UCompactlyGeneratedSpace.{u} X]
  [UWeakHausdorffSpace.{u} X]

/-- Constructor for CGWH objects. -/
abbrev of : CGWH.{u, v} where
  toCompactlyGenerated := CompactlyGenerated.of X
  is_weakHausdorff := inferInstance

open Lean.PrettyPrinter.Delaborator in
/-- This prints `CGWH.of X` as `↧X`. -/
@[app_delab CGWH.of]
meta def delabOf : Delab := CategoryTheory.delabOf

section

variable {X Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]
  [UCompactlyGeneratedSpace.{u} X]
  [UCompactlyGeneratedSpace.{u} Y]
  [UWeakHausdorffSpace.{u} X]
  [UWeakHausdorffSpace.{u} Y]

/-- Typecheck a continuous map as a CGWH morphism. -/
abbrev ofHom (f : C(X, Y)) : of X ⟶ of Y :=
  ConcreteCategory.ofHom f

end

/-- The fully faithful inclusion of CGWH spaces into compactly generated
spaces. -/
def cgwhToCompactlyGenerated :
    CGWH.{u, v} ⥤ CompactlyGenerated.{u, v} :=
  inducedFunctor CGWH.toCompactlyGenerated

/-- The inclusion into compactly generated spaces is fully faithful. -/
def fullyFaithfulCgwhToCompactlyGenerated :
    cgwhToCompactlyGenerated.{u, v}.FullyFaithful :=
  fullyFaithfulInducedFunctor CGWH.toCompactlyGenerated

instance : cgwhToCompactlyGenerated.{u, v}.Full :=
  fullyFaithfulCgwhToCompactlyGenerated.full

instance : cgwhToCompactlyGenerated.{u, v}.Faithful :=
  fullyFaithfulCgwhToCompactlyGenerated.faithful

/-- The fully faithful inclusion of CGWH spaces into topological spaces. -/
abbrev cgwhToTop : CGWH.{u, v} ⥤ TopCat.{v} :=
  cgwhToCompactlyGenerated ⋙
    CompactlyGenerated.compactlyGeneratedToTop

/-- The inclusion of CGWH spaces into topological spaces is fully faithful. -/
def fullyFaithfulCgwhToTop : cgwhToTop.{u, v}.FullyFaithful :=
  fullyFaithfulCgwhToCompactlyGenerated.comp
    CompactlyGenerated.fullyFaithfulCompactlyGeneratedToTop

/-- Construct a CGWH isomorphism from a homeomorphism. -/
def isoOfHomeo {X Y : CGWH.{u, v}} (f : X ≃ₜ Y) : X ≅ Y where
  hom := ConcreteCategory.ofHom ⟨f, f.continuous⟩
  inv := ConcreteCategory.ofHom ⟨f.symm, f.symm.continuous⟩
  hom_inv_id := by
    ext x
    exact f.symm_apply_apply x
  inv_hom_id := by
    ext x
    exact f.apply_symm_apply x

/-- Construct a homeomorphism from a CGWH isomorphism. -/
def homeoOfIso {X Y : CGWH.{u, v}} (f : X ≅ Y) : X ≃ₜ Y where
  toFun := f.hom
  invFun := f.inv
  left_inv := f.hom_inv_id_apply
  right_inv := f.inv_hom_id_apply
  continuous_toFun := (ConcreteCategory.hom f.hom).continuous
  continuous_invFun := (ConcreteCategory.hom f.inv).continuous

/-- CGWH isomorphisms are equivalent to homeomorphisms of their underlying
spaces. -/
def isoEquivHomeo {X Y : CGWH.{u, v}} : (X ≅ Y) ≃ (X ≃ₜ Y) where
  toFun := homeoOfIso
  invFun := isoOfHomeo
  left_inv f := by
    ext x
    rfl
  right_inv f := by
    ext x
    rfl

end CGWH
