/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.BoundedProjectiveDeterminants
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Normalized determinant transport for arbitrary bounded perfect presentations

Objects are actual bounded finite-projective cochain complexes. Arrows
are isomorphisms of their native derived objects. The determinant module
is the literal ordered alternating tensor already defined in MathlibExt;
transport agrees with the completed exterior/dual map on every strict
cochain isomorphism. Quasi-isomorphism transport and coherence remain
explicit construction requests, rather than two-term specializations.

References: Knudsen--Mumford, The projectivity of the moduli space of
stable curves I, Sections 1--2; Stacks Project, Tags 0FJW and 0FJX.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.BoundedDeterminantTransportModels

open CategoryTheory
open BoundedProjectiveDeterminants

attribute [local instance] HasDerivedCategory.standard

variable (R : Type) [CommRing R]

structure Presentation where
  complex : BoundedProjectiveDeterminants.Complex R

abbrev derivedObject (C : Presentation R) : DerivedCategory (ModuleCat.{0} R) :=
  DerivedCategory.Q.obj C.complex.cochain

instance : Category (Presentation R) where
  Hom C D := derivedObject R C ≅ derivedObject R D
  id C := Iso.refl (derivedObject R C)
  comp f g := f ≪≫ g
  id_comp f := Iso.refl_trans f
  comp_id f := Iso.trans_refl f
  assoc f g h := Iso.trans_assoc f g h

/-- A determinant functor on the actual derived-isomorphism category. -/
structure TransportSystem where
  map : ∀ (C D : Presentation R), (C ⟶ D) →
    (determinantObject R C.complex ≅ determinantObject R D.complex)
  identity : ∀ C, map C C (𝟙 C) = Iso.refl (determinantObject R C.complex)
  composition : ∀ (C D E : Presentation R) (f : C ⟶ D) (g : D ⟶ E),
    map C E (f ≫ g) = map C D f ≪≫ map D E g
  cochain_normalization : ∀ (C D : Presentation R) (e : C.complex.cochain ≅ D.complex.cochain),
    map C D (DerivedCategory.Q.mapIso e) = determinantIso R C.complex D.complex e

/-- The actual determinant object/map functor, once its normalized transport is supplied. -/
def determinantFunctor (S : TransportSystem R) : Presentation R ⥤ ModuleCat R where
  obj C := determinantObject R C.complex
  map f := (S.map _ _ f).hom
  map_id C := congrArg Iso.hom (S.identity C)
  map_comp f g := congrArg Iso.hom (S.composition _ _ _ f g)

end MathlibExt.AlgebraicGeometry.BoundedDeterminantTransportModels
