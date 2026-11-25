/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
# Original-carrier scalar restriction for commutative algebras

The native AlgCat restriction functor already constructs the original
composite algebra action. This owner restricts that functor to commutative
algebras; all carriers, ring operations and morphism values remain unchanged.
Its identity and composition comparisons are the native AlgCat comparisons.
No scalar-action engine or comparison certificate is supplied.

Ground rings and algebra carriers retain independent universes, without a
Small, flatness or extended-origin assumption.
The comparisons retain the native scalar actions on their bundled objects.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w z

namespace CommAlgCat

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The existing native composite action on the original algebra carrier. -/
abbrev restrictedAlgebra (f : R →+* S) (A : CommAlgCat.{w} S) : Algebra R A :=
  Algebra.compHom A f

/-- Restriction is the existing native AlgCat functor on original commutative algebras. -/
def restrictScalars (f : R →+* S) : CommAlgCat.{w} S ⥤ CommAlgCat.{w} R where
  obj A :=
    letI : Algebra R A := restrictedAlgebra f A
    CommAlgCat.of R A
  map {A B} g :=
    letI : Algebra R A := restrictedAlgebra f A
    letI : Algebra R B := restrictedAlgebra f B
    CommAlgCat.ofHom (((AlgCat.restrictScalars f).map
      ((forget₂ (CommAlgCat.{w} S) (AlgCat.{w} S)).map g)).hom)
  map_id A := by
    apply CommAlgCat.hom_ext
    ext a
    rfl
  map_comp g h := by
    apply CommAlgCat.hom_ext
    ext a
    rfl

theorem restrictScalars_obj_algebraMap (f : R →+* S) (A : CommAlgCat.{w} S) (r : R) :
    algebraMap R ((restrictScalars f).obj A) r = algebraMap S A (f r) := rfl

theorem restrictScalars_map_apply (f : R →+* S) {A B : CommAlgCat.{w} S}
    (g : A ⟶ B) (a : A) : ((restrictScalars f).map g).hom a = g.hom a := rfl

/-- Forgetting commutativity recovers the actual native restriction functor. -/
theorem restrictScalars_forget (f : R →+* S) :
    restrictScalars f ⋙ forget₂ (CommAlgCat.{w} R) (AlgCat.{w} R) =
      forget₂ (CommAlgCat.{w} S) (AlgCat.{w} S) ⋙ AlgCat.restrictScalars f := rfl

/-- Native identity restriction, lifted to original commutative algebras. -/
def restrictScalarsIdIso (R : Type u) [CommRing R] :
    restrictScalars.{u, u, w} (RingHom.id R) ≅ 𝟭 (CommAlgCat.{w} R) :=
  NatIso.ofComponents
    (fun A =>
      { hom := CommAlgCat.ofHom
          (((AlgCat.restrictScalarsId' (RingHom.id R) rfl).app
            ((forget₂ (CommAlgCat.{w} R) (AlgCat.{w} R)).obj A)).hom.hom)
        inv := CommAlgCat.ofHom
          (((AlgCat.restrictScalarsId' (RingHom.id R) rfl).app
            ((forget₂ (CommAlgCat.{w} R) (AlgCat.{w} R)).obj A)).inv.hom)
        hom_inv_id := by apply CommAlgCat.hom_ext; ext a; rfl
        inv_hom_id := by apply CommAlgCat.hom_ext; ext a; rfl })
    (by intro A B g; apply CommAlgCat.hom_ext; ext a; rfl)

variable {T : Type z} [CommRing T]

/-- Native composition restriction, lifted without replacing any carrier. -/
def restrictScalarsCompIso (f : R →+* S) (g : S →+* T) :
    restrictScalars.{u, z, w} (g.comp f) ≅
      restrictScalars.{v, z, w} g ⋙ restrictScalars.{u, v, w} f :=
  NatIso.ofComponents
    (fun A =>
      { hom := { hom' :=
          (((AlgCat.restrictScalarsComp' f g (g.comp f) rfl).app
            ((forget₂ (CommAlgCat.{w} T) (AlgCat.{w} T)).obj A)).hom.hom) }
        inv := { hom' :=
          (((AlgCat.restrictScalarsComp' f g (g.comp f) rfl).app
            ((forget₂ (CommAlgCat.{w} T) (AlgCat.{w} T)).obj A)).inv.hom) }
        hom_inv_id := by apply CommAlgCat.hom_ext; ext a; rfl
        inv_hom_id := by apply CommAlgCat.hom_ext; ext a; rfl })
    (by intro A B h; apply CommAlgCat.hom_ext; ext a; rfl)

end CommAlgCat

end
