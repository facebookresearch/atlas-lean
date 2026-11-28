/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
# Scalar restriction of commutative algebras

Let `R : Type u` and `S : Type v` be commutative rings and `f : R →+* S`. Restriction of
scalars sends an `S`-algebra `A` of carrier universe `w` to the same commutative ring, with
`R`-algebra structure given by the composite `R → S → A`. It acts on algebra morphisms by
their same underlying ring maps.

Identity and composition ring maps have natural restriction comparisons. These comparisons
preserve the algebra elements, and forgetting commutativity recovers scalar restriction on
`AlgCat`. The ring and algebra-carrier universes are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w z

namespace CommAlgCat

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Let `R : Type u` and `S : Type v` be commutative rings, `f : R →+* S`, and `A : CommAlgCat.{w}
S`. The structure `restrictedAlgebra f A : Algebra R A` has structural map `R → A` equal to
`algebraMap S A ∘ f`, as defined by `Algebra.compHom A f`. -/
abbrev restrictedAlgebra (f : R →+* S) (A : CommAlgCat.{w} S) : Algebra R A :=
  Algebra.compHom A f

/-- For commutative rings `R : Type u`, `S : Type v`, and `f : R →+* S`, `restrictScalars f :
CommAlgCat.{w} S → CommAlgCat.{w} R` retains each algebra's carrier and ring operations and
uses the composite `R→S→A` action. Each morphism retains its underlying ring map. The carrier
universe `w` is independent of `u,v`. -/
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

/-- For commutative rings `R,S` and `f : R →+* S`, restriction of commutative algebras followed by
`CommAlgCat R → AlgCat R` equals forgetting commutativity first and then
`AlgCat.restrictScalars f`. This is equality of the two functors on algebras of the same
carrier universe `w`. -/
theorem restrictScalars_forget (f : R →+* S) :
    restrictScalars f ⋙ forget₂ (CommAlgCat.{w} R) (AlgCat.{w} R) =
      forget₂ (CommAlgCat.{w} S) (AlgCat.{w} S) ⋙ AlgCat.restrictScalars f := rfl

/-- For a commutative ring `R : Type u` and carrier universe `w`, `restrictScalars (RingHom.id R)
≅ 𝟭 (CommAlgCat.{w} R)`. The components identify the composite identity scalar action with the
given `R`-action and preserve all algebra elements. -/
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

/-- Let `R : Type u`, `S : Type v`, and `T : Type z` be commutative rings, with `f : R→+*S`, `g :
S→+*T`. On `T`-algebras of carrier universe `w`, `restrictScalars (g.comp f) ≅ restrictScalars
g ⋙ restrictScalars f`. The components preserve the algebra elements and identify the two
composite scalar actions. -/
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
