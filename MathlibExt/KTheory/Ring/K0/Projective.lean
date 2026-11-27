/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.Pseudofunctor
public import MathlibExt.KTheory.Exact.K0.MapRing
public import Mathlib.Algebra.Category.Ring.Basic

/-!
# Projective-module `K₀` as a ring-valued functor

`RingK0 R` is `K₀` of `FGProjectiveCat R`, the split exact category of finitely
generated projective `R`-modules. For commutative rings, extension of scalars
gives a functor `CommRingCat ⥤ CommRingCat`, and `addCommGrpFunctor` is its
forgetful image to `AddCommGrpCat`.

## Main definitions
* `AlgebraicKTheory.RingK0`
* `AlgebraicKTheory.RingK0.functor`
* `AlgebraicKTheory.RingK0.addCommGrpFunctor`
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicKTheory

/-- `K₀` of `FGProjectiveCat R`. Lives in `Type (u + 1)`. -/
abbrev RingK0 (R : Type u) [Ring R] : Type (u + 1) :=
  K0 (FGProjectiveCat.{u} R)

namespace RingK0

/-- Ring-valued `K₀` functor for commutative rings via base change. -/
noncomputable def functor : CommRingCat.{u} ⥤ CommRingCat.{u + 1} where
  obj R := CommRingCat.of (RingK0 (R : Type u))
  map {R S} f := CommRingCat.ofHom (K0.mapRing (FGProjectiveCat.baseChange f.hom))
  map_id R := by
    calc
      CommRingCat.ofHom (K0.mapRing (FGProjectiveCat.baseChange (𝟙 R : R ⟶ R).hom))
          = CommRingCat.ofHom
              (K0.mapRing (FGProjectiveCat.baseChange (RingHom.id (R : Type u)))) := by
            rw [CommRingCat.hom_id]
      _ = CommRingCat.ofHom (K0.mapRing (𝟭 (FGProjectiveCat.{u} (R : Type u)))) := by
            rw [K0.mapRing_eq_of_iso (FGProjectiveCat.baseChangeId (R : Type u))]
      _ = CommRingCat.ofHom (RingHom.id (RingK0 (R : Type u))) := by
            rw [K0.mapRing_id]
      _ = 𝟙 (CommRingCat.of (RingK0 (R : Type u))) := by
            rw [CommRingCat.ofHom_id]
  map_comp {R S T} f g := by
    have hfg : (f ≫ g).hom = g.hom.comp f.hom := CommRingCat.hom_comp f g
    calc
      CommRingCat.ofHom (K0.mapRing (FGProjectiveCat.baseChange (f ≫ g).hom))
          = CommRingCat.ofHom
              (K0.mapRing (FGProjectiveCat.baseChange (g.hom.comp f.hom))) := by
            rw [hfg]
      _ = CommRingCat.ofHom
            (K0.mapRing (FGProjectiveCat.baseChange f.hom ⋙ FGProjectiveCat.baseChange g.hom)) := by
            rw [K0.mapRing_eq_of_iso (FGProjectiveCat.baseChangeComp f.hom g.hom)]
      _ = CommRingCat.ofHom
            ((K0.mapRing (FGProjectiveCat.baseChange g.hom)).comp
              (K0.mapRing (FGProjectiveCat.baseChange f.hom))) := by
            rw [K0.mapRing_comp]
      _ = CommRingCat.ofHom (K0.mapRing (FGProjectiveCat.baseChange f.hom)) ≫
            CommRingCat.ofHom (K0.mapRing (FGProjectiveCat.baseChange g.hom)) := by
            rw [CommRingCat.ofHom_comp]
      _ = (CommRingCat.ofHom (K0.mapRing (FGProjectiveCat.baseChange f.hom))) ≫
            (CommRingCat.ofHom (K0.mapRing (FGProjectiveCat.baseChange g.hom))) := rfl

/-- Additive view of `RingK0.functor` via forgetful functors. -/
noncomputable def addCommGrpFunctor : CommRingCat.{u} ⥤ AddCommGrpCat.{u + 1} :=
  functor ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat

@[simp]
lemma functor_obj (R : CommRingCat.{u}) :
    functor.obj R = CommRingCat.of (RingK0 (R : Type u)) :=
  rfl

@[simp]
lemma functor_map_hom {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (functor.map f).hom = K0.mapRing (FGProjectiveCat.baseChange f.hom) :=
  rfl

/-- Action of `functor` on a generator `[M]` via extension of scalars. -/
@[simp]
lemma functor_map_mk {R S : CommRingCat.{u}} (f : R ⟶ S)
    (M : FGProjectiveCat.{u} (R : Type u)) :
    (functor.map f) (K0.mk M) = K0.mk ((FGProjectiveCat.baseChange f.hom).obj M) := by
  change K0.map (FGProjectiveCat.baseChange f.hom) (K0.mk M) =
    K0.mk ((FGProjectiveCat.baseChange f.hom).obj M)
  rw [K0.map_mk]

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- The map on projective-module `K₀` induced by a commutative-ring
homomorphism. -/
noncomputable def mapRingHom (f : R →+* S) : RingK0 R →+* RingK0 S :=
  (functor.map (CommRingCat.ofHom f)).hom

/-- A commutative-ring homomorphism acts on `K₀` generators by extension of
scalars. -/
@[simp]
theorem mapRingHom_mk (f : R →+* S) (M : FGProjectiveCat.{u} R) :
    mapRingHom f (K0.mk M) =
      K0.mk ((FGProjectiveCat.baseChange f).obj M) :=
  functor_map_mk (CommRingCat.ofHom f) M

/-- The identity ring homomorphism induces the identity on projective-module
`K₀`. -/
@[simp]
theorem mapRingHom_id (R : Type u) [CommRing R] :
    mapRingHom (RingHom.id R) = RingHom.id (RingK0 R) := by
  change (functor.map (CommRingCat.ofHom (RingHom.id R))).hom = _
  rw [CommRingCat.ofHom_id, functor.map_id]
  rfl

/-- Maps on projective-module `K₀` respect composition. -/
theorem mapRingHom_comp (f : R →+* S) (g : S →+* T) :
    mapRingHom (g.comp f) = (mapRingHom g).comp (mapRingHom f) := by
  change (functor.map (CommRingCat.ofHom (g.comp f))).hom = _
  rw [CommRingCat.ofHom_comp, functor.map_comp]
  rfl

end RingK0

end AlgebraicKTheory
