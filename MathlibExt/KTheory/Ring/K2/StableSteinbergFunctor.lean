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

public import MathlibExt.KTheory.Ring.K2.StableSteinbergToElementary
public import MathlibExt.KTheory.Ring.StableElementary.Functor

/-! # Categorical packaging for the stable Steinberg group

Packages `St(R)` as a functor `RingCat ⥤ GrpCat` and the
Steinberg-to-elementary homomorphism as a natural transformation.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicKTheory

noncomputable section

/-! ## Stable Steinberg functor -/

/-- `R ↦ St(R)` as a functor `RingCat ⥤ GrpCat`. -/
noncomputable def StableSteinberg.functor : RingCat.{u} ⥤ GrpCat.{u} where
  obj R := GrpCat.of (StableSteinberg (R : Type u))
  map {R S} f := GrpCat.ofHom (StableSteinberg.mapRingHom f.hom)
  map_id R := by
    have h : (𝟙 R : R ⟶ R).hom = RingHom.id (R : Type u) := rfl
    rw [h, StableSteinberg.mapRingHom_id]
    rfl
  map_comp {R S T} f g := by
    have hfg : (f ≫ g).hom = g.hom.comp f.hom := rfl
    rw [hfg, StableSteinberg.mapRingHom_comp]
    rfl

@[simp]
lemma StableSteinberg.functor_obj (R : RingCat.{u}) :
    StableSteinberg.functor.obj R = GrpCat.of (StableSteinberg (R : Type u)) :=
  rfl

@[simp]
lemma StableSteinberg.functor_obj_of (R : Type u) [Ring R] :
    StableSteinberg.functor.obj (RingCat.of R) = GrpCat.of (StableSteinberg R) :=
  rfl

@[simp]
lemma StableSteinberg.functor_map {R S : RingCat.{u}} (f : R ⟶ S) :
    StableSteinberg.functor.map f = GrpCat.ofHom (StableSteinberg.mapRingHom f.hom) :=
  rfl

@[simp]
lemma StableSteinberg.functor_map_ofHom {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    StableSteinberg.functor.map (RingCat.ofHom f) = GrpCat.ofHom (StableSteinberg.mapRingHom f) :=
  rfl

/-! ## Natural transformation `St → E∞` -/

/-- Natural transformation `St ⥤ E∞` induced by `toStableE`. -/
noncomputable def StableSteinberg.toStableENat :
    StableSteinberg.functor.{u} ⟶ StableE.functor.{u} where
  app R := GrpCat.ofHom (StableSteinberg.toStableE (R := (R : Type u)))
  naturality {R S} f := by
    apply GrpCat.hom_ext
    ext x
    change StableSteinberg.toStableE (StableSteinberg.mapRingHom f.hom x) =
      StableE.mapRingHom f.hom (StableSteinberg.toStableE x)
    have h := StableSteinberg.toStableE_mapRingHom (R := (R : Type u)) (S := (S : Type u)) f.hom
    exact congrFun (congrArg DFunLike.coe h) x

@[simp]
lemma StableSteinberg.toStableENat_app (R : RingCat.{u}) :
    StableSteinberg.toStableENat.app R =
      GrpCat.ofHom (StableSteinberg.toStableE (R := (R : Type u))) :=
  rfl

@[simp]
lemma StableSteinberg.toStableENat_app_of (R : Type u) [Ring R] :
    StableSteinberg.toStableENat.app (RingCat.of R) =
      GrpCat.ofHom (StableSteinberg.toStableE (R := R)) :=
  rfl

@[simp]
lemma StableSteinberg.toStableENat_apply {R : Type u} [Ring R] (x : StableSteinberg R) :
    (StableSteinberg.toStableENat.app (RingCat.of R)).hom x =
      StableSteinberg.toStableE x :=
  rfl

end

end AlgebraicKTheory

end
