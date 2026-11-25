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

public import MathlibExt.KTheory.Ring.StableElementary.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.Ring.Basic

/-! # Categorical functor for the stable elementary subgroup

Packages the group-level `StableE` API as a functor `RingCat ⥤ GrpCat`
and provides its natural inclusion into the ring-restricted `StableGL`
functor.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicKTheory

noncomputable section

/-! ## Ring-restricted stable general linear functor -/

/-- Ring-restricted stable general linear group functor,
definitionally `forget₂ RingCat SemiRingCat ⋙ StableGL.functor`. -/
noncomputable def StableGL.ringFunctor : RingCat.{u} ⥤ GrpCat.{u} :=
  forget₂ RingCat SemiRingCat ⋙ StableGL.functor

@[simp]
lemma StableGL.ringFunctor_obj (R : RingCat.{u}) :
    StableGL.ringFunctor.obj R = GrpCat.of (StableGL (R : Type u)) :=
  rfl

@[simp]
lemma StableGL.ringFunctor_obj_of (R : Type u) [Ring R] :
    StableGL.ringFunctor.obj (RingCat.of R) = GrpCat.of (StableGL R) :=
  rfl

@[simp]
lemma StableGL.ringFunctor_map {R S : RingCat.{u}} (f : R ⟶ S) :
    StableGL.ringFunctor.map f = StableGL.functor.map (SemiRingCat.ofHom f.hom) :=
  rfl

@[simp]
lemma StableGL.ringFunctor_map_ofHom {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    StableGL.ringFunctor.map (RingCat.ofHom f) = StableGL.functor.map (SemiRingCat.ofHom f) :=
  rfl

/-! ## Stable elementary functor -/

/-- `R ↦ E∞(R)` as a functor `RingCat ⥤ GrpCat`. -/
noncomputable def StableE.functor : RingCat.{u} ⥤ GrpCat.{u} where
  obj R := GrpCat.of (StableE (R : Type u))
  map {R S} f := GrpCat.ofHom (StableE.mapRingHom f.hom)
  map_id R := by
    have h : (𝟙 R : R ⟶ R).hom = RingHom.id (R : Type u) := rfl
    rw [h, StableE.mapRingHom_id]
    rfl
  map_comp {R S T} f g := by
    have hfg : (f ≫ g).hom = g.hom.comp f.hom := rfl
    rw [hfg, StableE.mapRingHom_comp]
    rfl

@[simp]
lemma StableE.functor_obj (R : RingCat.{u}) :
    StableE.functor.obj R = GrpCat.of (StableE (R : Type u)) :=
  rfl

@[simp]
lemma StableE.functor_obj_of (R : Type u) [Ring R] :
    StableE.functor.obj (RingCat.of R) = GrpCat.of (StableE R) :=
  rfl

@[simp]
lemma StableE.functor_map {R S : RingCat.{u}} (f : R ⟶ S) :
    StableE.functor.map f = GrpCat.ofHom (StableE.mapRingHom f.hom) :=
  rfl

@[simp]
lemma StableE.functor_map_ofHom {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    StableE.functor.map (RingCat.ofHom f) = GrpCat.ofHom (StableE.mapRingHom f) :=
  rfl

/-! ## Natural inclusion `E∞ → GL∞` -/

/-- Natural inclusion of the stable elementary functor into the
ring-restricted stable general linear functor. -/
noncomputable def StableE.inclusion :
    StableE.functor.{u} ⟶ StableGL.ringFunctor.{u} where
  app R := GrpCat.ofHom (stableElementarySubgroup (R : Type u)).subtype
  naturality {R S} f := by
    apply GrpCat.hom_ext
    ext x
    change (StableGL.functor.map (SemiRingCat.ofHom f.hom)).hom
        ((stableElementarySubgroup (R : Type u)).subtype x) =
      (stableElementarySubgroup (S : Type u)).subtype
        (StableE.mapRingHom f.hom x)
    exact (StableE.coe_mapRingHom (R := (R : Type u)) (S := (S : Type u)) f.hom x).symm

@[simp]
lemma StableE.inclusion_app (R : RingCat.{u}) :
    StableE.inclusion.app R =
      GrpCat.ofHom (stableElementarySubgroup (R : Type u)).subtype :=
  rfl

@[simp]
lemma StableE.inclusion_app_of (R : Type u) [Ring R] :
    StableE.inclusion.app (RingCat.of R) =
      GrpCat.ofHom (stableElementarySubgroup R).subtype :=
  rfl

@[simp]
lemma StableE.inclusion_apply {R : Type u} [Ring R] (x : StableE R) :
    (StableE.inclusion.app (RingCat.of R)).hom x = (x : StableGL R) :=
  rfl

end

end AlgebraicKTheory

end
