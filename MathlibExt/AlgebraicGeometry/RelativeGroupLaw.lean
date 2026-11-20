/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicGeometry_RelativeGroupLaw.lean`,
`Definitions/Def_AlgebraicGeometry_RelativeGroupLawGrpObj.lean`,
`Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_grpObj_eq.lean`
and
`P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_grpObj_eq.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Relative group laws on schemes

A relative group law on a scheme over a base assigns a group law to the
points of the scheme over every test scheme, naturally in the test scheme.
Such a law determines a group object in the category of schemes over the
base, and its multiplication, unit and inverse agree with the given law on
all test schemes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory

open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes over a common base: a morphism `φ : Y ⟶ X` with
`φ ≫ f = g`. -/
abbrev SchemeHomOver {B Y X : Scheme.{u}} (g : Y ⟶ B) (f : X ⟶ B) :=
  { φ : Y ⟶ X // φ ≫ f = g }

/-- The morphism of schemes over the base determined by a morphism in the
over category. -/
def overHomToSchemeHomOver {B Y X : Scheme.{u}} {g : Y ⟶ B} {f : X ⟶ B}
    (h : Over.mk g ⟶ Over.mk f) : SchemeHomOver g f :=
  ⟨h.left, by simpa using Over.w h⟩

@[simp]
theorem overHomToSchemeHomOver_coe {B Y X : Scheme.{u}} {g : Y ⟶ B} {f : X ⟶ B}
    (h : Over.mk g ⟶ Over.mk f) : (overHomToSchemeHomOver h).1 = h.left :=
  rfl

/-- The morphism in the over category determined by a morphism of schemes
over the base. -/
def schemeHomOverToOverHom {B Y X : Scheme.{u}} {g : Y ⟶ B} {f : X ⟶ B}
    (φ : SchemeHomOver g f) : Over.mk g ⟶ Over.mk f :=
  Over.homMk φ.1 (by simpa using φ.2)

@[simp]
theorem schemeHomOverToOverHom_left {B Y X : Scheme.{u}} {g : Y ⟶ B} {f : X ⟶ B}
    (φ : SchemeHomOver g f) : (schemeHomOverToOverHom φ).left = φ.1 :=
  rfl

@[simp]
theorem overHomToSchemeHomOver_schemeHomOverToOverHom {B Y X : Scheme.{u}}
    {g : Y ⟶ B} {f : X ⟶ B} (φ : SchemeHomOver g f) :
    overHomToSchemeHomOver (schemeHomOverToOverHom φ) = φ :=
  Subtype.ext (by simp)

@[simp]
theorem schemeHomOverToOverHom_overHomToSchemeHomOver {B Y X : Scheme.{u}}
    {g : Y ⟶ B} {f : X ⟶ B} (h : Over.mk g ⟶ Over.mk f) :
    schemeHomOverToOverHom (overHomToSchemeHomOver h) = h :=
  Over.OverMorphism.ext (by simp)

/-- Morphisms of schemes over a base are the same as morphisms in the over
category. -/
def schemeHomOverEquivOverHom {B Y X : Scheme.{u}} (g : Y ⟶ B) (f : X ⟶ B) :
    SchemeHomOver g f ≃ (Over.mk g ⟶ Over.mk f) where
  toFun := schemeHomOverToOverHom
  invFun := overHomToSchemeHomOver
  left_inv := overHomToSchemeHomOver_schemeHomOverToOverHom
  right_inv := schemeHomOverToOverHom_overHomToSchemeHomOver

/-- Precomposition of a morphism over the base with a morphism of test
schemes. -/
def schemeHomOverComp {B T' T A : Scheme.{u}} {t : T ⟶ B} {t' : T' ⟶ B} {f : A ⟶ B}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) : SchemeHomOver t' f :=
  ⟨ψ ≫ x.1, by rw [Category.assoc, x.2, hψ]⟩

@[simp]
theorem schemeHomOverComp_coe {B T' T A : Scheme.{u}} {t : T ⟶ B} {t' : T' ⟶ B}
    {f : A ⟶ B} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    (schemeHomOverComp ψ hψ x).1 = ψ ≫ x.1 :=
  rfl

/-- A group law on a scheme `A` over `Spec R`, given on the points over
every test scheme and natural in the test scheme. -/
structure RelativeGroupLaw (R : Type u) [CommRing R] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) where
  /-- Multiplication on points over a test scheme. -/
  mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
    SchemeHomOver t f → SchemeHomOver t f → SchemeHomOver t f
  /-- The identity point over a test scheme. -/
  one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), SchemeHomOver t f
  /-- Inversion on points over a test scheme. -/
  inv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
    SchemeHomOver t f → SchemeHomOver t f
  /-- Multiplication is associative. -/
  mul_assoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x y z : SchemeHomOver t f), mul t (mul t x y) z = mul t x (mul t y z)
  /-- The identity is a left unit. -/
  one_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
    mul t (one t) x = x
  /-- The identity is a right unit. -/
  mul_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
    mul t x (one t) = x
  /-- Inverses cancel on the left. -/
  inv_mul_cancel : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t f), mul t (inv t x) x = one t
  /-- Multiplication is natural in the test scheme. -/
  mul_natural : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x y : SchemeHomOver t f),
    schemeHomOverComp ψ hψ (mul t x y) =
      mul t' (schemeHomOverComp ψ hψ x) (schemeHomOverComp ψ hψ y)

namespace RelativeGroupLaw

/-- The group structure on points of a relative group law over a fixed test
scheme. -/
@[reducible]
def pointGroup {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Group (SchemeHomOver t f) where
  mul x y := G.mul t x y
  one := G.one t
  inv x := G.inv t x
  mul_assoc := G.mul_assoc t
  one_mul := G.one_mul t
  mul_one := G.mul_one t
  inv_mul_cancel := G.inv_mul_cancel t

theorem mul_inv_cancel {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    G.mul t x (G.inv t x) = G.one t := by
  calc G.mul t x (G.inv t x)
      = G.mul t (G.one t) (G.mul t x (G.inv t x)) := (G.one_mul t _).symm
    _ = G.mul t (G.mul t (G.inv t (G.inv t x)) (G.inv t x)) (G.mul t x (G.inv t x)) := by
        rw [G.inv_mul_cancel t (G.inv t x)]
    _ = G.mul t (G.inv t (G.inv t x)) (G.mul t (G.inv t x) (G.mul t x (G.inv t x))) := by
        rw [G.mul_assoc]
    _ = G.mul t (G.inv t (G.inv t x)) (G.mul t (G.mul t (G.inv t x) x) (G.inv t x)) := by
        rw [G.mul_assoc]
    _ = G.mul t (G.inv t (G.inv t x)) (G.mul t (G.one t) (G.inv t x)) := by
        rw [G.inv_mul_cancel]
    _ = G.mul t (G.inv t (G.inv t x)) (G.inv t x) := by rw [G.one_mul]
    _ = G.one t := G.inv_mul_cancel t (G.inv t x)

theorem one_natural {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    schemeHomOverComp ψ hψ (G.one t) = G.one t' := by
  have h : G.mul t' (schemeHomOverComp ψ hψ (G.one t))
        (schemeHomOverComp ψ hψ (G.one t)) =
      schemeHomOverComp ψ hψ (G.one t) := by
    rw [← G.mul_natural t t' ψ hψ, G.one_mul]
  calc schemeHomOverComp ψ hψ (G.one t)
      = G.mul t' (G.one t') (schemeHomOverComp ψ hψ (G.one t)) := (G.one_mul t' _).symm
    _ = G.mul t' (G.mul t' (G.inv t' (schemeHomOverComp ψ hψ (G.one t)))
          (schemeHomOverComp ψ hψ (G.one t))) (schemeHomOverComp ψ hψ (G.one t)) := by
        rw [G.inv_mul_cancel]
    _ = G.mul t' (G.inv t' (schemeHomOverComp ψ hψ (G.one t)))
          (G.mul t' (schemeHomOverComp ψ hψ (G.one t))
            (schemeHomOverComp ψ hψ (G.one t))) := by
        rw [G.mul_assoc]
    _ = G.mul t' (G.inv t' (schemeHomOverComp ψ hψ (G.one t)))
          (schemeHomOverComp ψ hψ (G.one t)) := by rw [h]
    _ = G.one t' := G.inv_mul_cancel t' _

end RelativeGroupLaw

namespace RelativeGroupLaw

/-- The presheaf of groups on schemes over the base given by the points
of a relative group law. -/
noncomputable def yonedaGrpObjPresheaf {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) :
    (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ GrpCat.{u} where
  obj T := @GrpCat.of (SchemeHomOver T.unop.hom f) (G.pointGroup T.unop.hom)
  map {S T} χ :=
    letI := G.pointGroup S.unop.hom
    letI := G.pointGroup T.unop.hom
    GrpCat.ofHom
      { toFun := fun x => schemeHomOverComp χ.unop.left (Over.w χ.unop) x
        map_one' := G.one_natural _ _ _ _
        map_mul' := fun x y => G.mul_natural _ _ _ _ x y }
  map_id S := by
    letI := G.pointGroup S.unop.hom
    refine GrpCat.hom_ext (MonoidHom.ext fun x => Subtype.ext ?_)
    simp
  map_comp {S T U} χ χ' := by
    letI := G.pointGroup S.unop.hom
    letI := G.pointGroup T.unop.hom
    letI := G.pointGroup U.unop.hom
    refine GrpCat.hom_ext (MonoidHom.ext fun x => Subtype.ext ?_)
    simp

/-- Morphisms in the over category are the same as morphisms of schemes
over the base. -/
noncomputable def overHomEquivSchemeHomOver {R : Type u} [CommRing R] {A : Scheme.{u}}
    (T : Over (Spec (CommRingCat.of R))) (f : A ⟶ Spec (CommRingCat.of R)) :
    (T ⟶ Over.mk f) ≃ SchemeHomOver T.hom f where
  toFun φ := ⟨φ.left, by simpa using Over.w φ⟩
  invFun x := Over.homMk x.1 (by simpa using x.2)
  left_inv φ := Over.OverMorphism.ext (by simp)
  right_inv x := Subtype.ext (by simp)

/-- The presheaf of groups of a relative group law is represented by the
scheme over the base. -/
noncomputable def overMkRepresentableBy {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) :
    (G.yonedaGrpObjPresheaf ⋙ forget GrpCat).RepresentableBy (Over.mk f) where
  homEquiv {T} := overHomEquivSchemeHomOver T f
  homEquiv_comp _ _ := Subtype.ext rfl

/-- The group object in schemes over the base determined by a relative
group law. -/
@[reducible]
noncomputable def grpObjOverMk {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) :
    GrpObj (Over.mk f) :=
  GrpObj.ofRepresentableBy (Over.mk f) G.yonedaGrpObjPresheaf G.overMkRepresentableBy

theorem overHomToSchemeHomOver_mul {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (a b : Over.mk t ⟶ Over.mk f) :
    letI := G.grpObjOverMk
    overHomToSchemeHomOver (a * b) =
      G.mul t (overHomToSchemeHomOver a) (overHomToSchemeHomOver b) := by
  letI := G.grpObjOverMk
  exact ((yonedaGrpObjIsoOfRepresentableBy (Over.mk f) G.yonedaGrpObjPresheaf
    G.overMkRepresentableBy).hom.app (Opposite.op (Over.mk t))).hom.map_mul a b

theorem overHomToSchemeHomOver_one {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    letI := G.grpObjOverMk
    overHomToSchemeHomOver (1 : Over.mk t ⟶ Over.mk f) = G.one t := by
  letI := G.grpObjOverMk
  exact ((yonedaGrpObjIsoOfRepresentableBy (Over.mk f) G.yonedaGrpObjPresheaf
    G.overMkRepresentableBy).hom.app (Opposite.op (Over.mk t))).hom.map_one

theorem overHomToSchemeHomOver_inv {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (a : Over.mk t ⟶ Over.mk f) :
    letI := G.grpObjOverMk
    overHomToSchemeHomOver a⁻¹ = G.inv t (overHomToSchemeHomOver a) := by
  letI := G.grpObjOverMk
  letI := G.pointGroup t
  exact map_inv ((yonedaGrpObjIsoOfRepresentableBy (Over.mk f) G.yonedaGrpObjPresheaf
    G.overMkRepresentableBy).hom.app (Opposite.op (Over.mk t))).hom a

/-- A relative group law determines a group object in schemes over the base
whose multiplication, identity and inverse match the law on all test
schemes. -/
theorem exists_grpObj_eq {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) :
    ∃ g : GrpObj (Over.mk f),
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (a b : Over.mk t ⟶ Over.mk f),
        overHomToSchemeHomOver (lift a b ≫ g.mul) =
          G.mul t (overHomToSchemeHomOver a) (overHomToSchemeHomOver b)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
        overHomToSchemeHomOver (toUnit (Over.mk t) ≫ g.one) = G.one t) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (a : Over.mk t ⟶ Over.mk f),
        overHomToSchemeHomOver (a ≫ g.inv) = G.inv t (overHomToSchemeHomOver a)) :=
  ⟨G.grpObjOverMk, fun t a b => G.overHomToSchemeHomOver_mul t a b,
    fun t => G.overHomToSchemeHomOver_one t, fun t a => G.overHomToSchemeHomOver_inv t a⟩

end RelativeGroupLaw

end AlgebraicGeometry
