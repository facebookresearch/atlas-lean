/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import MathlibExt.CategoryTheory.DGQuasiFunctorModels

/-!
# Scalar-changing DG module restriction and extension contracts

The coefficient map is an actual ring homomorphism. The Hom objects are
the complete native cochain Hom complexes, with scalar restriction in
every degree. Module restriction is fixed on every value, action and
homogeneous natural-transformation component. Extension is normalized
by the full Hom-complex adjunction against every raw target module and
its actual closed unit.

These contracts permit geometric coefficient changes between different
plus rings. They do not select an unrelated functor and call it scalar
extension, or replace DG modules by their degree-zero homotopy category.
Construction of the displayed models is separate deferred work.

References: Keller, Deriving DG categories, Section 6; Toën,
arXiv:math/0408337v7, Section 3; Anschuetz--Mann,
arXiv:2403.01951v2, Sections 2.1--2.2.
-/

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.SemilinearDGModuleRestrictions

open _root_.CategoryTheory _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open CochainComplex.HomComplex

universe u v

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)

/-- Literal scalar restriction of every module term and differential. -/
def restrictCochains : CochainComplex (ModuleCat.{u} B) ℤ ⥤
    CochainComplex (ModuleCat.{u} A) ℤ :=
  (ModuleCat.restrictScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)

/-- A DG functor whose homogeneous maps use the specified coefficient map. -/
structure SemilinearFunctor (C D : Type v) [DGCategory A C] [DGCategory B D] where
  obj : C → D
  map : ∀ X Y : C, dgHomComplex A X Y ⟶
    (restrictCochains φ).obj (dgHomComplex B (obj X) (obj Y))
  identity : ∀ X, ((map X X).f 0) (dgId A X) = dgId B (obj X)
  composition : ∀ (X Y Z : C) (p q r : ℤ)
    (a : DGHom A p X Y) (b : DGHom A q Y Z) (h : p + q = r),
    ((map X Z).f r) (dgComp A a b h) =
      dgComp B (((map X Y).f p) a) (((map Y Z).f q) b) h

/-- The literal action of a homogeneous arrow on one module component. -/
def moduleAction {R : Type u} [CommRing R] {C : Type u} [DGCategory R C]
    (M : RightModule R C) {x y : Cᵒᵖ} {n : ℤ} (a : DGHom R n x y)
    (q s : ℤ) (h : q + n = s) :
    (M.toEnrichedFunctor.obj x).X q → (M.toEnrichedFunctor.obj y).X s :=
  fun z ↦ ((M.toEnrichedFunctor.dgMap n a :
    Cochain (M.toEnrichedFunctor.obj x) (M.toEnrichedFunctor.obj y) n).v q s h).hom z

/-- The actual homogeneous component of a DG module natural transformation. -/
def moduleHomComponent {R : Type u} [CommRing R] {C : Type u} [DGCategory R C]
    {M N : RightModule R C} {n : ℤ} (a : DGHom R n M N) (x : Cᵒᵖ)
    (q s : ℤ) (h : q + n = s) :
    (M.toEnrichedFunctor.obj x).X q → (N.toEnrichedFunctor.obj x).X s :=
  fun z ↦ ((DGFunctor.dgApp R n x a :
    Cochain (M.toEnrichedFunctor.obj x) (N.toEnrichedFunctor.obj x) n).v q s h).hom z

/-- The native homogeneous zero-cycle represented by a module morphism. -/
def closedModuleHom {R : Type u} [CommRing R] {C : Type u} [DGCategory R C]
    {M N : RightModule R C} (f : M ⟶ N) : DGHom R 0 M N :=
  (DGFunctor.homEquivDGCycles R M N f).val

variable {C D : Type u} [DGCategory A C] [DGCategory B D]

/-- Restriction is fixed by precomposition and scalar restriction on all values/actions. -/
structure RestrictionModel (F : SemilinearFunctor φ Cᵒᵖ Dᵒᵖ) where
  functor : RightModule B D ⥤ RightModule A C
  value : ∀ (M : RightModule B D) (x : Cᵒᵖ),
    (functor.obj M).toEnrichedFunctor.obj x ≅
      (restrictCochains φ).obj (M.toEnrichedFunctor.obj (F.obj x))
  action : ∀ (M : RightModule B D) (x y : Cᵒᵖ) (n q s : ℤ)
    (a : DGHom A n x y) (h : q + n = s)
    (z : ((functor.obj M).toEnrichedFunctor.obj x).X q),
    ((value M y).hom.f s) (moduleAction (functor.obj M) a q s h z) =
      moduleAction M (((F.map x y).f n) a) q s h (((value M x).hom.f q) z)
  homMap : ∀ M N : RightModule B D,
    (restrictCochains φ).obj (dgHomComplex B M N) ⟶
      dgHomComplex A (functor.obj M) (functor.obj N)
  hom_components : ∀ (M N : RightModule B D) (n : ℤ) (a : DGHom B n M N)
    (x : Cᵒᵖ) (q s : ℤ) (h : q + n = s)
    (z : ((functor.obj M).toEnrichedFunctor.obj x).X q),
    ((value N x).hom.f s)
      (moduleHomComponent (((homMap M N).f n) a) x q s h z) =
      moduleHomComponent a (F.obj x) q s h (((value M x).hom.f q) z)
  map_closed : ∀ {M N : RightModule B D} (f : M ⟶ N),
    ((homMap M N).f 0) (closedModuleHom f) = closedModuleHom (functor.map f)

/-- Cofibrant scalar extension with the complete restricted Hom-complex adjunction. -/
structure ExtensionModel {F : SemilinearFunctor φ Cᵒᵖ Dᵒᵖ}
    (R : RestrictionModel φ F) where
  functor : SemilinearFunctor φ (DGDerivedModules A C) (DGDerivedModules B D)
  unit : ∀ M : DGDerivedModules A C,
    DGHom A 0 M.obj (R.functor.obj (functor.obj M).obj)
  unit_closed : ∀ M : DGDerivedModules A C, dgDifferential A 0 (unit M) = 0
  homIso : ∀ (M : DGDerivedModules A C) (N : RightModule B D),
    (restrictCochains φ).obj (dgHomComplex B (functor.obj M).obj N) ≅
      dgHomComplex A M.obj (R.functor.obj N)
  hom_formula : ∀ (M : DGDerivedModules A C) (N : RightModule B D)
    (n : ℤ) (a : DGHom B n (functor.obj M).obj N),
    ((homIso M N).hom.f n) a =
      dgComp A (unit M) (((R.homMap (functor.obj M).obj N).f n) a) (by omega)
  target_naturality : ∀ (M : DGDerivedModules A C) (N P : RightModule B D)
    (p q r : ℤ) (a : DGHom B p (functor.obj M).obj N)
    (b : DGHom B q N P) (h : p + q = r),
    ((homIso M P).hom.f r) (dgComp B a b h) =
      dgComp A (((homIso M N).hom.f p) a) (((R.homMap N P).f q) b) h
  source_naturality : ∀ (M N : DGDerivedModules A C) (P : RightModule B D)
    (p q r : ℤ) (a : DGHom A p M N) (b : DGHom B q (functor.obj N).obj P)
    (h : p + q = r),
    ((homIso M P).hom.f r) (dgComp B (((functor.map M N).f p) a) b h) =
      dgComp A (X := M.obj) (Y := N.obj) (Z := R.functor.obj P)
        a (((homIso N P).hom.f q) b) h

end MathlibExt.CategoryTheory.SemilinearDGModuleRestrictions
