/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.PerfectDGModuleModels
public import MathlibExt.CategoryTheory.DGAlgebraCategoryModels

/-!
# Derived scalar extension on the actual DG modules

Restriction is literal precomposition with the opposite DG functor.
Its enrichment is fixed on every homogeneous natural-transformation
component. Scalar extension takes cofibrant modules to cofibrant modules
and is normalized by the enriched adjunction against every raw target
module. The adjunction map is restriction followed by the displayed unit.

No DG functorial projective resolution is requested over an arbitrary
ground ring. Raw target modules are fibrant in the component-surjective
projective model. The enhanced Hom adjunction therefore expresses the
derived scalar extension on the actual cofibrant source objects.
Perfect objects remain the genuine localized retracts of native finite
cells, and perfection preservation is a separate theorem request.

References: Keller, Deriving DG categories, §6; Toën,
arXiv:math/0408337v7, §3; Toën--Vaquié, arXiv:math/0503269v5, §2.2.
Native enrichment, modules, finite cells and localizations use the
completed Apache-attributed DGSource and DGSourceMore ports.
-/

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.DGScalarExtensionModels

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.PerfectDGModuleModels
open MathlibExt.Algebra.Homology
open MathlibExt.CategoryTheory.DGAlgebraCategoryModels

universe u

variable {k : Type u} [CommRing k]

/-- A native DG-algebra map gives its literal one-object DG functor. -/
def algebraFunctor {A B : DGAlgebra k} (f : A ⟶ B) :
    algebraCategory A ⟶ algebraCategory B where
  obj _ := PUnit.unit
  map _ _ := f.hom
  map_id _ := IsMonHom.one_hom f.hom
  map_comp _ _ _ := IsMonHom.mul_hom f.hom

/-- The actual right-module restriction, retaining all module-action maps. -/
def restrictModule {C D : DGCat k} (f : C ⟶ D) (M : RightModule k D) :
    RightModule k C :=
  ⟨(EnrichedFunctor.op (V := Cochains k) f).comp (Cochains k) M.toEnrichedFunctor⟩

/-- Restriction evaluates at the specified DG image in every module degree. -/
theorem restrictModule_value {C D : DGCat k} (f : C ⟶ D)
    (M : RightModule k D) (x : Cᵒᵖ) :
    (restrictModule f M).toEnrichedFunctor.obj x =
      M.toEnrichedFunctor.obj (op (f.obj x.unop)) := rfl

/-- A restriction enrichment is constrained on all homogeneous components.
The heterogeneous equality transports only the displayed object equalities. -/
structure RestrictionModel {C D : DGCat k} (f : C ⟶ D) where
  functor : EnrichedFunctor (Cochains k) (RightModule k D) (RightModule k C)
  object_eq : ∀ M : RightModule k D, functor.obj M = restrictModule f M
  component_eq : ∀ (M N : RightModule k D) (n : ℤ) (a : DGHom k n M N) (x : Cᵒᵖ),
    HEq (DGFunctor.dgApp k n x (functor.dgMap n a))
      (DGFunctor.dgApp k n (op (f.obj x.unop)) a)

/-- Scalar extension on cofibrant modules, normalized by its full enriched
adjunction with the fixed raw restriction. Every Hom degree is retained. -/
structure ExtensionModel {C D : DGCat k} (f : C ⟶ D) (R : RestrictionModel f) where
  functor : EnrichedFunctor (Cochains k) (DGDerivedModules k C) (DGDerivedModules k D)
  unit : ∀ M : DGDerivedModules k C,
    DGHom k 0 M.obj (R.functor.obj (functor.obj M).obj)
  unit_closed : ∀ M : DGDerivedModules k C, dgDifferential k 0 (unit M) = 0
  homIso : ∀ (M : DGDerivedModules k C) (N : RightModule k D),
    dgHomComplex k (functor.obj M).obj N ≅ dgHomComplex k M.obj (R.functor.obj N)
  hom_formula : ∀ (M : DGDerivedModules k C) (N : RightModule k D) (n : ℤ)
    (a : DGHom k n (functor.obj M).obj N),
    ((homIso M N).hom.f n) a =
      dgComp k (unit M) (R.functor.dgMap n a) (by omega)
  target_naturality : ∀ (M : DGDerivedModules k C) (N P : RightModule k D)
    (p q r : ℤ) (a : DGHom k p (functor.obj M).obj N) (b : DGHom k q N P)
    (h : p + q = r),
    ((homIso M P).hom.f r) (dgComp k a b h) =
      dgComp k (((homIso M N).hom.f p) a) (R.functor.dgMap q b) h
  source_naturality : ∀ (M N : DGDerivedModules k C) (P : RightModule k D)
    (p q r : ℤ) (a : DGHom k p M N) (b : DGHom k q (functor.obj N).obj P)
    (h : p + q = r),
    ((homIso M P).hom.f r) (dgComp k (functor.dgMap p a) b h) =
      dgComp k (X := M.obj) (Y := N.obj) (Z := R.functor.obj P)
        a (((homIso N P).hom.f q) b) h

/-- Actual perfection preservation for this normalized extension. -/
def PreservesPerfect {C D : DGCat k} {f : C ⟶ D} {R : RestrictionModel f}
    (L : ExtensionModel f R) : Prop :=
  ∀ M : DGDerivedModules k C,
    IsPerfectModule C M.obj → IsPerfectModule D (L.functor.obj M).obj

/-- The native inclusion of Perf into cofibrant modules. It retains every Hom. -/
def perfectToCofibrant (C : DGCat k) :
    EnrichedFunctor (Cochains k) (PerfectDGCategory C) (DGDerivedModules k C) where
  obj M := ⟨M.obj, M.property.1⟩
  map _ _ := 𝟙 _

/-- The actual enriched scalar extension of perfect objects. -/
def perfectExtension {C D : DGCat k} {f : C ⟶ D} {R : RestrictionModel f}
    (L : ExtensionModel f R) (h : PreservesPerfect L) :
    EnrichedFunctor (Cochains k) (PerfectDGCategory C) (PerfectDGCategory D) where
  obj M :=
    let N := L.functor.obj ((perfectToCofibrant C).obj M)
    ⟨N.obj, N.property, h ((perfectToCofibrant C).obj M) M.property.2⟩
  map M N := L.functor.map ((perfectToCofibrant C).obj M) ((perfectToCofibrant C).obj N)
  map_id M := L.functor.map_id ((perfectToCofibrant C).obj M)
  map_comp M N P := L.functor.map_comp ((perfectToCofibrant C).obj M)
    ((perfectToCofibrant C).obj N) ((perfectToCofibrant C).obj P)

/-- Every perfect extension object is the actual output of the same scalar functor. -/
theorem perfectExtension_object {C D : DGCat k} {f : C ⟶ D} {R : RestrictionModel f}
    (L : ExtensionModel f R) (h : PreservesPerfect L) (M : PerfectDGCategory C) :
    ((perfectExtension L h).obj M).obj =
      (L.functor.obj ((perfectToCofibrant C).obj M)).obj := rfl

end MathlibExt.CategoryTheory.DGScalarExtensionModels
