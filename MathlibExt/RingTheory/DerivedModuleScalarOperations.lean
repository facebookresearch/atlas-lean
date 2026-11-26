/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Localization.Prod
public import MathlibExt.RingTheory.DerivedAdicCompleteness

/-!
# Fixed derived scalar extension, tensor and completion operations

Scalar extension and tensor are the Kan-derived functors of the actual
degreewise extension and total cochain tensor sources. Their existence
assumptions name those fixed sources; no arbitrary functor is called a
derived tensor product.

A completion model is a reflector onto the actual localization-Hom
complete objects, with unit-precomposition as its universal map.
Completion existence and generic derived existence are already public
source theory, not new prismatic comparison conclusions. These explicit
inputs permit integration without changing their carriers.

References: Stacks Project, Tags 06Y0, 091S and 091Z;
AxiomMath/Stacks revision
`c496df0d9beea9deaeabcea8492605f9a0a2313b`,
`StacksFrontier/Homology/DerivedComplete/TriangulatedReflection.lean`
and `StacksFrontier/Algebra/Homology/KFlat.lean` (Apache 2.0).
The constructors below are original adapters to native Mathlib sources.
-/

@[expose] public noncomputable section

namespace MathlibExt.RingTheory.DerivedModuleScalarOperations

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open DerivedAdicCompleteness
open scoped TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A]

abbrev Modules := ModuleCat.{u + 1} A
abbrev Cochains := CochainComplex (Modules A) ℤ
abbrev D := DerivedCategory (Modules A)

/-- The fixed quasi-isomorphisms of actual module complexes. -/
abbrev quasiIso : MorphismProperty (Cochains A) :=
  HomologicalComplex.quasiIso (Modules A) (ComplexShape.up ℤ)

variable {A} {B : Type u} [CommRing B]

/-- The actual degreewise scalar-extension source, followed by Q. -/
def extensionSource (f : A →+* B) : Cochains A ⥤ D B :=
  letI : (ModuleCat.extendScalars.{u, u, u + 1} f).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} f).isLeftAdjoint
  (ModuleCat.extendScalars.{u, u, u + 1} f).mapHomologicalComplex
    (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q

/-- Existence of the left-derived functor of this specified source. -/
class HasExtension (f : A →+* B) : Prop where
  exists_derived : (extensionSource f).HasLeftDerivedFunctor (quasiIso A)

attribute [instance] HasExtension.exists_derived

/-- Actual derived scalar extension along the fixed ring map. -/
def extension (f : A →+* B) [HasExtension f] : D A ⥤ D B :=
  (extensionSource f).totalLeftDerived DerivedCategory.Q (quasiIso A)

/-- Its defining comparison to the actual degreewise source. -/
def extensionCounit (f : A →+* B) [HasExtension f] :
    DerivedCategory.Q ⋙ extension f ⟶ extensionSource f :=
  (extensionSource f).totalLeftDerivedCounit DerivedCategory.Q (quasiIso A)

instance extension_isLeftDerived (f : A →+* B) [HasExtension f] :
    (extension f).IsLeftDerivedFunctor (extensionCounit f) (quasiIso A) := by
  dsimp only [extension, extensionCounit]
  infer_instance

variable (A)

/-- The actual tensor functor, also for modules in the larger site universe. -/
def tensorLeft (M : Modules A) : Modules A ⥤ Modules A where
  obj N := ModuleCat.of A (M ⊗[A] N)
  map f := ModuleCat.ofHom (f.hom.lTensor M)
  map_id _ := by ext a b; rfl
  map_comp _ _ := by ext a b; rfl

instance tensorLeft_additive (M : Modules A) : (tensorLeft A M).Additive where
  map_add {X Y} f g := by
    apply ModuleCat.hom_ext
    change (f.hom + g.hom).lTensor M =
      f.hom.lTensor M + g.hom.lTensor M
    exact LinearMap.lTensor_add _ _ _

/-- Both actual module tensor variables, with their native linear maps. -/
def tensorBifunctor : Modules A ⥤ Modules A ⥤ Modules A where
  obj := tensorLeft A
  map f :=
    { app N := ModuleCat.ofHom (f.hom.rTensor N)
      naturality {N N'} g := by
        apply ModuleCat.hom_ext
        apply TensorProduct.ext
        ext a b
        rfl }
  map_id _ := by
    apply NatTrans.ext
    funext N
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext a b
    rfl
  map_comp _ _ := by
    apply NatTrans.ext
    funext N
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext a b
    rfl

instance tensorBifunctor_additive : (tensorBifunctor A).Additive where
  map_add {X Y} f g := by
    apply NatTrans.ext
    funext N
    apply ModuleCat.hom_ext
    change (f.hom + g.hom).rTensor N =
      f.hom.rTensor N + g.hom.rTensor N
    exact LinearMap.rTensor_add _ _ _

instance tensorBifunctor_obj_additive (M : Modules A) :
    ((tensorBifunctor A).obj M).Additive := tensorLeft_additive A M

/-- Total cochain tensor with the native Koszul differential. -/
def tensorSource : (Cochains A × Cochains A) ⥤ D A :=
  Functor.uncurry.obj ((tensorBifunctor A).map₂CochainComplex) ⋙
    DerivedCategory.Q

/-- The actual tensor source admits its two-variable left derived functor. -/
class HasTensor : Prop where
  exists_derived : (tensorSource A).HasLeftDerivedFunctor
    ((quasiIso A).prod (quasiIso A))

attribute [instance] HasTensor.exists_derived

/-- Both variables of the actual tensor source are derived. -/
def tensor [HasTensor A] : (D A × D A) ⥤ D A :=
  (tensorSource A).totalLeftDerived
    (DerivedCategory.Q.prod DerivedCategory.Q)
    ((quasiIso A).prod (quasiIso A))

/-- The real comparison to ordinary total cochain tensor. -/
def tensorCounit [HasTensor A] :
    (DerivedCategory.Q.prod DerivedCategory.Q) ⋙ tensor A ⟶ tensorSource A :=
  (tensorSource A).totalLeftDerivedCounit
    (DerivedCategory.Q.prod DerivedCategory.Q)
    ((quasiIso A).prod (quasiIso A))

instance tensor_isLeftDerived [HasTensor A] :
    (tensor A).IsLeftDerivedFunctor (tensorCounit A)
      ((quasiIso A).prod (quasiIso A)) := by
  dsimp only [tensor, tensorCounit]
  infer_instance

/-- A completion reflector characterized on actual derived-Hom complete
objects; its universal map is precisely precomposition with its unit. -/
structure Completion (I : Ideal A) where
  functor : D A ⥤ D A
  unit : 𝟭 (D A) ⟶ functor
  complete : ∀ K : D A, IsComplete A I (functor.obj K)
  universal : ∀ (K L : D A), IsComplete A I L →
    Function.Bijective (fun f : functor.obj K ⟶ L ↦ unit.app K ≫ f)

variable {A}

/-- Completed scalar extension along the actual ring map and reflector. -/
def completedExtension (f : A →+* B) [HasExtension f]
    {I : Ideal B} (C : Completion B I) : D A ⥤ D B :=
  extension f ⋙ C.functor

/-- The actual completed tensor product at two given derived objects. -/
def completedTensor [HasTensor A] {I : Ideal A} (C : Completion A I)
    (K L : D A) : D A :=
  C.functor.obj ((tensor A).obj (K, L))

end MathlibExt.RingTheory.DerivedModuleScalarOperations
