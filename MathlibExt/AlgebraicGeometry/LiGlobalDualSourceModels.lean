/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StackAffineModules
public import MathlibExt.Algebra.Category.ModuleCat.ModulePresheafUniverseLift
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Ring.ULift

/-!
# A global dual of the complete Li source

The ring presheaf and all module actions are transported together through
the native ULift ring equivalence. This places the actual universe-2
source in Mathlib's native monoidal category of module presheaves without
lowering its values or discarding any source/coefficient arrow.

The dual is identified by ONE global evaluation/coevaluation pair on
whole cochain diagrams. Its triangle comparisons are actual native
homotopies after a genuine unit resolution. Strict chain-level triangles
are not imposed. The two tensor-flat models make these the actual
derived tensors, including arbitrary nonflat coefficient base changes.

The source model and duality maps are construction outputs. In particular,
no objectwise collection of local isomorphisms supplies the global dual.
Source: Jun Li math/0110113v1 Sections 1--2; the native whole coefficient
model of Atlas PR4048 e6e3c8d7c02b1baedace4e3044e622070b5217d0; Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679 Presheaf/Monoidal and cochain
monoidal constructions (Apache 2.0).
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LiGlobalDualSourceModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry GeneralStackGeometry StackCycleGeometry StackAffineModules
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard

variable {k : Type} [Field k] (X : Stack (Spec (.of k)))

abbrev SmallModules := ModulePresheaf X
abbrev LargeModules := PresheafOfModules.{2} (rings X ⋙ forget₂ CommRingCat RingCat)
abbrev SmallComplex := CochainComplex (SmallModules X) ℤ
abbrev LargeComplex := CochainComplex (LargeModules X) ℤ

/-- The complete coefficient presheaf, with its native maps lifted together. -/
def tensorRings : (AffinePoint X)ᵒᵖ ⥤ CommRingCat.{2} where
  obj p := .of (ULift.{2} ((rings X).obj p))
  map f := CommRingCat.ofHom
    ((ULift.ringEquiv : ULift.{2} ((rings X).obj _) ≃+* (rings X).obj _).symm.toRingHom.comp
      (((rings X).map f).hom.comp
        (ULift.ringEquiv : ULift.{2} ((rings X).obj _) ≃+* (rings X).obj _).toRingHom))
  map_id p := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    apply ULift.ext
    simp
  map_comp f g := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    apply ULift.ext
    simp

abbrev TensorModules := PresheafOfModulesOfCommRing.{2} (tensorRings X)
abbrev TensorComplex := CochainComplex (TensorModules X) ℤ

instance tensorLeftAdditive (M : TensorModules X) :
    ((curriedTensor (TensorModules X)).obj M).Additive where
  map_add := by
    intro N P f g
    ext1 p
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    simp

instance tensorFunctorAdditive : (curriedTensor (TensorModules X)).Additive where
  map_add := by
    intro M N f g
    apply NatTrans.ext
    funext P
    ext1 p
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    simp

/- The preservation proof adapts Mathlib Presheaf/Monoidal.lean at the pinned
revision, Copyright (c) 2024 Dagur Asgeirsson, Jack McKoen and Joël Riou,
Apache 2.0. Here the indexing universe is independently small. -/
instance tensorLeftPreservesSmall (M : TensorModules X) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft M) where
  preservesColimitsOfShape := ⟨⟨fun h =>
    ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _
      (fun p => isColimitOfPreserves
        (tensorLeft (show ModuleCat ((tensorRings X).obj p) from M.obj p))
        (isColimitOfPreserves (PresheafOfModules.evaluation _ p) h))⟩⟩⟩

instance tensorRightPreservesSmall (M : TensorModules X) :
    PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
  preservesColimits_of_natIso (CategoryTheory.BraidedCategory.tensorLeftIsoTensorRight M)

noncomputable instance tensorComplexMonoidalStruct : MonoidalCategoryStruct (TensorComplex X) :=
  HomologicalComplex.monoidalCategoryStruct (TensorModules X) (ComplexShape.up ℤ)

noncomputable instance tensorComplexMonoidal : MonoidalCategory (TensorComplex X) :=
  HomologicalComplex.monoidalCategory (TensorModules X) (ComplexShape.up ℤ)

def tensorRingDown (p : (AffinePoint X)ᵒᵖ) : (tensorRings X).obj p →+* (rings X).obj p :=
  (ULift.ringEquiv : ULift.{2} ((rings X).obj p) ≃+* (rings X).obj p).toRingHom

def transportObject (M : LargeModules X) : TensorModules X where
  obj p := (ModuleCat.restrictScalars (tensorRingDown X p)).obj (M.obj p)
  map {p q} f :=
    (ModuleCat.restrictScalars (tensorRingDown X p)).map (M.map f) ≫
      (ModuleCat.restrictScalarsComp (tensorRingDown X p) ((rings X).map f).hom).inv.app (M.obj q) ≫
      (ModuleCat.restrictScalarsComp' ((tensorRings X).map f).hom (tensorRingDown X q)
        (((rings X).map f).hom.comp (tensorRingDown X p)) (by ext r; rfl)).hom.app (M.obj q)
  map_id p := by
    refine ModuleCat.hom_ext
      (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun x => ?_))
    change M.map (𝟙 p) x = x
    rw [M.map_id]
    rfl
  map_comp f g := by
    refine ModuleCat.hom_ext
      (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun x => ?_))
    simp

def transportMap {M N : LargeModules X} (f : M ⟶ N) :
    transportObject X M ⟶ transportObject X N where
  app p := (ModuleCat.restrictScalars (tensorRingDown X p)).map (f.app p)
  naturality {p q} g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change f.app q (M.map g x) = N.map g (f.app p x)
    exact ConcreteCategory.congr_hom (f.naturality g) x

/-- One functor transports all source maps and all coefficient actions. -/
def transport : LargeModules X ⥤ TensorModules X where
  obj := transportObject X
  map f := transportMap X f
  map_id M := by ext p x; rfl
  map_comp f g := by ext p x; rfl

instance : (transport X).Additive where
  map_add := by intros; ext p x; rfl

def raised (P : SmallComplex X) : LargeComplex X :=
  ((MathlibExt.Algebra.Category.ModuleCat.ModulePresheafUniverseLift.functor
    (rings X ⋙ forget₂ CommRingCat RingCat)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P

def transported (L : LargeComplex X) : TensorComplex X :=
  ((transport X).mapHomologicalComplex (ComplexShape.up ℤ)).obj L

def raisedTransported (P : SmallComplex X) : TensorComplex X := transported X (raised X P)

/-- The native tensor test on the entire cochain diagram category. -/
def IsTensorFlat (P : TensorComplex X) : Prop :=
  ∀ (A B : TensorComplex X) (f : A ⟶ B), QuasiIso f →
    QuasiIso (P ◁ f) ∧ QuasiIso (f ▷ P)

/-- The first triangle before inverting the genuine unit resolution. -/
def leftTriangle (P T U : TensorComplex X)
    (evaluation : P ⊗ T ⟶ 𝟙_ (TensorComplex X))
    (coevaluation : U ⟶ T ⊗ P) : P ⊗ U ⟶ P :=
  (P ◁ coevaluation) ≫ (α_ P T P).inv ≫ (evaluation ▷ P) ≫ (λ_ P).hom

/-- The second triangle on the same actual diagrams. -/
def rightTriangle (P T U : TensorComplex X)
    (evaluation : P ⊗ T ⟶ 𝟙_ (TensorComplex X))
    (coevaluation : U ⟶ T ⊗ P) : U ⊗ T ⟶ T :=
  (coevaluation ▷ T) ≫ (α_ T P T).hom ≫ (T ◁ evaluation) ≫ (ρ_ T).hom

/-- A constructed global derived dual of this SAME complete source.
The source shift places tangent/obstruction degrees 1,2 in degrees 0,1. -/
structure Duality (P : SmallComplex X) (L : LargeComplex X) where
  dualModel : TensorComplex X
  dualResolution : dualModel ⟶ raisedTransported X P
  [dualQuasi : QuasiIso dualResolution]
  sourceModel : TensorComplex X
  sourceResolution : sourceModel ⟶ transported X (L⟦(1 : ℤ)⟧)
  [sourceQuasi : QuasiIso sourceResolution]
  dualFlat : IsTensorFlat X dualModel
  sourceFlat : IsTensorFlat X sourceModel
  unitModel : TensorComplex X
  unitResolution : unitModel ⟶ 𝟙_ (TensorComplex X)
  [unitQuasi : QuasiIso unitResolution]
  evaluation : dualModel ⊗ sourceModel ⟶ 𝟙_ (TensorComplex X)
  coevaluation : unitModel ⟶ sourceModel ⊗ dualModel
  left : Homotopy (leftTriangle X dualModel sourceModel unitModel evaluation coevaluation)
    ((dualModel ◁ unitResolution) ≫ (ρ_ dualModel).hom)
  right : Homotopy (rightTriangle X dualModel sourceModel unitModel evaluation coevaluation)
    ((unitResolution ▷ sourceModel) ≫ (λ_ sourceModel).hom)
attribute [instance] Duality.dualQuasi Duality.sourceQuasi Duality.unitQuasi

end MathlibExt.AlgebraicGeometry.LiGlobalDualSourceModels
