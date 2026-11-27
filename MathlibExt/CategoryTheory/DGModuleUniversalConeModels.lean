/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.DGModuleBiproductModels
public import MathlibExt.CategoryTheory.DGScalarExtensionModels

/-!
# Native DG-module cone comparisons for homotopy squares

The universal comparison of a square is the native mapping-cone matrix
at every module point. Its off-diagonal block is the displayed homogeneous
homotopy. Quasi-isomorphism of this computed total comparison expresses
the derived pushout or pullback property. These construction inputs and
outputs are independent of any Calabi-Yau class.

References: Brav--Dyckerhoff, arXiv:1606.00619v1, Theorem 6.1 and
the completions following diagrams 6.6--6.7; Keller, Deriving DG
categories, §§2--3. Native cone/cochain formulas use Mathlib.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.DGModuleUniversalConeModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGScalarExtensionModels
open MathlibExt.CategoryTheory.DGModuleConeShiftModels
open MathlibExt.CategoryTheory.DGModuleBiproductModels
open CochainComplex.HomComplex

universe u
variable {k : Type u} [Field k]

/-- Induction of a closed module map is the actual degree-zero enriched map. -/
def pushedModuleMap {C E : DGCat k} {f : C ⟶ E} {R : RestrictionModel f}
    (L : ExtensionModel f R) (M N : DGDerivedModules k C) (a : M.obj ⟶ N.obj) :
    (L.functor.obj M).obj ⟶ (L.functor.obj N).obj :=
  (DGFunctor.homEquivDGCycles k _ _).symm
    ⟨L.functor.dgMap 0 (moduleCycle a), (mem_dgCycles k).mpr (by
      have ha : dgDifferential k 0 (show DGHom k 0 M N from moduleCycle a) = 0 :=
        by
          rw [DGFullSubcategory.dgDifferential_eq]
          exact (mem_dgCycles k).mp (DGFunctor.homEquivDGCycles k _ _ a).property
      simpa only [DGFullSubcategory.dgDifferential_eq] using
        L.functor.dgDifferential_dgMap_eq_zero ha)⟩

/-- Difference of two closed module maps uses the actual enriched cycle equivalence. -/
def moduleDifference {C : DGCat k} {M N : RightModule k C} (a b : M ⟶ N) : M ⟶ N :=
  (DGFunctor.homEquivDGCycles k M N).symm
    ((DGFunctor.homEquivDGCycles k M N a) - (DGFunctor.homEquivDGCycles k M N b))

/-- Negation of a module map is native negation in its closed degree-zero cochain module. -/
def negatedModuleMap {C : DGCat k} {M N : RightModule k C} (a : M ⟶ N) : M ⟶ N :=
  (DGFunctor.homEquivDGCycles k M N).symm (-(DGFunctor.homEquivDGCycles k M N a))

/-- Native cone descent at each module point, including its actual homotopy block. -/
structure ModuleConeDescModel {C : DGCat k} {M N V : RightModule k C}
    (f : M ⟶ N) (Q : ModuleConeModel f) (b : N ⟶ V) (h : DGHom k (-1) M V)
    (boundary : dgDifferential k (-1) h = moduleCycle (f ≫ b)) where
  map : Q.module ⟶ V
  normalized : ∀ (x : Cᵒᵖ) (r : ℤ),
    (moduleComponent map x).f r = (Q.valueIso x).hom.f r ≫
      (CochainComplex.mappingCone.descCochain (moduleComponent f x)
        (DGFunctor.dgApp k (-1) x h : Cochain _ _ (-1))
        (Cochain.ofHom (moduleComponent b x)) (by omega)).v r r (by omega)

/-- The literal cone comparison for a homotopy-commutative square. -/
structure ModuleConeMapModel {C : DGCat k} {M N M' N' : RightModule k C}
    (f : M ⟶ N) (g : M' ⟶ N') (Q : ModuleConeModel f) (Q' : ModuleConeModel g)
    (a : M ⟶ M') (b : N ⟶ N') (h : DGHom k (-1) M N')
    (boundary : dgDifferential k (-1) h = moduleCycle (f ≫ b) - moduleCycle (a ≫ g)) where
  map : Q.module ⟶ Q'.module
  normalized : ∀ (x : Cᵒᵖ) (r : ℤ),
    (moduleComponent map x).f r ≫ (Q'.valueIso x).hom.f r =
      (Q.valueIso x).hom.f r ≫
        ((CochainComplex.mappingCone.fst (moduleComponent f x)).val.v r (r + 1) rfl ≫
          ((moduleComponent a x).f (r + 1) ≫
            (CochainComplex.mappingCone.inl (moduleComponent g x)).v (r + 1) r (by omega) +
            (DGFunctor.dgApp k (-1) x h : Cochain _ _ (-1)).v (r + 1) r (by omega) ≫
              (CochainComplex.mappingCone.inr (moduleComponent g x)).f r) +
          (CochainComplex.mappingCone.snd (moduleComponent f x)).v r r (by omega) ≫
            (moduleComponent b x).f r ≫
              (CochainComplex.mappingCone.inr (moduleComponent g x)).f r)

/-- The computed biproduct descent map has both source inclusions fixed. -/
structure ModuleBiproductDescModel {C : DGCat k} {M N V : RightModule k C}
    (Q : ModuleBiproductModel M N) (a : M ⟶ V) (b : N ⟶ V) where
  map : Q.module ⟶ V
  normalized : ∀ x : Cᵒᵖ,
    moduleComponent map x = (Q.valueIso x).hom ≫
      biprod.desc (moduleComponent a x) (moduleComponent b x)

/-- The native biproduct lift fixes both actual projections. -/
structure ModuleBiproductLiftModel {C : DGCat k} {V M N : RightModule k C}
    (Q : ModuleBiproductModel M N) (a : V ⟶ M) (b : V ⟶ N) where
  map : V ⟶ Q.module
  normalized : ∀ x : Cᵒᵖ,
    moduleComponent map x ≫ (Q.valueIso x).hom =
      biprod.lift (moduleComponent a x) (moduleComponent b x)

/-- A square retains its four genuine module maps and the native degree -1 cell. -/
structure ModuleHomotopySquare (C : DGCat k) where
  topLeft : DGDerivedModules k C
  topRight : DGDerivedModules k C
  bottomLeft : DGDerivedModules k C
  bottomRight : DGDerivedModules k C
  top : topLeft.obj ⟶ topRight.obj
  left : topLeft.obj ⟶ bottomLeft.obj
  right : topRight.obj ⟶ bottomRight.obj
  bottom : bottomLeft.obj ⟶ bottomRight.obj
  cell : DGHom k (-1) topLeft.obj bottomRight.obj
  cell_boundary : dgDifferential k (-1) cell =
    moduleCycle (top ≫ right) - moduleCycle (left ≫ bottom)

/-- The source difference has the exact top-minus-left sign. -/
def ModuleHomotopySquare.difference {C : DGCat k} (D : ModuleHomotopySquare C)
    (Q : CofibrantBiproductModel D.topRight D.bottomLeft) : D.topLeft.obj ⟶ Q.module :=
  moduleDifference (D.top ≫ Q.inl) (D.left ≫ Q.inr)

/-- The homotopy pushout is certified by its single native total-cofiber comparison.
No nondegeneracy or Calabi-Yau input occurs here. -/
structure ModuleHomotopyPushout {C : DGCat k} (D : ModuleHomotopySquare C) where
  sum : CofibrantBiproductModel D.topRight D.bottomLeft
  cone : CofibrantConeModel D.topLeft (⟨sum.module, sum.cofibrant⟩) (D.difference sum)
  descent : ModuleBiproductDescModel sum.toModuleBiproductModel D.right D.bottom
  boundary : dgDifferential k (-1) D.cell = moduleCycle (D.difference sum ≫ descent.map)
  comparison : ModuleConeDescModel (D.difference sum) cone.toModuleConeModel
    descent.map D.cell boundary
  universal : ∀ x : Cᵒᵖ, QuasiIso (moduleComponent comparison.map x)

/-- The native target difference for a homotopy pullback. -/
def ModuleHomotopySquare.targetDifference {C : DGCat k} (D : ModuleHomotopySquare C)
    (Q : CofibrantBiproductModel D.topRight D.bottomLeft) : Q.module ⟶ D.bottomRight.obj :=
  moduleDifference (Q.fst ≫ D.right) (Q.snd ≫ D.bottom)

/-- A homotopy pullback is tested by the computed map to the native shifted target cone.
The first block is the same square cell; the second is its two actual incoming arrows. -/
structure ModuleHomotopyPullback {C : DGCat k} (D : ModuleHomotopySquare C) where
  sum : CofibrantBiproductModel D.topRight D.bottomLeft
  cone : CofibrantConeModel (⟨sum.module, sum.cofibrant⟩) D.bottomRight (D.targetDifference sum)
  fibre : CofibrantShiftModel (⟨cone.module, cone.cofibrant⟩) (-1)
  comparison : D.topLeft.obj ⟶ fibre.module
  normalized : ∀ (x : Cᵒᵖ) (r : ℤ),
    (moduleComponent comparison x).f r ≫ (fibre.valueIso x).hom.f r ≫
      ((cone.module.toEnrichedFunctor.obj x).shiftFunctorObjXIso (-1) r (r - 1) (by omega)).hom ≫
        (cone.valueIso x).hom.f (r - 1) =
      (biprod.lift (moduleComponent D.top x) (moduleComponent D.left x)).f r ≫
        (sum.valueIso x).inv.f r ≫
        (CochainComplex.mappingCone.inl (moduleComponent (D.targetDifference sum) x)).v
          r (r - 1) (by omega) +
      -(DGFunctor.dgApp k (-1) x D.cell : Cochain _ _ (-1)).v r (r - 1) (by omega) ≫
        (CochainComplex.mappingCone.inr (moduleComponent (D.targetDifference sum) x)).f (r - 1)
  universal : ∀ x : Cᵒᵖ, QuasiIso (moduleComponent comparison x)

end MathlibExt.CategoryTheory.DGModuleUniversalConeModels
