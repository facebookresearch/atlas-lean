/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.FreeFunction.TriplePermutation
public import MathlibExt.CategoryTheory.Monoidal.Mod.FreeInternalHom

/-!
# Coefficient actions on Day internal Hom generators

For a commutative Day monoid, computes the transposed scalar action on each triple of
coend generator indices. Under the stated Kan-extension and tensor-preservation
hypotheses, the formula retains the coefficient braiding, end evaluation, target module
action and index comparison.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uI vI uV vV
open CategoryTheory MonoidalCategory Limits
open scoped MonoidalClosed ExternalProduct CategoryTheory.MonObj

namespace NativeOmegaPreparation.DayCoefficientAction
variable {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  [MonoidalClosed V]
  [∀ (F G : I ⥤ V), (tensor I).HasPointwiseLeftKanExtension (F ⊠ G)]
  [(Functor.fromPUnit.{0} (𝟙_ I)).HasPointwiseLeftKanExtension
    (Functor.fromPUnit.{0} (𝟙_ V))]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (tensor I) d) (tensorLeft v)]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (tensor I) d) (tensorRight v)]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ I)) d) (tensorLeft v)]
  [∀ (v : V) (d : I), PreservesColimitsOfShape
    (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ I)) d) (tensorRight v)]
  [∀ (v : V) (d : I × I), PreservesColimitsOfShape
    (CostructuredArrow ((𝟭 I).prod (Functor.fromPUnit.{0} (𝟙_ I))) d) (tensorRight v)]
  [∀ (v : V) (d : I × I), PreservesColimitsOfShape
    (CostructuredArrow ((tensor I).prod (𝟭 I)) d) (tensorRight v)]
  [∀ (F G : I ⥤ V) (c : I), HasEnd
    ((dayConvolutionInternalHomDiagramFunctor F).obj G |>.obj c)]

/-- The original selected Day closed structure retains its genuine end adjunction. -/
local instance originalDayClosed : MonoidalClosed (DayFunctor I V) := inferInstance

/-- The actual auxiliary internal-Hom scalar action retains the full original coupled three-input
coend generator, whole coefficient braiding, end evaluation, target action and index comparison. -/
theorem transpose_generator (A : CommMon (DayFunctor I V)) (F : DayFunctor I V)
    (N : Mod (DayFunctor I V) A.X) (x y z : I) :
    (F.functor.obj x ◁ (DayFunctor.η A.X ((ihom F).obj N.X)).app (y, z)) ≫
        (DayFunctor.η F (A.X ⊗ (ihom F).obj N.X)).app (x, y ⊗ z) ≫
        (MonoidalClosed.uncurry ((Mod.internalHomAuxiliary A F N).mod.smul)).natTrans.app
          (x ⊗ (y ⊗ z)) =
      (α_ (F.functor.obj x) (A.X.functor.obj y) (((ihom F).obj N.X).functor.obj z)).inv ≫
        ((β_ (F.functor.obj x) (A.X.functor.obj y)).hom ▷
          ((ihom F).obj N.X).functor.obj z) ≫
        (α_ (A.X.functor.obj y) (F.functor.obj x) (((ihom F).obj N.X).functor.obj z)).hom ≫
        (A.X.functor.obj y ◁ MonoidalClosed.uncurry
          (end_.π
            ((dayConvolutionInternalHomDiagramFunctor F.functor).obj N.X.functor |>.obj z) x)) ≫
        (DayFunctor.η A.X N.X).app (y, x ⊗ z) ≫
        N.mod.smul.natTrans.app (y ⊗ (x ⊗ z)) ≫
        N.X.functor.map (DayActionIndex.leftCoefficientComparison x y z).hom := by
  let H := (ihom F).obj N.X
  let e : F ⊗ H ⟶ N.X := (ihom.ev F).app N.X
  let t : A.X ⊗ (F ⊗ H) ⟶ N.X := (A.X ◁ e) ≫ N.mod.smul
  let p : F ⊗ (A.X ⊗ H) ⟶ A.X ⊗ (F ⊗ H) :=
    (α_ F A.X H).inv ≫ ((β_ F A.X).hom ▷ H) ≫ (α_ A.X F H).hom
  let v : H.functor.obj z ⟶ (ihom (F.functor.obj x)).obj
      (N.X.functor.obj (x ⊗ z)) :=
    end_.π ((dayConvolutionInternalHomDiagramFunctor F.functor).obj N.X.functor |>.obj z) x
  let g : F.functor.obj x ⊗ H.functor.obj z ⟶ N.X.functor.obj (x ⊗ z) :=
    MonoidalClosed.uncurry v
  have hq : MonoidalClosed.uncurry ((Mod.internalHomAuxiliary A F N).mod.smul) = p ≫ t := by
    rw [Mod.internalHomAuxiliary_smul]
    simp only [MonoidalClosed.uncurry_curry, p, t,
      H, e, Category.assoc]
  have ht :=
    LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerLeft_app
      V A.X e y (x ⊗ z)
  change (DayFunctor.η A.X (F ⊗ H)).app (y, x ⊗ z) ≫
      (A.X ◁ e).natTrans.app (y ⊗ (x ⊗ z)) =
    (A.X.functor.obj y ◁ e.natTrans.app (x ⊗ z)) ≫
      (DayFunctor.η A.X N.X).app (y, x ⊗ z) at ht
  have he : (DayFunctor.η F H).app (x, z) ≫ e.natTrans.app (x ⊗ z) = g :=
    DayFunctor.evaluation_generator F N.X x z
  have hp := DayTriplePermutation.generator F A.X H x y z
  have hn := t.natTrans.naturality (DayActionIndex.leftCoefficientComparison x y z).hom
  change (F.functor.obj x ◁ (DayFunctor.η A.X H).app (y, z)) ≫
      (DayFunctor.η F (A.X ⊗ H)).app (x, y ⊗ z) ≫
      (MonoidalClosed.uncurry ((Mod.internalHomAuxiliary A F N).mod.smul)).natTrans.app
        (x ⊗ (y ⊗ z)) =
    (α_ (F.functor.obj x) (A.X.functor.obj y) (H.functor.obj z)).inv ≫
      ((β_ (F.functor.obj x) (A.X.functor.obj y)).hom ▷ H.functor.obj z) ≫
      (α_ (A.X.functor.obj y) (F.functor.obj x) (H.functor.obj z)).hom ≫
      (A.X.functor.obj y ◁ g) ≫ (DayFunctor.η A.X N.X).app (y, x ⊗ z) ≫
      N.mod.smul.natTrans.app (y ⊗ (x ⊗ z)) ≫
      N.X.functor.map (DayActionIndex.leftCoefficientComparison x y z).hom
  rw [hq]
  simp only [DayFunctor.comp_natTrans, NatTrans.comp_app]
  rw [reassoc_of% hp]
  rw [hn]
  simp only [t, DayFunctor.comp_natTrans, NatTrans.comp_app, Category.assoc]
  rw [reassoc_of% ht, ← whiskerLeft_comp_assoc, he]

end NativeOmegaPreparation.DayCoefficientAction
