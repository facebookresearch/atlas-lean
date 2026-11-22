/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.FreeFunction.FreeCoefficientRightAction
public import MathlibExt.CategoryTheory.Monoidal.Closed.CoefficientShuffleNaturality
public import MathlibExt.CategoryTheory.Monoidal.Mod.FreeInternalHom

/-!
# Pair actions on free Day module function objects

For modules over a commutative Day monoid under the stated Kan-extension, tensor-preservation and end hypotheses, identifies the underlying function diagram from a free module with a shifted cotensor. The module pair action and stabilization label are computed using the index braiding.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uI vI uV vV
open CategoryTheory MonoidalCategory Limits
open scoped MonoidalClosed ExternalProduct CategoryTheory.MonObj

namespace NativeOmegaRecovery.FullFreeFunctionPair

section Scalar
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]

/-- Currying the original coefficient shuffle retains a whole parameter arrow. -/
private theorem curryShuffle_naturality (M A : V) {X Y Z W : V}
    (f : X ⟶ Y) (q : M ⊗ Y ⟶ Z) (g : A ⊗ Z ⟶ W) :
    (A ◁ f) ≫ MonoidalClosed.curry
        (NativeOmegaPreparation.CoefficientShuffle.map M A Y ≫ (A ◁ q) ≫ g) =
      MonoidalClosed.curry
        (NativeOmegaPreparation.CoefficientShuffle.map M A X ≫
          (A ◁ ((M ◁ f) ≫ q)) ≫ g) := by
  rw [← MonoidalClosed.curry_natural_left]
  rw [reassoc_of% NativeOmegaPreparation.CoefficientShuffle.naturality_third M A f]
  simp only [whiskerLeft_comp, Category.assoc]

end Scalar

section Day
variable {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  [MonoidalClosed V] [∀ a b : I, HasCoproductsOfShape (a ⟶ b) V]
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
  [HasEqualizers (DayFunctor I V)]

/-- The actual selected ordinary Day closed structure is the original end adjunction. -/
local instance originalDayClosed : MonoidalClosed (DayFunctor I V) := inferInstance

private abbrev freeDiagram (r : I) (M : V) : DayFunctor I V :=
  .mk ((evaluationLeftAdjoint V r).obj M)

/-- The original module free-unit and original end evaluation, followed by the
actual beta_(r,n), provide the full underlying sequence comparison. -/
def comparison (A : CommMon (DayFunctor I V)) (r : I) (M : V)
    (N : Mod (DayFunctor I V) A.X) :
    ((Mod.internalHom A ((Mod.free A.X).obj
      (DayFunctor.mk ((evaluationLeftAdjoint V r).obj M)))).obj N).X ≅
      (NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor r M).obj N.X :=
  CategoryTheory.Mod.FreeInternalHom.iso A
      (DayFunctor.mk ((evaluationLeftAdjoint V r).obj M)) N ≪≫
    (NativeOmegaPreparation.DayFreeEnd.comparison r M ≪≫
      NativeOmegaPreparation.DayIndexOrder.comparison r M).app N.X

/-- The original shifted-cotensor pair formula is expressed on its unchanged
coefficient, original target module action and final-factor associator. -/
def targetAction (A : CommMon (DayFunctor I V)) (r : I) (M : V)
    (N : Mod (DayFunctor I V) A.X) (a n : I) :
    A.X.functor.obj a ⊗ (ihom M).obj (N.X.functor.obj (n ⊗ r)) ⟶
      (ihom M).obj (N.X.functor.obj ((a ⊗ n) ⊗ r)) :=
  MonoidalClosed.curry
    (NativeOmegaPreparation.CoefficientShuffle.map M (A.X.functor.obj a)
        ((ihom M).obj (N.X.functor.obj (n ⊗ r))) ≫
      (A.X.functor.obj a ◁ (ihom.ev M).app (N.X.functor.obj (n ⊗ r))) ≫
      (DayFunctor.η A.X N.X).app (a, n ⊗ r) ≫
      N.mod.smul.natTrans.app (a ⊗ (n ⊗ r)) ≫
      N.X.functor.map (α_ a n r).inv)

/-- Every original Day pair action of the actual free-source module internal Hom
commutes with the complete original evaluation/extension comparison. -/
theorem pair_square (A : CommMon (DayFunctor I V)) (r : I) (M : V)
    (N : Mod (DayFunctor I V) A.X) (a n : I) :
    (DayFunctor.η A.X
        ((Mod.internalHom A ((Mod.free A.X).obj
          (DayFunctor.mk ((evaluationLeftAdjoint V r).obj M)))).obj N).X).app (a, n) ≫
      ((Mod.internalHom A ((Mod.free A.X).obj
        (DayFunctor.mk ((evaluationLeftAdjoint V r).obj M)))).obj N).mod.smul.natTrans.app
        (a ⊗ n) ≫ (comparison A r M N).hom.natTrans.app (a ⊗ n) =
      (A.X.functor.obj a ◁ (comparison A r M N).hom.natTrans.app n) ≫
        targetAction A r M N a n := by
  let F := freeDiagram r M
  let H := (Mod.internalHom A ((Mod.free A.X).obj F)).obj N
  let J := (ihom F).obj N.X
  let e : H.X ⟶ J := CategoryTheory.Mod.FreeInternalHom.forward A F N
  let d : J ≅ (NativeOmegaPreparation.DayIndexOrder.rightTargetFunctor r M).obj N.X :=
    (NativeOmegaPreparation.DayFreeEnd.comparison r M ≪≫
      NativeOmegaPreparation.DayIndexOrder.comparison r M).app N.X
  let ψ (k : I) : J.functor.obj k ⟶ (ihom M).obj (N.X.functor.obj (k ⊗ r)) :=
    d.hom.natTrans.app k
  let φ (k : I) : H.X.functor.obj k ⟶ (ihom M).obj (N.X.functor.obj (k ⊗ r)) :=
    (comparison A r M N).hom.natTrans.app k
  let pH : A.X.functor.obj a ⊗ H.X.functor.obj n ⟶ H.X.functor.obj (a ⊗ n) :=
    (DayFunctor.η A.X H.X).app (a, n) ≫ H.mod.smul.natTrans.app (a ⊗ n)
  let pJ : A.X.functor.obj a ⊗ J.functor.obj n ⟶ J.functor.obj (a ⊗ n) :=
    (DayFunctor.η A.X J).app (a, n) ≫
      ((Mod.internalHomAuxiliary A F N).mod.smul).natTrans.app (a ⊗ n)
  let g : A.X.functor.obj a ⊗ N.X.functor.obj (n ⊗ r) ⟶
      N.X.functor.obj ((a ⊗ n) ⊗ r) :=
    (DayFunctor.η A.X N.X).app (a, n ⊗ r) ≫
      N.mod.smul.natTrans.app (a ⊗ (n ⊗ r)) ≫ N.X.functor.map (α_ a n r).inv
  have hφ (k : I) : φ k = e.natTrans.app k ≫ ψ k := rfl
  have hlinear : H.mod.smul.natTrans.app (a ⊗ n) ≫ e.natTrans.app (a ⊗ n) =
      (A.X ◁ e).natTrans.app (a ⊗ n) ≫
        ((Mod.internalHomAuxiliary A F N).mod.smul).natTrans.app
          (a ⊗ n) := by
    have h := congrArg
      (fun q : A.X ⊗ H.X ⟶ J => q.natTrans.app (a ⊗ n))
      (CategoryTheory.Mod.FreeInternalHom.forward_linear A F N)
    simpa only [DayFunctor.comp_natTrans, NatTrans.comp_app] using h
  have hw := LawfulDayConvolutionMonoidalCategoryStruct.convolutionExtensionUnit_comp_ι_map_whiskerLeft_app
    V A.X e a n
  change (DayFunctor.η A.X H.X).app (a, n) ≫ (A.X ◁ e).natTrans.app (a ⊗ n) =
    (A.X.functor.obj a ◁ e.natTrans.app n) ≫ (DayFunctor.η A.X J).app (a, n) at hw
  have he : pH ≫ e.natTrans.app (a ⊗ n) =
      (A.X.functor.obj a ◁ e.natTrans.app n) ≫ pJ := by
    dsimp only [pH, pJ]
    rw [Category.assoc, hlinear, ← Category.assoc, hw, Category.assoc]
  have hd : pJ ≫ ψ (a ⊗ n) =
      MonoidalClosed.curry
        (NativeOmegaPreparation.CoefficientShuffle.map M (A.X.functor.obj a)
            (J.functor.obj n) ≫
          (A.X.functor.obj a ◁ MonoidalClosed.uncurry (ψ n)) ≫ g) := by
    have h : (DayFunctor.η A.X J).app (a, n) ≫
        ((Mod.internalHomAuxiliary A F N).mod.smul).natTrans.app (a ⊗ n) ≫
        ψ (a ⊗ n) =
      MonoidalClosed.curry
        (NativeOmegaPreparation.CoefficientShuffle.map M (A.X.functor.obj a)
            (J.functor.obj n) ≫
          (A.X.functor.obj a ◁ MonoidalClosed.uncurry (ψ n)) ≫ g) :=
      NativeOmegaPreparation.DayFreeCoefficientRightAction.action_forward A r M N a n
    exact (Category.assoc ((DayFunctor.η A.X J).app (a, n))
      (((Mod.internalHomAuxiliary A F N).mod.smul).natTrans.app (a ⊗ n))
      (ψ (a ⊗ n))).trans h
  suffices pH ≫ φ (a ⊗ n) =
      (A.X.functor.obj a ◁ φ n) ≫ targetAction A r M N a n by
    exact (Category.assoc ((DayFunctor.η A.X H.X).app (a, n))
      (H.mod.smul.natTrans.app (a ⊗ n)) (φ (a ⊗ n))).symm.trans this
  have hLeft : pH ≫ φ (a ⊗ n) = MonoidalClosed.curry
        (NativeOmegaPreparation.CoefficientShuffle.map M (A.X.functor.obj a)
            (H.X.functor.obj n) ≫
          (A.X.functor.obj a ◁ MonoidalClosed.uncurry (φ n)) ≫ g) := by
    rw [hφ, ← Category.assoc, he, Category.assoc, hd, curryShuffle_naturality,
      hφ, MonoidalClosed.uncurry_natural_left]
  rw [hLeft]
  dsimp only [targetAction]
  change MonoidalClosed.curry
      (NativeOmegaPreparation.CoefficientShuffle.map M (A.X.functor.obj a)
          (H.X.functor.obj n) ≫
        (A.X.functor.obj a ◁ MonoidalClosed.uncurry (φ n)) ≫ g) =
    (A.X.functor.obj a ◁ φ n) ≫ MonoidalClosed.curry
      (NativeOmegaPreparation.CoefficientShuffle.map M (A.X.functor.obj a)
          ((ihom M).obj (N.X.functor.obj (n ⊗ r))) ≫
        (A.X.functor.obj a ◁ (ihom.ev M).app (N.X.functor.obj (n ⊗ r))) ≫ g)
  rw [curryShuffle_naturality, MonoidalClosed.uncurry_eq]

end Day

section Index
variable {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]

/-- The original cross-degree source generator retains both actual conjugating
braids and the original right-shift associator. -/
def stabilizationLabel (n r a : I) : a ⊗ (n ⊗ r) ⟶ n ⊗ (r ⊗ a) :=
  (a ◁ (β_ n r).hom) ≫ (α_ a r n).inv ≫
    ((β_ a r).hom ▷ n) ≫ (β_ (r ⊗ a) n).hom

/-- Symmetric coherence identifies that whole original label with the native
coefficient-first label and its complete target associator. -/
theorem stabilizationLabel_eq (n r a : I) :
    stabilizationLabel n r a = (β_ a (n ⊗ r)).hom ≫ (α_ n r a).hom := by
  simp only [stabilizationLabel]
  rw [BraidedCategory.braiding_naturality_left]
  simp only [BraidedCategory.braiding_tensor_left_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [← whiskerLeft_comp_assoc, SymmetricCategory.symmetry,
    whiskerLeft_id, Category.id_comp]
  simp only [BraidedCategory.braiding_tensor_right_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

end Index

end NativeOmegaRecovery.FullFreeFunctionPair
