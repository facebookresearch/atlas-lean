/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.FreeFunction.FreeCoefficientAction
public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.FreeFunction.IndexOrder

/-!
# Right coefficient actions in free Day Hom comparisons

For a symmetric monoidal index and a braided monoidal closed base, the
free-diagram internal-Hom comparison moves the source index to the right
tensor factor under the stated Day coproduct, extension, preservation and
end hypotheses. The auxiliary action of a commutative Day monoid transports
through this comparison to the displayed curried coefficient action. The
formula retains the coefficient shuffle and final inverse index associator.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uI vI uV vV
open CategoryTheory MonoidalCategory Limits
open scoped MonoidalClosed ExternalProduct CategoryTheory.MonObj

namespace NativeOmegaPreparation.DayFreeCoefficientRightAction
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

/-- The selected ordinary Day closed structure is its original end adjunction. -/
local instance originalDayClosed : MonoidalClosed (DayFunctor I V) := inferInstance

private abbrev freeDiagram (r : I) (M : V) : DayFunctor I V :=
  .mk ((evaluationLeftAdjoint V r).obj M)

/-- The actual free-end comparison followed by beta_(r,n) respects every original sphere-coefficient
action, with the full final-factor associator and no identification of index maps by dimension. -/
theorem action_forward (A : CommMon (DayFunctor I V)) (r : I) (M : V)
    (N : Mod (DayFunctor I V) A.X) (a n : I) :
    (DayFunctor.η A.X ((ihom ((DayFunctor.mk ((evaluationLeftAdjoint V r).obj M)))).obj N.X)).app (a, n) ≫
        ((Mod.internalHomAuxiliary A ((DayFunctor.mk ((evaluationLeftAdjoint V r).obj M))) N).mod.smul).natTrans.app
          (a ⊗ n) ≫
        ((DayFreeEnd.comparison r M ≪≫ DayIndexOrder.comparison r M).hom.app N.X).natTrans.app
          (a ⊗ n) =
      MonoidalClosed.curry
        (CoefficientShuffle.map M (A.X.functor.obj a)
          (((ihom ((DayFunctor.mk ((evaluationLeftAdjoint V r).obj M)))).obj N.X).functor.obj n) ≫
          (A.X.functor.obj a ◁ MonoidalClosed.uncurry
            (((DayFreeEnd.comparison r M ≪≫ DayIndexOrder.comparison r M).hom.app N.X).natTrans.app
              n)) ≫
          (DayFunctor.η A.X N.X).app (a, n ⊗ r) ≫
          N.mod.smul.natTrans.app (a ⊗ (n ⊗ r)) ≫
          N.X.functor.map (α_ a n r).inv) := by
  let H := (ihom (freeDiagram r M)).obj N.X
  let φ (k : I) : H.functor.obj k ⟶ (ihom M).obj (N.X.functor.obj (r ⊗ k)) :=
    (DayFreeEnd.objectComparison r M N.X).hom.app k
  let ψ (k : I) : H.functor.obj k ⟶ (ihom M).obj (N.X.functor.obj (k ⊗ r)) :=
    ((DayFreeEnd.comparison r M ≪≫ DayIndexOrder.comparison r M).hom.app N.X).natTrans.app k
  have hψ (k : I) : ψ k = φ k ≫ (ihom M).map (N.X.functor.map (β_ r k).hom) := rfl
  have hu : MonoidalClosed.uncurry (ψ n) =
      MonoidalClosed.uncurry (φ n) ≫ N.X.functor.map (β_ r n).hom := by
    rw [hψ, MonoidalClosed.uncurry_natural_right]
  let p (k : I) : A.X.functor.obj a ⊗ N.X.functor.obj k ⟶
      N.X.functor.obj (a ⊗ k) :=
    (DayFunctor.η A.X N.X).app (a, k) ≫ N.mod.smul.natTrans.app (a ⊗ k)
  have hp : (A.X.functor.obj a ◁ N.X.functor.map (β_ r n).hom) ≫ p (n ⊗ r) =
      p (r ⊗ n) ≫ N.X.functor.map (a ◁ (β_ r n).hom) := by
    have h := (DayFunctor.η A.X N.X ≫
      Functor.whiskerLeft (tensor I) N.mod.smul.natTrans).naturality
        (show (a, r ⊗ n) ⟶ (a, n ⊗ r) from (𝟙 a, (β_ r n).hom))
    simpa [p, tensorHom_def] using h
  suffices (DayFunctor.η A.X H).app (a, n) ≫
      ((Mod.internalHomAuxiliary A (freeDiagram r M) N).mod.smul).natTrans.app (a ⊗ n) ≫
      ψ (a ⊗ n) =
    MonoidalClosed.curry (CoefficientShuffle.map M (A.X.functor.obj a) (H.functor.obj n) ≫
      (A.X.functor.obj a ◁ MonoidalClosed.uncurry (ψ n)) ≫ p (n ⊗ r) ≫
      N.X.functor.map (α_ a n r).inv) by
    simp only [p, Category.assoc] at this
    exact this
  rw [hψ]
  have h : (DayFunctor.η A.X H).app (a, n) ≫
      ((Mod.internalHomAuxiliary A (freeDiagram r M) N).mod.smul).natTrans.app (a ⊗ n) ≫
      φ (a ⊗ n) =
    MonoidalClosed.curry (CoefficientShuffle.map M (A.X.functor.obj a) (H.functor.obj n) ≫
      (A.X.functor.obj a ◁ MonoidalClosed.uncurry (φ n)) ≫ p (r ⊗ n) ≫
      N.X.functor.map (DayActionIndex.leftCoefficientComparison r a n).hom) := by
    simpa only [p, Category.assoc] using DayFreeCoefficientAction.action_forward A r M N a n
  rw [reassoc_of% h, ← MonoidalClosed.curry_natural_right]
  apply congrArg MonoidalClosed.curry
  simp only [Category.assoc]
  rw [← N.X.functor.map_comp, DayActionIndex.rightOrder, N.X.functor.map_comp,
    hu, whiskerLeft_comp]
  simp only [p, Category.assoc] at hp ⊢
  rw [reassoc_of% hp]

end NativeOmegaPreparation.DayFreeCoefficientRightAction
