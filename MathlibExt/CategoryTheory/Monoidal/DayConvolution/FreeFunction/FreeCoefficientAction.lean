/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.FreeFunction.CoefficientAction
public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.FreeFunction.EndComparison
public import MathlibExt.CategoryTheory.Monoidal.Closed.CoefficientShuffle

/-!
# Day-module actions on free-source internal Hom

For a commutative Day monoid and a target module, the action on internal Hom from a free Day
diagram is expressed through the original Day pairing and free-generator evaluation maps.
The formula retains the free index and coefficient, the target module action and the ambient
currying, under the stated Day-convolution existence hypotheses.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uI vI uV vV
open CategoryTheory MonoidalCategory Limits
open scoped MonoidalClosed ExternalProduct CategoryTheory.MonObj

namespace NativeOmegaPreparation.DayFreeCoefficientAction
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

/-- The original selected Day closed structure is its actual end adjunction. -/
local instance originalDayClosed : MonoidalClosed (DayFunctor I V) := inferInstance

private abbrev freeDiagram (r : I) (M : V) : DayFunctor I V :=
  .mk ((evaluationLeftAdjoint V r).obj M)

/-- The whole auxiliary scalar action from the original free source is carried by genuine free-end
evaluation, retaining the original full coefficient shuffle, module action and complete index
comparison. -/
theorem action_forward (A : CommMon (DayFunctor I V)) (r : I) (M : V)
    (N : Mod (DayFunctor I V) A.X) (a n : I) :
    (DayFunctor.η A.X ((ihom (DayFunctor.mk ((evaluationLeftAdjoint V r).obj M))).obj
        N.X)).app (a, n) ≫
        ((Mod.internalHomAuxiliary A (DayFunctor.mk ((evaluationLeftAdjoint V r).obj M))
          N).mod.smul).natTrans.app (a ⊗ n) ≫
        (DayFreeEnd.objectComparison r M N.X).hom.app (a ⊗ n) =
      MonoidalClosed.curry
        (CoefficientShuffle.map M (A.X.functor.obj a)
          (((ihom (DayFunctor.mk ((evaluationLeftAdjoint V r).obj M))).obj N.X).functor.obj n) ≫
          (A.X.functor.obj a ◁ MonoidalClosed.uncurry
            ((DayFreeEnd.objectComparison r M N.X).hom.app n)) ≫
          (DayFunctor.η A.X N.X).app (a, r ⊗ n) ≫
          N.mod.smul.natTrans.app (a ⊗ (r ⊗ n)) ≫
          N.X.functor.map (DayActionIndex.leftCoefficientComparison r a n).hom) := by
  let F := freeDiagram r M
  let H := (ihom F).obj N.X
  let u : M ⟶ F.functor.obj r := Sigma.ι (fun _ : r ⟶ r => M) (𝟙 r)
  let φ (k : I) : H.functor.obj k ⟶ (ihom M).obj (N.X.functor.obj (r ⊗ k)) :=
    (DayFreeEnd.objectComparison r M N.X).hom.app k
  let π (k : I) : H.functor.obj k ⟶
      (ihom (F.functor.obj r)).obj (N.X.functor.obj (r ⊗ k)) :=
    end_.π
      ((dayConvolutionInternalHomDiagramFunctor F.functor).obj N.X.functor |>.obj k) r
  let ν : A.X ⊗ H ⟶ H := (Mod.internalHomAuxiliary A F N).mod.smul
  let q : F ⊗ (A.X ⊗ H) ⟶ N.X := MonoidalClosed.uncurry ν
  have hφ (k : I) : φ k = π k ≫ (MonoidalClosed.pre u).app (N.X.functor.obj (r ⊗ k)) :=
    rfl
  have hφu : MonoidalClosed.uncurry (φ n) =
      (u ▷ H.functor.obj n) ≫ MonoidalClosed.uncurry (π n) := by
    rw [hφ]
    exact MonoidalClosed.uncurry_pre_app _ _ _
  have hν : ν.natTrans.app (a ⊗ n) ≫ π (a ⊗ n) =
      MonoidalClosed.curry
        ((DayFunctor.η F (A.X ⊗ H)).app (r, a ⊗ n) ≫ q.natTrans.app (r ⊗ (a ⊗ n))) := by
    have h := DayClosedProjection.curry_π F (A.X ⊗ H) N.X q (a ⊗ n) r
    rw [show MonoidalClosed.curry q = ν from MonoidalClosed.curry_uncurry ν] at h
    change ν.natTrans.app (a ⊗ n) ≫ π (a ⊗ n) =
      MonoidalClosed.curry
        ((DayFunctor.η F (A.X ⊗ H)).app (r, a ⊗ n) ≫ q.natTrans.app (r ⊗ (a ⊗ n))) at h
    exact h
  have hq := DayCoefficientAction.transpose_generator A F N r a n
  let g : F.functor.obj r ⊗ H.functor.obj n ⟶ N.X.functor.obj (r ⊗ n) :=
    MonoidalClosed.uncurry (π n)
  let v : A.X.functor.obj a ⊗ H.functor.obj n ⟶ (A.X ⊗ H).functor.obj (a ⊗ n) :=
    (DayFunctor.η A.X H).app (a, n)
  change (F.functor.obj r ◁ v) ≫
      (DayFunctor.η F (A.X ⊗ H)).app (r, a ⊗ n) ≫ q.natTrans.app (r ⊗ (a ⊗ n)) =
    (α_ (F.functor.obj r) (A.X.functor.obj a) (H.functor.obj n)).inv ≫
      ((β_ (F.functor.obj r) (A.X.functor.obj a)).hom ▷ H.functor.obj n) ≫
      (α_ (A.X.functor.obj a) (F.functor.obj r) (H.functor.obj n)).hom ≫
      (A.X.functor.obj a ◁ g) ≫ (DayFunctor.η A.X N.X).app (a, r ⊗ n) ≫
      N.mod.smul.natTrans.app (a ⊗ (r ⊗ n)) ≫
      N.X.functor.map (DayActionIndex.leftCoefficientComparison r a n).hom at hq
  change (DayFunctor.η A.X H).app (a, n) ≫ ν.natTrans.app (a ⊗ n) ≫ φ (a ⊗ n) =
    MonoidalClosed.curry (CoefficientShuffle.map M (A.X.functor.obj a) (H.functor.obj n) ≫
      (A.X.functor.obj a ◁ MonoidalClosed.uncurry (φ n)) ≫
      (DayFunctor.η A.X N.X).app (a, r ⊗ n) ≫ N.mod.smul.natTrans.app (a ⊗ (r ⊗ n)) ≫
      N.X.functor.map (DayActionIndex.leftCoefficientComparison r a n).hom)
  rw [hφ, reassoc_of% hν, MonoidalClosed.curry_pre_app,
    ← MonoidalClosed.curry_natural_left]
  apply congrArg MonoidalClosed.curry
  change (M ◁ v) ≫ (u ▷ (A.X ⊗ H).functor.obj (a ⊗ n)) ≫
      (DayFunctor.η F (A.X ⊗ H)).app (r, a ⊗ n) ≫ q.natTrans.app (r ⊗ (a ⊗ n)) = _
  rw [whisker_exchange_assoc, hq]
  have hs := CoefficientShuffle.naturality_first u (A.X.functor.obj a) (H.functor.obj n)
  simp only [CoefficientShuffle.map, Category.assoc] at hs
  rw [reassoc_of% hs,
    ← whiskerLeft_comp_assoc, ← hφu]
  simp only [CoefficientShuffle.map, Category.assoc]

end NativeOmegaPreparation.DayFreeCoefficientAction
