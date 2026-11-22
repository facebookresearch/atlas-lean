/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.FreeFunction.RepresentableEnd
public import MathlibExt.CategoryTheory.Monoidal.DayConvolution.DayFunctorClosedSymmetric

/-!
# Day internal Hom from a free diagram

Under the required copowers and ends, identifies the Day internal Hom from a free diagram at `r` with index translation by `r` followed by scalar internal Hom. The comparison is natural in the target diagram, with formulas on the end projections.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uI vI uV vV
open CategoryTheory MonoidalCategory Limits
open scoped MonoidalClosed

namespace NativeOmegaPreparation.DayFreeEnd
variable {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  [MonoidalClosed V] [∀ a b : I, HasCoproductsOfShape (a ⟶ b) V]
  [∀ (F G : I ⥤ V) (c : I), HasEnd
    ((dayConvolutionInternalHomDiagramFunctor F).obj G |>.obj c)]
  (r : I) (M : V)

/-- The original Day internal-Hom end family supplies this identical free-diagram end, without an
additional limit assumption. -/
local instance originalFreeEnd (G : I ⥤ V) (c : I) :
    HasEnd (OrdinaryFreeEnd.diagram r M (tensorRight c ⋙ G)) := by
  change HasEnd
    ((dayConvolutionInternalHomDiagramFunctor ((evaluationLeftAdjoint V r).obj M)).obj
      G |>.obj c)
  infer_instance

/-- The target keeps the actual first-factor index translation and original coefficient internal Hom
through the existing Day wrapper. -/
def targetFunctor : DayFunctor I V ⥤ DayFunctor I V :=
  (DayFunctor.equiv I V).functor ⋙
    (Functor.whiskeringLeft I I V).obj (tensorLeft r) ⋙
      (Functor.whiskeringRight I V V).obj (ihom M) ⋙ (DayFunctor.equiv I V).inverse

/-- Original free-diagram end evaluation identifies the entire existing Day internal-Hom sequence,
including every index map. -/
def objectComparison (G : DayFunctor I V) :
    ((DayFunctor.internalHom (.mk ((evaluationLeftAdjoint V r).obj M))).obj G).functor ≅
      tensorLeft r ⋙ G.functor ⋙ ihom M :=
  NatIso.ofComponents (fun c => OrdinaryFreeEnd.iso r M (tensorRight c ⋙ G.functor)) (by
    intro c c' f
    change end_.map
        (((dayConvolutionInternalHomDiagramFunctor
          ((evaluationLeftAdjoint V r).obj M)).obj G.functor).map f) ≫
          OrdinaryFreeEnd.forward r M (tensorRight c' ⋙ G.functor) =
      OrdinaryFreeEnd.forward r M (tensorRight c ⋙ G.functor) ≫
        (ihom M).map (G.functor.map (r ◁ f))
    exact OrdinaryFreeEnd.forward_naturality r M (tensorRight c ⋙ G.functor)
      (Functor.whiskerRight ((curriedTensor I).flip.map f) G.functor))

omit [BraidedCategory V] in
/-- The actual selected Day internal-Hom target map retains every original end projection and target
component. -/
@[reassoc]
theorem original_map_π {G G' : DayFunctor I V} (h : G ⟶ G') (c j : I) :
    ((DayFunctor.internalHom (.mk ((evaluationLeftAdjoint V r).obj M))).map h).natTrans.app c ≫
        end_.π
          ((dayConvolutionInternalHomDiagramFunctor ((evaluationLeftAdjoint V r).obj M)).obj
            G'.functor |>.obj c) j =
      end_.π
          ((dayConvolutionInternalHomDiagramFunctor ((evaluationLeftAdjoint V r).obj M)).obj
            G.functor |>.obj c) j ≫
        (ihom (((evaluationLeftAdjoint V r).obj M).obj j)).map
          (h.natTrans.app (j ⊗ c)) := by
  dsimp only [DayFunctor.internalHom]
  exact DayConvolutionInternalHom.map_app_comp_π _ _ _ c j

omit [BraidedCategory V] in
/-- The whole selected Day target map is the actual ordinary end map by the original projection
universal property. -/
theorem original_map_component {G G' : DayFunctor I V} (h : G ⟶ G') (c : I) :
    ((DayFunctor.internalHom (.mk ((evaluationLeftAdjoint V r).obj M))).map h).natTrans.app c =
      end_.map
        (((dayConvolutionInternalHomDiagramFunctor ((evaluationLeftAdjoint V r).obj M)).map
          h.natTrans).app c) := by
  apply end_.hom_ext
  intro j
  exact (original_map_π r M h c j).trans
    ((end_.map_π
      (((dayConvolutionInternalHomDiagramFunctor ((evaluationLeftAdjoint V r).obj M)).map
        h.natTrans).app c) j).symm)

/-- Both full target transformation families are retained by the actual Day free-end comparison. -/
def comparison :
    DayFunctor.internalHom (.mk ((evaluationLeftAdjoint V r).obj M)) ≅
      targetFunctor r M :=
  NatIso.ofComponents
    (fun G => (DayFunctor.equiv I V).inverse.mapIso (objectComparison r M G)) (by
      intro G G' h
      apply DayFunctor.hom_ext
      apply NatTrans.ext
      funext c
      change ((DayFunctor.internalHom (.mk ((evaluationLeftAdjoint V r).obj M))).map
          h).natTrans.app c ≫
            OrdinaryFreeEnd.forward r M (tensorRight c ⋙ G'.functor) =
        OrdinaryFreeEnd.forward r M (tensorRight c ⋙ G.functor) ≫
          (ihom M).map (h.natTrans.app (r ⊗ c))
      rw [original_map_component]
      exact OrdinaryFreeEnd.forward_naturality r M (tensorRight c ⋙ G.functor)
        (Functor.whiskerLeft (tensorRight c) h.natTrans))

end NativeOmegaPreparation.DayFreeEnd
