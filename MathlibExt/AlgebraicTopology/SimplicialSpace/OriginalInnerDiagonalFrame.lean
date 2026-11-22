/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- The inner representable frame and original coefficient diagonal.
import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkCompletionRaw
import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerEnrichment
import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkScalarSM7
import Mathlib.CategoryTheory.Limits.Shapes.End
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# The actual inner representable frame and original coefficient diagonal

The frame is constant in the original outer space coordinate. Its degree-m
scalar is the original inner Delta[m]. Thus the diagonal keeps original outer
k and selects coefficient m equal to the INNER simplex degree n. The raw
completion and its coaugmentation are identified through their original
functors and genuine constant-diagonal Iso, before any weak-equivalence proof.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SimplicialSpace.Inner SSet.modelCategoryQuillen

namespace SimplicialSpace.OriginalInnerRealization

/-- An inner scalar is constant in the original outer simplicial-space coordinate. -/
def constantOuterScalar : SSet.{u} ⥤ SimplicialSpace.{u} :=
  SimplicialObject.const SSet.{u} ⋙ ofSimplicialObject

/-- The cosimplicial frame is the actual inner Delta[m], rather than an outer representable. -/
def innerRepresentableFrame : SimplexCategory ⥤ SimplicialSpace.{u} :=
  SSet.stdSimplex.{u} ⋙ constantOuterScalar

/-- Every frame bidegree retains the original outer coordinate and actual inner simplex. -/
theorem innerRepresentableFrame_bidegree (m : SimplexCategory)
    (k n : SimplexCategoryᵒᵖ) :
    (((innerRepresentableFrame.{u}.obj m).diagram.obj k).obj n) =
      (SSet.stdSimplex.{u}.obj m).obj n := rfl

/-- Every frame operator is the original inner standard-simplex operator. -/
theorem innerRepresentableFrame_map (m l : SimplexCategory) (f : m ⟶ l)
    (k : SimplexCategoryᵒᵖ) :
    (innerRepresentableFrame.{u}.map f).hom.app k = SSet.stdSimplex.map f := rfl

/-- The actual inner boundary object is also constant in the original outer coordinate. -/
def innerBoundaryFrame (m : ℕ) : SimplicialSpace.{u} :=
  constantOuterScalar.obj (SSet.boundary.{u} m : SSet.{u})

/-- The actual frame boundary arrow is the original scalar boundary inclusion everywhere outerly. -/
def innerBoundaryFrameMap (m : ℕ) : innerBoundaryFrame.{u} m ⟶
    innerRepresentableFrame.obj ⦋m⦌ :=
  constantOuterScalar.map (SSet.boundary.{u} m).ι

/-- All outer evaluations preserve the same actual scalar boundary map. -/
theorem innerBoundaryFrameMap_bidegree (m : ℕ) (k : SimplexCategoryᵒᵖ) :
    (innerBoundaryFrameMap.{u} m).hom.app k = (SSet.boundary.{u} m).ι := rfl

/-- The constant-outer scalar functor preserves original monomorphisms component by component. -/
theorem constantOuterScalar_mono {K L : SSet.{u}} (f : K ⟶ L) [Mono f] :
    Mono (constantOuterScalar.map f) := by
  apply forget.mono_of_mono_map
  rw [NatTrans.mono_iff_mono_app]
  intro k
  change Mono f
  infer_instance

/-- The actual frame boundary is cofibrant in the SAME named Rezk model. -/
theorem innerBoundaryFrameMap_cofibration (m : ℕ) :
    letI : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
    Cofibration (innerBoundaryFrameMap.{u} m) := by
  let : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
  rw [cofibration_iff]
  change RezkModel.modelCategory.categoryWithCofibrations.cofibrations (innerBoundaryFrameMap m)
  rw [RezkModel.modelCategory_cofibrations]
  exact constantOuterScalar_mono (SSet.boundary.{u} m).ι

/-- Diagonalize coefficient m and inner n, keeping the original outer space coordinate. -/
def innerDiagonalFunctor : SimplicialObject SimplicialSpace.{u} ⥤ SimplicialSpace.{u} :=
  (Functor.whiskeringRight SimplexCategoryᵒᵖ SimplicialSpace.{u}
      (SimplicialObject SSet.{u})).obj forget ⋙
    flipFunctor _ _ _ ⋙
    (Functor.whiskeringRight SimplexCategoryᵒᵖ (SimplicialObject SSet.{u}) SSet.{u}).obj
      SSet.simplicialDiagonalFunctor ⋙ ofSimplicialObject

/-- The literal diagonal carrier selects coefficient n and inner degree n at every outer k. -/
theorem innerDiagonalFunctor_bidegree (X : SimplicialObject SimplicialSpace.{u})
    (k n : SimplexCategoryᵒᵖ) :
    (((innerDiagonalFunctor.obj X).diagram.obj k).obj n) =
      ((X.obj n).diagram.obj k).obj n := rfl

/-- The actual diagonal map keeps the entire original bidegree component. -/
theorem innerDiagonalFunctor_map_bidegree {X Y : SimplicialObject SimplicialSpace.{u}}
    (f : X ⟶ Y) (k n : SimplexCategoryᵒᵖ) :
    ((innerDiagonalFunctor.map f).hom.app k).app n = ((f.app n).hom.app k).app n := rfl

/-- A constant coefficient diagram has the genuine original constant-diagonal Iso. -/
def innerDiagonalConstIso (W : SimplicialSpace.{u}) :
    innerDiagonalFunctor.obj ((SimplicialObject.const SimplicialSpace.{u}).obj W) ≅ W :=
  InducedCategory.isoMk (NatIso.ofComponents
    (fun k => SSet.diagonalConstIso (W.diagram.obj k))
    (by
      intro k l f
      exact CategoryTheory.SimplicialObject.diagonalConstIso_naturality (Type u) (W.diagram.map f)))

/-- The exact original full-J power diagram has the SAME Raw20 diagonal carrier. -/
theorem innerDiagonalFunctor_original_raw (W : SimplicialSpace.{u}) :
    innerDiagonalFunctor.obj (RezkCompletionRaw.powerDiagram W) =
      RezkCompletionRaw.rawCompletion W := rfl

/-- The constant-diagonal inverse followed by the actual full constant section is the SAME raw
Unit. -/
theorem innerDiagonalFunctor_original_unit (W : SimplicialSpace.{u}) :
    (innerDiagonalConstIso W).inv ≫
        innerDiagonalFunctor.map (RezkCompletionRaw.constantPowerSection W) =
      RezkCompletionRaw.rawCompletionUnit W := by
  apply InducedCategory.hom_ext
  apply NatTrans.ext
  funext k
  rfl

/-- The native coend bifunctor uses the actual INNER scalar tensor on each original coefficient
value. -/
def innerRealizationBifunctor (X : SimplicialObject SimplicialSpace.{u}) :
    SimplexCategoryᵒᵖ ⥤ SimplexCategory ⥤ SimplicialSpace.{u} :=
  X ⋙ innerTensorBifunctor ⋙
    (Functor.whiskeringLeft SimplexCategory SSet.{u} SimplicialSpace.{u}).obj SSet.stdSimplex

/-- Its full bidegree is X_m(k,n) times the original inner Delta[l]_n. -/
theorem innerRealizationBifunctor_bidegree (X : SimplicialObject SimplicialSpace.{u})
    (m : SimplexCategoryᵒᵖ) (l : SimplexCategory) (k n : SimplexCategoryᵒᵖ) :
    ((((innerRealizationBifunctor X).obj m).obj l).diagram.obj k).obj n =
      (((X.obj m).diagram.obj k).obj n × (SSet.stdSimplex.{u}.obj l).obj n) := rfl

/-- The actual weighted coend object; its diagonal Iso and adjunction are separate proofs still
required. -/
def innerRealization (X : SimplicialObject SimplicialSpace.{u}) : SimplicialSpace.{u} :=
  coend (innerRealizationBifunctor X)

end SimplicialSpace.OriginalInnerRealization
