/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.SmallObject.DiagramEligibility
public import MathlibExt.CategoryTheory.SmallObject.Image
public import MathlibExt.CategoryTheory.MorphismProperty.FunctorCategory

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w uJ vJ uC vC

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace CategoryTheory.MorphismProperty

variable {J : Type uJ} [Category.{vJ} J] {C : Type uC} [Category.{vC} C]
  [∀ i j : J, HasCoproductsOfShape (i ⟶ j) C]

/-- Evaluate the actual generated left class using the base cells and their original cardinal. -/
theorem freeDiagrams_leftClass_evaluation_le
    (P Q : MorphismProperty C) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [OrderBot κ.ord.ToType] [Small.{w} J] [LocallySmall.{w} J]
    (hP : P.IsCardinalForSmallObjectArgument κ) (hPQ : P ≤ Q)
    [Q.IsStableUnderRetracts] [Q.IsStableUnderCoproducts.{w}]
    [Q.IsStableUnderCobaseChange]
    [Q.IsStableUnderTransfiniteCompositionOfShape κ.ord.ToType]
    (k : J) :
    (adjointFamilyGenerators (fun j : J => evaluationLeftAdjoint C j) P).rlp.llp ≤
      Q.inverseImage ((evaluation J C).obj k) := by
  let L : J → C ⥤ (J ⥤ C) := fun j => evaluationLeftAdjoint.{vJ, vC, uJ, uC} C j
  let _ : HasPushouts C := hP.hasPushouts
  let _ : HasCoproducts.{w} C := hP.hasCoproducts
  let _ : HasIterationOfShape κ.ord.ToType C := hP.hasIterationOfShape
  let _ : (adjointFamilyGenerators L P).IsCardinalForSmallObjectArgument κ :=
    isCardinalForSmallObjectArgument_freeDiagrams (J := J) P κ hP
  apply rlp_llp_le_inverseImage_of_cardinal_cells
    (adjointFamilyGenerators L P) Q ((evaluation J C).obj k) κ
  intro X Y f c
  let g (p : J × P.toSet) : p.2.1.left ⟶ p.2.1.right := p.2.1.hom
  let loc : J × P.toSet → J := _root_.Prod.fst
  let d : RelativeCellComplex.{w}
      (fun (_ : κ.ord.ToType) p => (L (loc p)).map (g p)) f :=
    c.adjointFamilyCellTypes L P
  let ev : (J ⥤ C) ⥤ C := (evaluation J C).obj k
  let _ : PreservesColimit d.F ev := inferInstance
  let evaluated : RelativeCellComplex.{w}
      (fun (_ : κ.ord.ToType) => P.homFamily) (ev.map f) :=
    d.evaluateFreeDiagramsInProperty κ g loc k
      (fun j hj => by
        let _ : HasColimitsOfShape (Set.Iio j) C :=
          hasColimitsOfShape_of_isSuccLimit C j hj
        infer_instance)
      (fun _ _ => by infer_instance)
      (fun _ _ => by infer_instance)
      (fun _ _ => by infer_instance)
      P (fun p => p.2.2) (fun _ _ => by infer_instance)
  let _ : PreservesWellOrderContinuousOfShape κ.ord.ToType (𝟭 C) :=
    { preservesColimitsOfShape := fun _ _ => inferInstance }
  have hEndpoint : Q ((𝟭 C).map (ev.map f)) :=
    evaluated.map_mem_of_le (𝟭 C) P Q hPQ
  change Q (((evaluation J C).obj k).map f) at hEndpoint
  exact hEndpoint

/-- The actual generated left class lies pointwise in W when its base cells lie in a closed Q. -/
theorem freeDiagrams_leftClass_le_functorCategory
    (P Q W : MorphismProperty C) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [OrderBot κ.ord.ToType] [Small.{w} J] [LocallySmall.{w} J]
    (hP : P.IsCardinalForSmallObjectArgument κ) (hPQ : P ≤ Q) (hQW : Q ≤ W)
    [Q.IsStableUnderRetracts] [Q.IsStableUnderCoproducts.{w}]
    [Q.IsStableUnderCobaseChange]
    [Q.IsStableUnderTransfiniteCompositionOfShape κ.ord.ToType] :
    (adjointFamilyGenerators (fun j : J => evaluationLeftAdjoint C j) P).rlp.llp ≤
      W.functorCategory J := by
  intro X Y f hf k
  have hLevel : Q (((evaluation J C).obj k).map f) :=
    (freeDiagrams_leftClass_evaluation_le P Q κ hP hPQ k) f hf
  change W (f.app k)
  exact hQW _ hLevel

end CategoryTheory.MorphismProperty
