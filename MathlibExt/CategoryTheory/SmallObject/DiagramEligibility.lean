/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.SmallObject.DiagramSourceSmallness
public import MathlibExt.CategoryTheory.SmallObject.AdjointFamilyCells
public import Mathlib.CategoryTheory.EssentiallySmall

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w uJ vJ uC vC

open CategoryTheory CategoryTheory.Limits Opposite

namespace HomotopicalAlgebra

variable {J : Type uJ} [Category.{vJ} J] {C : Type uC} [Category.{vC} C]
  [∀ i j : J, HasCoproductsOfShape (i ⟶ j) C]

/-- Actual projective free images inherit all six fields at the original base cardinal. -/
theorem isCardinalForSmallObjectArgument_freeDiagrams
    (P : MorphismProperty C) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [OrderBot κ.ord.ToType] [Small.{w} J] [LocallySmall.{w} J]
    (hP : P.IsCardinalForSmallObjectArgument κ) :
    (MorphismProperty.adjointFamilyGenerators
      (fun j : J => evaluationLeftAdjoint C j) P).IsCardinalForSmallObjectArgument κ := by
  let L : J → C ⥤ (J ⥤ C) :=
    fun j => evaluationLeftAdjoint.{vJ, vC, uJ, uC} C j
  let _ : P.IsSmall.{w} := hP.isSmall
  let _ : LocallySmall.{w} C := hP.locallySmall
  let _ : HasPushouts C := hP.hasPushouts
  let _ : HasCoproducts.{w} C := hP.hasCoproducts
  let _ : HasIterationOfShape κ.ord.ToType C := hP.hasIterationOfShape
  let _ : LocallySmall.{w} (J ⥤ C) :=
    { hom_small := fun F G =>
        small_of_injective (f := fun η : F ⟶ G => fun j : J => η.app j)
          (fun η θ h => NatTrans.ext h) }
  refine
    { isSmall := MorphismProperty.adjointFamilyGenerators_isSmall L P
      locallySmall := inferInstance
      hasPushouts := inferInstance
      hasCoproducts := inferInstance
      hasIterationOfShape := inferInstance
      preservesColimit := ?_ }
  intro A B X Y i hi f c
  obtain ⟨q, hq⟩ := (MorphismProperty.adjointFamilyGenerators_iff L P i).mp hi
  let g (p : J × P.toSet) : p.2.1.left ⟶ p.2.1.right := p.2.1.hom
  let loc : J × P.toSet → J := Prod.fst
  let d : RelativeCellComplex.{w}
      (fun (_ : κ.ord.ToType) p => (L (loc p)).map (g p)) f :=
    c.adjointFamilyCellTypes L P
  let ev : (J ⥤ C) ⥤ C := (evaluation J C).obj q.1
  let _ : PreservesColimit d.F ev := inferInstance
  have hFree : PreservesColimit d.F
      (coyoneda.obj (op ((L q.1).obj q.2.1.left))) :=
    d.preservesColimit_freeDiagramSource κ g loc q.1
      (fun j hj => by
        let _ : HasColimitsOfShape (Set.Iio j) C :=
          hasColimitsOfShape_of_isSuccLimit C j hj
        infer_instance)
      (fun _ _ => by infer_instance)
      (fun _ _ => by infer_instance)
      (fun _ _ => by infer_instance)
      P (fun p => p.2.2) (fun _ _ => by infer_instance)
      hP q.2.1.hom q.2.2
  change PreservesColimit c.F
    (coyoneda.obj (op ((L q.1).obj q.2.1.left))) at hFree
  let _ : PreservesColimit c.F
      (coyoneda.obj (op ((L q.1).obj q.2.1.left))) := hFree
  let e : A ≅ (L q.1).obj q.2.1.left :=
    Arrow.leftFunc.mapIso (eqToIso hq)
  exact preservesColimit_of_natIso c.F (coyoneda.mapIso e.op)

end HomotopicalAlgebra
