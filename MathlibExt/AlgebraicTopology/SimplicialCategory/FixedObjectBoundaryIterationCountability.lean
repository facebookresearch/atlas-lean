/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectBoundaryCountability
import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeGeneratingFactorizations

/-!
# Countability of the same original countable boundary factorization

The native original cell-complex functor supplies its actual bottom
isomorphism, successor pushout isomorphisms and full limiting cocones.
Successor/limit induction counts every SAME actual stage. Its genuine
whole countable colimit therefore retains countable entire original Homs.
No replacement factorization or assumed countable stage is introduced.
-/

noncomputable section
universe u v w
open CategoryTheory Limits SmallObject
attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

namespace CategoryTheory.SimplicialEnrichment.FixedObjects

variable {O : Type u} [Countable O]

/-- Countability of all original whole stages counts the SAME point of an actual full colimit cocone. -/
theorem countableHoms_of_isColimit {J : Type v} [Category.{w} J] [Small.{u} J] [Countable J]
    {F : J ⥤ FixedObjects O} [∀ j, CountableHoms (F.obj j)] {c : Cocone F}
    (hc : IsColimit c) : CountableHoms c.pt := by
  let _ : HasColimit F := ⟨⟨c, hc⟩⟩
  have : CountableHoms (colimit.cocone F).pt := colimit_countable F
  exact countableHoms_of_iso (hc.coconePointUniqueUpToIso (colimit.isColimit F))

private theorem countable_boundaryIterationIndex : Countable Cardinal.aleph0.{u}.ord.ToType := by
  apply Cardinal.mk_le_aleph0_iff.mp
  simp only [Cardinal.mk_toType, Cardinal.card_ord]
  exact le_rfl

/-- Every SAME actual stage of the original countable boundary small-object construction has countable entire Homs. -/
theorem boundaryIteration_countableHoms {C D : FixedObjects O}
    [CountableHoms C] [CountableHoms D] (p : C ⟶ D)
    (j : Cardinal.aleph0.{u}.ord.ToType) :
    CountableHoms ((FreeFactorization.boundaryCells p).F.obj j) := by
  let _ : Countable Cardinal.aleph0.{u}.ord.ToType := countable_boundaryIterationIndex
  have : CountableHoms (Arrow.mk p).right := by
    change CountableHoms D
    infer_instance
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl := hj.eq_bot
    exact countableHoms_of_iso (FreeFactorization.boundaryCells p).isoBot
  | succ j _ hj =>
    have : CountableHoms (((iterationFunctor (boundaryFamily O) Cardinal.aleph0.{u}).obj j).obj
        (Arrow.mk p)).left := hj
    have : CountableHoms (((iterationFunctor (boundaryFamily O) Cardinal.aleph0.{u}).obj j).obj
        (Arrow.mk p)).right :=
      countableHoms_of_iso (iterationFunctorObjObjRightIso (boundaryFamily O)
        Cardinal.aleph0.{u} (Arrow.mk p) j)
    exact countableHoms_of_iso (relativeCellComplexιObjFObjSuccIso (boundaryFamily O)
      Cardinal.aleph0.{u} p j)
  | isSuccLimit j hj ih =>
    have (k : Set.Iio j) : CountableHoms
        (((Set.principalSegIio j).monotone.functor ⋙ (FreeFactorization.boundaryCells p).F).obj k) :=
      ih k.val k.property
    exact countableHoms_of_isColimit
      ((FreeFactorization.boundaryCells p).F.isColimitOfIsWellOrderContinuous j hj)

/-- The SAME stored original full boundary factorization object has countable entire Hom simplices. -/
instance boundaryFactorization_countableHoms {C D : FixedObjects O}
    [CountableHoms C] [CountableHoms D] (p : C ⟶ D) :
    CountableHoms (FreeFactorization.boundary p).Z := by
  let _ : Countable Cardinal.aleph0.{u}.ord.ToType := countable_boundaryIterationIndex
  have (j : Cardinal.aleph0.{u}.ord.ToType) :
      CountableHoms ((FreeFactorization.boundaryCells p).F.obj j) := boundaryIteration_countableHoms p j
  exact countableHoms_of_isColimit (FreeFactorization.boundaryCells p).isColimit

end CategoryTheory.SimplicialEnrichment.FixedObjects
