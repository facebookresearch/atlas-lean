/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridMixedRealizationMap
public import MathlibExt.CategoryTheory.ClassifyingSpace.FunctorUniverseMapSimplexValue
public import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalMixedRealization

/-!
# The actual independent-role original Stage-grid to Quillen square

The original grid functor sends retained Quillen chains through the actual
Quillen functor. The lifted simplicial square is derived on every original
chain. Both original realization charts then give its whole mixed square,
with the Q endpoint recovered as the EXACT original Quillen realization map.
Original root/three-edge and Stage-side compatibility remain further work.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open scoped Simplicial Topology

universe uC vC uD vD

namespace AlgebraicKTheory

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

/-- Standard Waldhausen structure selected locally for the source exact category. -/
local instance originalMixedQSquareWaldhausenC : WaldhausenCategory C :=
  ExactCategory.waldhausenCategory C
/-- Standard Waldhausen structure selected locally for the target exact category. -/
local instance originalMixedQSquareWaldhausenD : WaldhausenCategory D :=
  ExactCategory.waldhausenCategory D

/-- The actual original Quillen chain map on the two unchanged carrier lifts. -/
def quillenNQOriginalCarrierLiftMap :
    SSet.uliftFunctor.{max uD vD, max uC vC}.obj (NQ C) ⟶
      SSet.uliftFunctor.{max uC vC, max uD vD}.obj (NQ D) where
  app n := ↾fun q => ULift.up (q.down ⋙ QuillenQ.map F)
  naturality {a b} f := by
    ext q
    apply ULift.ext
    rfl

private theorem originalNQCarrierLiftAppComputed (n : SimplexCategoryᵒᵖ)
    (q : (SSet.uliftFunctor.{max uD vD, max uC vC}.obj (NQ C)).obj n) :
    (quillenNQOriginalCarrierLiftMap F).app n q =
      (ULift.up (q.down ⋙ QuillenQ.map F) :
        (SSet.uliftFunctor.{max uC vC, max uD vD}.obj (NQ D)).obj n) := rfl

/-- Every original Quillen chain has its actual original functor image. -/
theorem quillenNQOriginalCarrierLiftMap_app (n : SimplexCategoryᵒᵖ)
    (q : (SSet.uliftFunctor.{max uD vD, max uC vC}.obj (NQ C)).obj n) :
    (quillenNQOriginalCarrierLiftMap F).app n q =
      (ULift.up (q.down ⋙ QuillenQ.map F) :
        (SSet.uliftFunctor.{max uC vC, max uD vD}.obj (NQ D)).obj n) :=
  originalNQCarrierLiftAppComputed F n q

private theorem originalGridQCarrierSquareComputed :
    quillenStageGridDiagonalMixedMap F ≫
        SSet.uliftFunctor.{max uC vC, max uD vD}.map (quillenStageGridToNQ (C := D)) =
      SSet.uliftFunctor.{max uD vD, max uC vC}.map (quillenStageGridToNQ (C := C)) ≫
        quillenNQOriginalCarrierLiftMap F := by
  apply NatTrans.ext
  funext n
  ext q
  apply ULift.ext
  change ((SSet.uliftFunctor.{max uC vC, max uD vD}.map
    (quillenStageGridToNQ (C := D))).app n
      ((quillenStageGridDiagonalMixedMap F).app n q)).down =
    ((quillenNQOriginalCarrierLiftMap F).app n
      ((SSet.uliftFunctor.{max uD vD, max uC vC}.map
        (quillenStageGridToNQ (C := C))).app n q)).down
  rw [quillenStageGridDiagonalMixedMap_app, quillenNQOriginalCarrierLiftMap_app]
  change (quillenStageGridToNQ (C := D)).app n
    (q.down ⋙ quillenStageGridLiftMap F n.unop) =
    ((quillenStageGridToNQ (C := C)).app n q.down) ⋙ QuillenQ.map F
  change (((quillenStageGridLiftMap F n.unop).obj (q.down.obj 0)).q) =
    ((q.down.obj 0).q ⋙ QuillenQ.map F)
  exact quillenStageGridLiftMap_obj_q F n.unop (q.down.obj 0)

/-- The literal lifted original grid/Q chain square is derived internally,
retaining independent original source/target Obj/Hom worlds. -/
theorem quillenStageGridToNQ_carrierLift_square :
    quillenStageGridDiagonalMixedMap F ≫
        SSet.uliftFunctor.{max uC vC, max uD vD}.map (quillenStageGridToNQ (C := D)) =
      SSet.uliftFunctor.{max uD vD, max uC vC}.map (quillenStageGridToNQ (C := C)) ≫
        quillenNQOriginalCarrierLiftMap F :=
  originalGridQCarrierSquareComputed F

private theorem originalNQMixedRealizationEqComputed :
    SSet.originalMixedRealization (quillenNQOriginalCarrierLiftMap F) =
      CategoryTheory.realizedNerveFunctorMap (QuillenQ.map F) := by
  apply ContinuousMap.ext
  intro x
  obtain ⟨n, σ, t, hσ⟩ := SSet.originalSimplexPresentation (NQ C) x
  have hMixed := SSet.originalMixedRealization_simplexValue
    (quillenNQOriginalCarrierLiftMap F) n σ t
  have hActual := CategoryTheory.realizedNerveFunctorMap_simplexValue (QuillenQ.map F) n σ t
  have hChain := quillenNQOriginalCarrierLiftMap_app F (op n) (ULift.up σ)
  have hImage : ((quillenNQOriginalCarrierLiftMap F).app (op n) (ULift.up σ)).down =
      σ ⋙ QuillenQ.map F := congrArg ULift.down hChain
  have hValue := congrArg (fun q : (NQ D).obj (op n) =>
    SSet.toTop.map (SSet.yonedaEquiv.symm q)
      ((SSet.toTopSimplex.{max uD vD}.inv.app n)
        (ULift.up t : SimplexCategory.toTop.{max uD vD}.obj n))) hImage
  exact (congrArg (SSet.originalMixedRealization (quillenNQOriginalCarrierLiftMap F)) hσ).symm.trans
    (hMixed.trans (hValue.trans
      (hActual.symm.trans (congrArg (CategoryTheory.realizedNerveFunctorMap (QuillenQ.map F)) hσ))))

/-- The actual lifted Quillen realization is the EXACT original mixed map,
with every original point/source/target carrier retained. -/
theorem quillenNQOriginalCarrierLiftMap_realization_eq :
    SSet.originalMixedRealization (quillenNQOriginalCarrierLiftMap F) =
      CategoryTheory.realizedNerveFunctorMap (QuillenQ.map F) :=
  originalNQMixedRealizationEqComputed F

private theorem originalGridMixedRealizationEqComputed :
    SSet.originalMixedRealization (quillenStageGridDiagonalMixedMap F) =
      quillenStageGridDiagonalRealMixedMap F := by
  apply ContinuousMap.ext
  intro x
  exact (SSet.originalMixedRealization_apply (quillenStageGridDiagonalMixedMap F) x).trans
    (quillenStageGridDiagonalRealMixedMap_apply F x).symm

/-- The ENTIRE actual original grid-to-Q realization square commutes for
independent source/target Obj/Hom worlds, with EXACT original Q-map endpoint. -/
theorem quillenStageGridToNQ_mixed_realization_square :
    (SSet.toTop.map (quillenStageGridToNQ (C := D))).hom.comp
        (quillenStageGridDiagonalRealMixedMap F) =
      (CategoryTheory.realizedNerveFunctorMap (QuillenQ.map F)).comp
        (SSet.toTop.map (quillenStageGridToNQ (C := C))).hom := by
  have h := SSet.originalMixedRealization_square
    (quillenStageGridDiagonalMixedMap F) (quillenNQOriginalCarrierLiftMap F)
    (quillenStageGridToNQ (C := C)) (quillenStageGridToNQ (C := D))
    (quillenStageGridToNQ_carrierLift_square F)
  rw [originalGridMixedRealizationEqComputed F,
    quillenNQOriginalCarrierLiftMap_realization_eq F] at h
  exact h

end AlgebraicKTheory

end
