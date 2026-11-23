/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.ExactCategoryFunctor
public import MathlibExt.KTheory.Exact.Quillen.QuillenOriginalZigzagLoopEquivalence
public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridMixedLoopSquares
public import MathlibExt.Topology.Homotopy.OriginalEquivalenceSquareCancellation

/-!
# Quillen and Waldhausen loop models

For a preadditive exact category with a zero object and binary biproducts,
the Q-construction loop model is homotopy equivalent to the Waldhausen
S-construction loop model, using the standard Waldhausen structure.
The comparison is the Q-loop inverse followed by the S-construction map.
Both inverse homotopies are included.

An additive exact functor induces a continuous naturality homotopy for this
comparison. Source and target categories may have independent object and
morphism universes.

## Main results

* `quillenOriginalQSLoopHomotopyEquiv`: the Q/S loop equivalence.
* `quillenOriginalQSLoopHomotopyEquiv_both_inverse_families`: both
  inverse homotopies.
* `quillenOriginalQSMixedLoopHomotopy`: naturality under additive
  exact functors.
-/

public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open scoped Topology

universe uC vC uD vD

namespace AlgebraicKTheory

variable (C : Type uC) [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- The standard Waldhausen structure on the original exact category `C`. -/
local instance originalQSLoopComparisonWaldhausenC : WaldhausenCategory C :=
  ExactCategory.waldhausenCategory C

/-- The homotopy equivalence between the Q-construction and Waldhausen
S-construction loop models. -/
def quillenOriginalQSLoopHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (NQKSpace C) (stageWeakDiagonalKSpace C) :=
  (quillenOriginalQZigzagLoopEquiv C).symm.trans (quillenOriginalStageZigzagLoopEquiv C)

/-- The continuous comparison from the Q-loop model to the Waldhausen
loop model. -/
def quillenOriginalQSLoopMap : C(NQKSpace C, stageWeakDiagonalKSpace C) :=
  (quillenOriginalQSLoopHomotopyEquiv C).toFun

private theorem originalQSLoopMapValueComputed :
    quillenOriginalQSLoopMap C = (quillenStageGridToStageLoopMap (C := C)).comp
      (quillenOriginalQZigzagLoopEquiv C).invFun :=
  congrArg (fun f => f.comp (quillenOriginalQZigzagLoopEquiv C).invFun)
    (quillenOriginalStageZigzagLoopEquiv_toFun C)

/-- The comparison is the Q-loop inverse followed by the S-construction
loop map. -/
theorem quillenOriginalQSLoopMap_eq :
    quillenOriginalQSLoopMap C = (quillenStageGridToStageLoopMap (C := C)).comp
      (quillenOriginalQZigzagLoopEquiv C).invFun :=
  originalQSLoopMapValueComputed C

/-- Both inverse homotopies for the Q/S loop equivalence. -/
theorem quillenOriginalQSLoopHomotopyEquiv_both_inverse_families :
    Nonempty (ContinuousMap.Homotopy
      ((quillenOriginalQSLoopHomotopyEquiv C).invFun.comp (quillenOriginalQSLoopMap C))
      (ContinuousMap.id (NQKSpace C))) ∧
    Nonempty (ContinuousMap.Homotopy
      ((quillenOriginalQSLoopMap C).comp (quillenOriginalQSLoopHomotopyEquiv C).invFun)
      (ContinuousMap.id (stageWeakDiagonalKSpace C))) :=
  ⟨(quillenOriginalQSLoopHomotopyEquiv C).left_inv,
    (quillenOriginalQSLoopHomotopyEquiv C).right_inv⟩

variable {C}
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

/-- The standard Waldhausen structure on the original exact category `D`. -/
local instance originalQSLoopComparisonWaldhausenD : WaldhausenCategory D :=
  ExactCategory.waldhausenCategory D

/-- The naturality homotopy for the inverse Q-loop equivalence. -/
def quillenOriginalQInverseMixedLoopSquare :
    ContinuousMap.Homotopy
      ((quillenStageGridDiagonalMixedLoopMap F).comp (quillenOriginalQZigzagLoopEquiv C).invFun)
      ((quillenOriginalQZigzagLoopEquiv D).invFun.comp (NQKSpaceFunctorMap F)) := by
  let EC := quillenOriginalQZigzagLoopEquiv C
  let ED := quillenOriginalQZigzagLoopEquiv D
  have hC := quillenOriginalQZigzagLoopEquiv_toFun C
  have hD := quillenOriginalQZigzagLoopEquiv_toFun D
  let H := (quillenStageGridToNQMixedLoopSquare F).cast
    (congrArg (fun M => M.comp (quillenStageGridDiagonalMixedLoopMap F)) hD.symm)
    (congrArg (fun M => (NQKSpaceFunctorMap F).comp M) hC.symm)
  exact ContinuousMap.HomotopyEquiv.originalInverseSquareHomotopy EC ED
    (quillenStageGridDiagonalMixedLoopMap F) (NQKSpaceFunctorMap F) H

/-- The Q/S loop comparison is natural up to continuous homotopy under an
additive exact functor between categories in independent universes. -/
def quillenOriginalQSMixedLoopHomotopy :
    ContinuousMap.Homotopy
      ((quillenOriginalQSLoopMap D).comp (NQKSpaceFunctorMap F))
      (((Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalKSpaceMixedMap).comp
        (quillenOriginalQSLoopMap C)) := by
  let IC := (quillenOriginalQZigzagLoopEquiv C).invFun
  let ID := (quillenOriginalQZigzagLoopEquiv D).invFun
  let sC := quillenStageGridToStageLoopMap (C := C)
  let sD := quillenStageGridToStageLoopMap (C := D)
  let H₁ := (ContinuousMap.Homotopy.refl sD).comp (quillenOriginalQInverseMixedLoopSquare F).symm
  let H₂ := (quillenStageGridToStageMixedLoopSquare F).compContinuousMap IC
  have hStart : sD.comp (ID.comp (NQKSpaceFunctorMap F)) =
      (quillenOriginalQSLoopMap D).comp (NQKSpaceFunctorMap F) :=
    congrArg (fun M => M.comp (NQKSpaceFunctorMap F)) (quillenOriginalQSLoopMap_eq D).symm
  have hEnd : (((Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalKSpaceMixedMap).comp sC).comp IC =
      ((Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalKSpaceMixedMap).comp
        (quillenOriginalQSLoopMap C) :=
    congrArg (fun M => ((Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalKSpaceMixedMap).comp M)
      (quillenOriginalQSLoopMap_eq C).symm
  exact (H₁.cast hStart rfl).trans (H₂.cast rfl hEnd)

end AlgebraicKTheory

end
