/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.SmallObject.CellularNormalization.Closure
public import MathlibExt.CategoryTheory.SmallObject.CoherentRetracts.TransfiniteAbsorption
public import MathlibExt.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Actual pushouts and coproducts of cellular Arrow retracts

Use the canonical cellular class and its original-history closure theorems.
The generic Arrow-retract constructors are in `MorphismProperty.Retract`.
Original coherent transfinite absorption supplies the remaining cellular
retract stability, with every source history and endpoint map retained.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe w ν u v

namespace CategoryTheory.SmallObject.CellularRetractsClosure

open Limits CellularNormalization MorphismProperty

variable {C : Type u} [Category.{v} C]

/-- Each original generator belongs to the literal cellular class at the same arrow. -/
theorem le_cellularClosure (P : MorphismProperty C) : P ≤ cellularClosure.{w, ν} P :=
  (P.le_coproducts.trans (P.coproducts.{ν}).le_pushouts).trans
    (P.coproducts.{ν}).pushouts.le_transfiniteCompositions

/-- The actual original generators belong to retracts of their cellular class. -/
theorem le_cellularRetracts (P : MorphismProperty C) :
    P ≤ (cellularClosure.{w, ν} P).retracts :=
  (le_cellularClosure P).trans (cellularClosure.{w, ν} P).le_retracts

/-- Cobase stability uses the canonical original-history pushout theorem. -/
instance cellularIsStableUnderCobaseChange (P : MorphismProperty C) [HasPushouts C] :
    (cellularClosure.{w, ν} P).IsStableUnderCobaseChange where
  of_isPushout sq hf := CellularNormalization.cobaseChange_mem P _ sq hf

private def emptyCofan [HasInitial C] : Cofan (fun i : PEmpty.{ν + 1} => (i.elim : C)) :=
  Cofan.mk (⊥_ C) (fun i => i.elim)

private def emptyCofanIsColimit [HasInitial C] : IsColimit (emptyCofan.{ν} (C := C)) :=
  (isColimitEquivIsInitialOfIsEmpty C (emptyCofan.{ν} (C := C))).symm initialIsInitial

/-- The canonical whole-history closure supplies the actual coproduct stability field. -/
theorem cellularIsStableUnderCoproducts (P : MorphismProperty C)
    [HasPushouts C] [HasCoproducts.{w} C] [HasInitial C] :
    (cellularClosure.{w, ν} P).IsStableUnderCoproducts.{w} :=
  (CellularNormalization.cellularClosure_stable.{w, ν} P
    emptyCofan.{ν} emptyCofan.{ν} emptyCofanIsColimit.{ν} emptyCofanIsColimit.{ν}).2.1

/-- Cobase closure of cellular retracts uses their actual original representative maps. -/
theorem cellularRetractsIsStableUnderCobaseChange (P : MorphismProperty C) [HasPushouts C] :
    (cellularClosure.{w, ν} P).retracts.IsStableUnderCobaseChange :=
  retractsIsStableUnderCobaseChange (cellularClosure.{w, ν} P)

/-- Coproduct closure of cellular retracts is derived from actual representatives and histories. -/
theorem cellularRetractsIsStableUnderCoproducts (P : MorphismProperty C)
    [HasPushouts C] [HasCoproducts.{w} C] [HasInitial C] :
    (cellularClosure.{w, ν} P).retracts.IsStableUnderCoproducts.{w} := by
  let := cellularIsStableUnderCoproducts (C := C) P
  exact retractsIsStableUnderCoproducts (cellularClosure.{w, ν} P)

/-- Original-shape coherent absorption derives transfinite stability of cellular retracts. -/
theorem cellularRetractsIsStableUnderTransfiniteComposition (P : MorphismProperty C)
    [HasPushouts C] [HasColimitsOfSize.{w, w} C] :
    MorphismProperty.IsStableUnderTransfiniteComposition.{w}
      (cellularClosure.{w, ν} P).retracts := by
  let : HasInitial C := hasInitialChangeUniverse.{w, 0} C
  exact
    { isStableUnderTransfiniteCompositionOfShape := fun J _ _ _ _ =>
        { le := fun _ _ _ ⟨outer⟩ =>
            CoherentRetracts.cellular_retracts_of_transfiniteComposition P outer
              emptyCofan.{ν} emptyCofan.{ν} emptyCofanIsColimit.{ν} emptyCofanIsColimit.{ν} } }

end CategoryTheory.SmallObject.CellularRetractsClosure
