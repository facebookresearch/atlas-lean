/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicSquareScaledDomain
import Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayer
import Code.Universality.FiniteHolomorphicInterpolation










namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section



def fkIsingSquareBoundaryPerturbedDobrushinDomain
    (n : Nat) (hn : 0 < n) (mesh : Real) (hmesh : 0 < mesh) :
    FKIsingDobrushinDomain (fkIsingSquareBoundaryDeletedPlanar n)
      (FKIsingSquareWiredCarrier n) where
  wiredArc := fkIsingSquareWiredArc n
  markedA := fkIsingSquareMarkedA n
  markedB := fkIsingSquareMarkedB n
  markedA_mem := fkIsingSquareMarkedA_mem_wiredArc n
  markedB_mem := fkIsingSquareMarkedB_mem_wiredArc n
  sourceEdge := .source
  terminalEdge := .terminal
  medialPosition := fkIsingSquareWiredPerturbedCarrierPosition n hn mesh hmesh
  exploration := fun omega =>
    fkIsingSquareWiredExplorationOrder n hn
      (fkIsingSquareClosePerimeter n omega)
  source_mem := fun omega =>
    fkIsingSquareWiredExplorationOrder_source_mem n hn _
  terminal_mem := fun omega =>
    fkIsingSquareWiredExplorationOrder_terminal_mem n hn _
  winding := fun omega =>
    fkIsingSquareWiredLiftedWinding n hn
      (fkIsingSquareClosePerimeter n omega)
  winding_terminal := fun omega =>
    fkIsingSquareWiredLiftedWinding_terminal n hn _



@[simp] theorem fkIsingSquareBoundaryPerturbedDobrushinDomain_fermionicObservable
    (n : Nat) (hn : 0 < n) (mesh : Real) (hmesh : 0 < mesh)
    (a : FKIsingSquareWiredCarrier n) :
    (fkIsingSquareBoundaryPerturbedDobrushinDomain n hn mesh hmesh).fermionicObservable
        a =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        a := rfl



noncomputable def fkIsingSquareBoundaryPerturbedRawInterpolant
    (n : Nat) (hn : 0 < n) (mesh : Real) (hmesh : 0 < mesh)
    (z : Complex) : Complex :=
  if h : ∃ a : FKIsingSquareWiredCarrier n,
      fkIsingSquareWiredPerturbedCarrierPosition n hn mesh hmesh a = z then
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
      (Classical.choose h)
  else 0

@[simp] theorem fkIsingSquareBoundaryPerturbedRawInterpolant_medial
    (n : Nat) (hn : 0 < n) (mesh : Real) (hmesh : 0 < mesh)
    (a : FKIsingSquareWiredCarrier n) :
    fkIsingSquareBoundaryPerturbedRawInterpolant n hn mesh hmesh
        (fkIsingSquareWiredPerturbedCarrierPosition n hn mesh hmesh a) =
      (fkIsingSquareBoundaryPerturbedDobrushinDomain n hn mesh hmesh).fermionicObservable
        a := by
  rw [fkIsingSquareBoundaryPerturbedRawInterpolant, dif_pos ⟨a, rfl⟩]
  have hchosen := Classical.choose_spec
    (show ∃ b : FKIsingSquareWiredCarrier n,
      fkIsingSquareWiredPerturbedCarrierPosition n hn mesh hmesh b =
        fkIsingSquareWiredPerturbedCarrierPosition n hn mesh hmesh a from
      ⟨a, rfl⟩)
  have heq : Classical.choose
        (show ∃ b : FKIsingSquareWiredCarrier n,
          fkIsingSquareWiredPerturbedCarrierPosition n hn mesh hmesh b =
            fkIsingSquareWiredPerturbedCarrierPosition n hn mesh hmesh a from
          ⟨a, rfl⟩) = a :=
    fkIsingSquareWiredPerturbedCarrierPosition_injective
      n hn mesh hmesh hchosen
  rw [heq]
  rfl



noncomputable def fkIsingSquareBoundaryPerturbedHolomorphicInterpolant
    (n : Nat) (hn : 0 < n) (mesh : Real) (hmesh : 0 < mesh) :
    Complex → Complex :=
  finiteLagrangeInterpolant
    (fkIsingSquareWiredPerturbedCarrierPosition n hn mesh hmesh)
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable



@[simp] theorem fkIsingSquareBoundaryPerturbedHolomorphicInterpolant_medial
    (n : Nat) (hn : 0 < n) (mesh : Real) (hmesh : 0 < mesh)
    (a : FKIsingSquareWiredCarrier n) :
    fkIsingSquareBoundaryPerturbedHolomorphicInterpolant n hn mesh hmesh
        (fkIsingSquareWiredPerturbedCarrierPosition n hn mesh hmesh a) =
      (fkIsingSquareBoundaryPerturbedDobrushinDomain n hn mesh hmesh).fermionicObservable
        a := by
  unfold fkIsingSquareBoundaryPerturbedHolomorphicInterpolant
  rw [finiteLagrangeInterpolant_apply _ _
    (fkIsingSquareWiredPerturbedCarrierPosition_injective n hn mesh hmesh)]
  rfl


theorem fkIsingSquareBoundaryPerturbedHolomorphicInterpolant_differentiable
    (n : Nat) (hn : 0 < n) (mesh : Real) (hmesh : 0 < mesh) :
    Differentiable Complex
      (fkIsingSquareBoundaryPerturbedHolomorphicInterpolant n hn mesh hmesh) := by
  unfold fkIsingSquareBoundaryPerturbedHolomorphicInterpolant
  exact differentiable_finiteLagrangeInterpolant _ _

end

end StatMech.Universality
