/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicSquareWindowRealization
import Code.Universality.FiniteInjectivePerturbation









namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section



def fkIsingSquareWiredScaledDobrushinDomain
    (n : Nat) (hn : 0 < n) (mesh : Real) :
    FKIsingDobrushinDomain (fkSquareBoxPlanar n)
      (FKIsingSquareWiredCarrier n) where
  wiredArc := fkIsingSquareWiredArc n
  markedA := fkIsingSquareMarkedA n
  markedB := fkIsingSquareMarkedB n
  markedA_mem := fkIsingSquareMarkedA_mem_wiredArc n
  markedB_mem := fkIsingSquareMarkedB_mem_wiredArc n
  sourceEdge := .source
  terminalEdge := .terminal
  medialPosition := fun a ↦ (mesh : Complex) *
    fkIsingSquareWiredCarrierPosition n hn a
  exploration := fkIsingSquareWiredExplorationTrace n hn
  source_mem := by
    intro omega
    rw [mem_fkIsingSquareWiredExplorationTrace_iff]
  terminal_mem := by
    intro omega
    rw [mem_fkIsingSquareWiredExplorationTrace_iff]
    exact fkIsingSquareWiredLoopGraph_source_reachable_terminal n hn omega
  winding := fkIsingSquareWiredLiftedWinding n hn
  winding_terminal := fkIsingSquareWiredLiftedWinding_terminal n hn

@[simp] theorem fkIsingSquareWiredScaledDobrushinDomain_medialPosition
    (n : Nat) (hn : 0 < n) (mesh : Real)
    (a : FKIsingSquareWiredCarrier n) :
    (fkIsingSquareWiredScaledDobrushinDomain n hn mesh).medialPosition a =
      (mesh : Complex) * fkIsingSquareWiredCarrierPosition n hn a := rfl


@[simp] theorem fkIsingSquareWiredScaledDobrushinDomain_fermionicObservable
    (n : Nat) (hn : 0 < n) (mesh : Real)
    (a : FKIsingSquareWiredCarrier n) :
    (fkIsingSquareWiredScaledDobrushinDomain n hn mesh).fermionicObservable a =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable a := rfl



@[simp] theorem
    fkIsingSquareWiredScaledDobrushinDomain_normalizedFermionicObservable
    (n : Nat) (hn : 0 < n) (mesh : Real)
    (a : FKIsingSquareWiredCarrier n) :
    (fkIsingSquareWiredScaledDobrushinDomain n hn mesh).normalizedFermionicObservable
        mesh a =
      (fkIsingSquareWiredDobrushinDomain n hn).normalizedFermionicObservable
        mesh a := rfl



noncomputable def fkIsingSquareWiredPerturbedCarrierPosition
    (n : Nat) (hn : 0 < n) (mesh : Real) (hmesh : 0 < mesh) :
    FKIsingSquareWiredCarrier n → Complex :=
  Classical.choose (exists_injective_perturbation
    (fun a : FKIsingSquareWiredCarrier n ↦
      (mesh : Complex) * fkIsingSquareWiredCarrierPosition n hn a)
    (show 0 < mesh / 10 by positivity))

theorem fkIsingSquareWiredPerturbedCarrierPosition_injective
    (n : Nat) (hn : 0 < n) (mesh : Real) (hmesh : 0 < mesh) :
    Function.Injective
      (fkIsingSquareWiredPerturbedCarrierPosition n hn mesh hmesh) :=
  (Classical.choose_spec (exists_injective_perturbation
    (fun a : FKIsingSquareWiredCarrier n ↦
      (mesh : Complex) * fkIsingSquareWiredCarrierPosition n hn a)
    (show 0 < mesh / 10 by positivity))).1

theorem fkIsingSquareWiredPerturbedCarrierPosition_dist_lt
    (n : Nat) (hn : 0 < n) (mesh : Real) (hmesh : 0 < mesh)
    (a : FKIsingSquareWiredCarrier n) :
    dist (fkIsingSquareWiredPerturbedCarrierPosition n hn mesh hmesh a)
        ((mesh : Complex) * fkIsingSquareWiredCarrierPosition n hn a) <
      mesh / 10 :=
  (Classical.choose_spec (exists_injective_perturbation
    (fun a : FKIsingSquareWiredCarrier n ↦
      (mesh : Complex) * fkIsingSquareWiredCarrierPosition n hn a)
    (show 0 < mesh / 10 by positivity))).2 a



def fkIsingSquareWiredPerturbedDobrushinDomain
    (n : Nat) (hn : 0 < n) (mesh : Real) (hmesh : 0 < mesh) :
    FKIsingDobrushinDomain (fkSquareBoxPlanar n)
      (FKIsingSquareWiredCarrier n) where
  wiredArc := fkIsingSquareWiredArc n
  markedA := fkIsingSquareMarkedA n
  markedB := fkIsingSquareMarkedB n
  markedA_mem := fkIsingSquareMarkedA_mem_wiredArc n
  markedB_mem := fkIsingSquareMarkedB_mem_wiredArc n
  sourceEdge := .source
  terminalEdge := .terminal
  medialPosition := fkIsingSquareWiredPerturbedCarrierPosition n hn mesh hmesh
  exploration := fkIsingSquareWiredExplorationTrace n hn
  source_mem := by
    intro omega
    rw [mem_fkIsingSquareWiredExplorationTrace_iff]
  terminal_mem := by
    intro omega
    rw [mem_fkIsingSquareWiredExplorationTrace_iff]
    exact fkIsingSquareWiredLoopGraph_source_reachable_terminal n hn omega
  winding := fkIsingSquareWiredLiftedWinding n hn
  winding_terminal := fkIsingSquareWiredLiftedWinding_terminal n hn

@[simp] theorem fkIsingSquareWiredPerturbedDobrushinDomain_fermionicObservable
    (n : Nat) (hn : 0 < n) (mesh : Real) (hmesh : 0 < mesh)
    (a : FKIsingSquareWiredCarrier n) :
    (fkIsingSquareWiredPerturbedDobrushinDomain n hn mesh hmesh).fermionicObservable
        a =
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable a := rfl



noncomputable def fkIsingSquareWiredPerturbedRawInterpolant
    (n : Nat) (hn : 0 < n) (mesh : Real) (hmesh : 0 < mesh)
    (z : Complex) : Complex :=
  if h : ∃ a : FKIsingSquareWiredCarrier n,
      fkIsingSquareWiredPerturbedCarrierPosition n hn mesh hmesh a = z then
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable
      (Classical.choose h)
  else 0

@[simp] theorem fkIsingSquareWiredPerturbedRawInterpolant_medial
    (n : Nat) (hn : 0 < n) (mesh : Real) (hmesh : 0 < mesh)
    (a : FKIsingSquareWiredCarrier n) :
    fkIsingSquareWiredPerturbedRawInterpolant n hn mesh hmesh
        (fkIsingSquareWiredPerturbedCarrierPosition n hn mesh hmesh a) =
      (fkIsingSquareWiredPerturbedDobrushinDomain n hn mesh hmesh).fermionicObservable
        a := by
  rw [fkIsingSquareWiredPerturbedRawInterpolant, dif_pos ⟨a, rfl⟩]
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

end

end StatMech.Universality
