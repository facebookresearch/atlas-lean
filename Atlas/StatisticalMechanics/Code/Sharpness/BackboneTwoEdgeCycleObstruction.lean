/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















import Code.Sharpness.BackboneTwoEdgeBondToggle

open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false

namespace StatMech.Sharpness

noncomputable section

namespace BackboneTwoEdgeCycleObstruction

open BackboneConcreteBondProgram
open BackboneConcreteSelector
open BackboneDeterminedCutSwitching
open BackboneLabeledSwitching
open BackbonePartialP2Reindex
open BackboneP2CoordinateReindex
open BackboneTwoEdgeBondProgram
open BackboneTwoEdgeBondToggle
open FluxEdgeCopy

noncomputable local instance obstructionDecidableAdj
    (G : SimpleGraph (Fin 6)) : DecidableRel G.Adj := Classical.decRel _


def graph : SimpleGraph (Fin 6) :=
  SimpleGraph.fromEdgeSet
    ({s((0 : Fin 6), 1), s((1 : Fin 6), 2), s((3 : Fin 6), 4),
        s((4 : Fin 6), 5), s((5 : Fin 6), 3)} : Set (Sym2 (Fin 6)))

@[simp] theorem graph_edgeFinset :
    graph.edgeFinset =
      {s((0 : Fin 6), 1), s((1 : Fin 6), 2), s((3 : Fin 6), 4),
        s((4 : Fin 6), 5), s((5 : Fin 6), 3)} := by
  ext e
  rw [SimpleGraph.mem_edgeFinset, graph,
    SimpleGraph.edgeSet_fromEdgeSet]
  simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · exact And.left
  · intro he
    refine ⟨he, ?_⟩
    rcases he with rfl | rfl | rfl | rfl | rfl <;> decide

def headEdge : graph.edgeFinset := ⟨s((0 : Fin 6), 1), by simp⟩
def suffixEdge : graph.edgeFinset := ⟨s((1 : Fin 6), 2), by simp⟩
def cycleEdge₀ : graph.edgeFinset := ⟨s((3 : Fin 6), 4), by simp⟩
def cycleEdge₁ : graph.edgeFinset := ⟨s((4 : Fin 6), 5), by simp⟩
def cycleEdge₂ : graph.edgeFinset := ⟨s((5 : Fin 6), 3), by simp⟩

theorem headEdge_ne_suffixEdge : headEdge ≠ suffixEdge := by
  intro h
  exact (by decide : s((0 : Fin 6), 1) ≠ s((1 : Fin 6), 2))
    (congrArg Subtype.val h)

theorem headEdge_ne_cycleEdge₀ : headEdge ≠ cycleEdge₀ := by
  intro h
  exact (by decide : s((0 : Fin 6), 1) ≠ s((3 : Fin 6), 4))
    (congrArg Subtype.val h)

theorem headEdge_ne_cycleEdge₁ : headEdge ≠ cycleEdge₁ := by
  intro h
  exact (by decide : s((0 : Fin 6), 1) ≠ s((4 : Fin 6), 5))
    (congrArg Subtype.val h)

theorem headEdge_ne_cycleEdge₂ : headEdge ≠ cycleEdge₂ := by
  intro h
  exact (by decide : s((0 : Fin 6), 1) ≠ s((5 : Fin 6), 3))
    (congrArg Subtype.val h)

theorem suffixEdge_ne_cycleEdge₀ : suffixEdge ≠ cycleEdge₀ := by
  intro h
  exact (by decide : s((1 : Fin 6), 2) ≠ s((3 : Fin 6), 4))
    (congrArg Subtype.val h)

theorem suffixEdge_ne_cycleEdge₁ : suffixEdge ≠ cycleEdge₁ := by
  intro h
  exact (by decide : s((1 : Fin 6), 2) ≠ s((4 : Fin 6), 5))
    (congrArg Subtype.val h)

theorem suffixEdge_ne_cycleEdge₂ : suffixEdge ≠ cycleEdge₂ := by
  intro h
  exact (by decide : s((1 : Fin 6), 2) ≠ s((5 : Fin 6), 3))
    (congrArg Subtype.val h)

theorem cycleEdge₀_ne_cycleEdge₁ : cycleEdge₀ ≠ cycleEdge₁ := by
  intro h
  exact (by decide : s((3 : Fin 6), 4) ≠ s((4 : Fin 6), 5))
    (congrArg Subtype.val h)

theorem cycleEdge₀_ne_cycleEdge₂ : cycleEdge₀ ≠ cycleEdge₂ := by
  intro h
  exact (by decide : s((3 : Fin 6), 4) ≠ s((5 : Fin 6), 3))
    (congrArg Subtype.val h)

theorem cycleEdge₁_ne_cycleEdge₂ : cycleEdge₁ ≠ cycleEdge₂ := by
  intro h
  exact (by decide : s((4 : Fin 6), 5) ≠ s((5 : Fin 6), 3))
    (congrArg Subtype.val h)

theorem suffixEdge_ne_headEdge : suffixEdge ≠ headEdge :=
  headEdge_ne_suffixEdge.symm
theorem cycleEdge₀_ne_headEdge : cycleEdge₀ ≠ headEdge :=
  headEdge_ne_cycleEdge₀.symm
theorem cycleEdge₁_ne_headEdge : cycleEdge₁ ≠ headEdge :=
  headEdge_ne_cycleEdge₁.symm
theorem cycleEdge₂_ne_headEdge : cycleEdge₂ ≠ headEdge :=
  headEdge_ne_cycleEdge₂.symm
theorem cycleEdge₀_ne_suffixEdge : cycleEdge₀ ≠ suffixEdge :=
  suffixEdge_ne_cycleEdge₀.symm
theorem cycleEdge₁_ne_suffixEdge : cycleEdge₁ ≠ suffixEdge :=
  suffixEdge_ne_cycleEdge₁.symm
theorem cycleEdge₂_ne_suffixEdge : cycleEdge₂ ≠ suffixEdge :=
  suffixEdge_ne_cycleEdge₂.symm
theorem cycleEdge₁_ne_cycleEdge₀ : cycleEdge₁ ≠ cycleEdge₀ :=
  cycleEdge₀_ne_cycleEdge₁.symm
theorem cycleEdge₂_ne_cycleEdge₀ : cycleEdge₂ ≠ cycleEdge₀ :=
  cycleEdge₀_ne_cycleEdge₂.symm
theorem cycleEdge₂_ne_cycleEdge₁ : cycleEdge₂ ≠ cycleEdge₁ :=
  cycleEdge₁_ne_cycleEdge₂.symm

attribute [simp] headEdge_ne_suffixEdge headEdge_ne_cycleEdge₀
  headEdge_ne_cycleEdge₁ headEdge_ne_cycleEdge₂
  suffixEdge_ne_cycleEdge₀ suffixEdge_ne_cycleEdge₁
  suffixEdge_ne_cycleEdge₂ cycleEdge₀_ne_cycleEdge₁
  cycleEdge₀_ne_cycleEdge₂ cycleEdge₁_ne_cycleEdge₂
  suffixEdge_ne_headEdge cycleEdge₀_ne_headEdge cycleEdge₁_ne_headEdge
  cycleEdge₂_ne_headEdge cycleEdge₀_ne_suffixEdge
  cycleEdge₁_ne_suffixEdge cycleEdge₂_ne_suffixEdge
  cycleEdge₁_ne_cycleEdge₀ cycleEdge₂_ne_cycleEdge₀
  cycleEdge₂_ne_cycleEdge₁


noncomputable def domain : shb_ExplorationDomain (Fin 6) where
  graph := graph
  active :=
    {canonicalEdgeSegment graph headEdge,
      canonicalEdgeSegment graph suffixEdge}
  active_supported := by
    intro seg hseg edge hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hseg
    rcases hseg with rfl | rfl
    · change edge ∈ (canonicalEdgeSegment graph headEdge).edgeSet at hedge
      rw [canonicalEdgeSegment_edgeSet] at hedge
      simp only [Set.mem_singleton_iff] at hedge
      subst edge
      exact SimpleGraph.mem_edgeFinset.mp headEdge.2
    · change edge ∈ (canonicalEdgeSegment graph suffixEdge).edgeSet at hedge
      rw [canonicalEdgeSegment_edgeSet] at hedge
      simp only [Set.mem_singleton_iff] at hedge
      subst edge
      exact SimpleGraph.mem_edgeFinset.mp suffixEdge.2

@[simp] theorem domain_graph : domain.graph = graph := rfl

@[simp] theorem head_active :
    canonicalEdgeSegment graph headEdge ∈ domain.active := by
  simp [domain]

@[simp] theorem suffix_active :
    canonicalEdgeSegment graph suffixEdge ∈ domain.active := by
  simp [domain]



def superposition : domain.graph.edgeFinset → Nat := fun e =>
  unitFlux domain.graph headEdge e + unitFlux domain.graph suffixEdge e +
    2 * unitFlux domain.graph cycleEdge₀ e +
    2 * unitFlux domain.graph cycleEdge₁ e +
    2 * unitFlux domain.graph cycleEdge₂ e


def oddCycleFlux : domain.graph.edgeFinset → Nat := fun e =>
  unitFlux domain.graph cycleEdge₀ e +
    unitFlux domain.graph cycleEdge₁ e +
    unitFlux domain.graph cycleEdge₂ e

theorem edge_cases (e : domain.graph.edgeFinset) :
    e = headEdge ∨ e = suffixEdge ∨ e = cycleEdge₀ ∨
      e = cycleEdge₁ ∨ e = cycleEdge₂ := by
  have he : e.1 ∈ graph.edgeFinset := by
    simpa only [domain_graph] using e.2
  rw [graph_edgeFinset] at he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with he | he | he | he | he
  · exact Or.inl (Subtype.ext he)
  · exact Or.inr (Or.inl (Subtype.ext he))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext he)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext he))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Subtype.ext he))))

@[simp] theorem superposition_head : superposition headEdge = 1 := by
  change (((((if headEdge = headEdge then 1 else 0) +
    (if headEdge = suffixEdge then 1 else 0)) +
    2 * (if headEdge = cycleEdge₀ then 1 else 0)) +
    2 * (if headEdge = cycleEdge₁ then 1 else 0)) +
    2 * (if headEdge = cycleEdge₂ then 1 else 0)) = 1
  simp

@[simp] theorem superposition_suffix : superposition suffixEdge = 1 := by
  change (((((if suffixEdge = headEdge then 1 else 0) +
    (if suffixEdge = suffixEdge then 1 else 0)) +
    2 * (if suffixEdge = cycleEdge₀ then 1 else 0)) +
    2 * (if suffixEdge = cycleEdge₁ then 1 else 0)) +
    2 * (if suffixEdge = cycleEdge₂ then 1 else 0)) = 1
  simp

@[simp] theorem superposition_cycle₀ : superposition cycleEdge₀ = 2 := by
  change (((((if cycleEdge₀ = headEdge then 1 else 0) +
    (if cycleEdge₀ = suffixEdge then 1 else 0)) +
    2 * (if cycleEdge₀ = cycleEdge₀ then 1 else 0)) +
    2 * (if cycleEdge₀ = cycleEdge₁ then 1 else 0)) +
    2 * (if cycleEdge₀ = cycleEdge₂ then 1 else 0)) = 2
  simp

@[simp] theorem superposition_cycle₁ : superposition cycleEdge₁ = 2 := by
  change (((((if cycleEdge₁ = headEdge then 1 else 0) +
    (if cycleEdge₁ = suffixEdge then 1 else 0)) +
    2 * (if cycleEdge₁ = cycleEdge₀ then 1 else 0)) +
    2 * (if cycleEdge₁ = cycleEdge₁ then 1 else 0)) +
    2 * (if cycleEdge₁ = cycleEdge₂ then 1 else 0)) = 2
  simp

@[simp] theorem superposition_cycle₂ : superposition cycleEdge₂ = 2 := by
  change (((((if cycleEdge₂ = headEdge then 1 else 0) +
    (if cycleEdge₂ = suffixEdge then 1 else 0)) +
    2 * (if cycleEdge₂ = cycleEdge₀ then 1 else 0)) +
    2 * (if cycleEdge₂ = cycleEdge₁ then 1 else 0)) +
    2 * (if cycleEdge₂ = cycleEdge₂ then 1 else 0)) = 2
  simp

@[simp] theorem oddCycleFlux_head : oddCycleFlux headEdge = 0 := by
  change ((if headEdge = cycleEdge₀ then 1 else 0) +
    (if headEdge = cycleEdge₁ then 1 else 0) +
    (if headEdge = cycleEdge₂ then 1 else 0)) = 0
  simp

@[simp] theorem oddCycleFlux_suffix : oddCycleFlux suffixEdge = 0 := by
  change ((if suffixEdge = cycleEdge₀ then 1 else 0) +
    (if suffixEdge = cycleEdge₁ then 1 else 0) +
    (if suffixEdge = cycleEdge₂ then 1 else 0)) = 0
  simp

@[simp] theorem oddCycleFlux_cycle₀ : oddCycleFlux cycleEdge₀ = 1 := by
  change ((if cycleEdge₀ = cycleEdge₀ then 1 else 0) +
    (if cycleEdge₀ = cycleEdge₁ then 1 else 0) +
    (if cycleEdge₀ = cycleEdge₂ then 1 else 0)) = 1
  simp

@[simp] theorem oddCycleFlux_cycle₁ : oddCycleFlux cycleEdge₁ = 1 := by
  change ((if cycleEdge₁ = cycleEdge₀ then 1 else 0) +
    (if cycleEdge₁ = cycleEdge₁ then 1 else 0) +
    (if cycleEdge₁ = cycleEdge₂ then 1 else 0)) = 1
  simp

@[simp] theorem oddCycleFlux_cycle₂ : oddCycleFlux cycleEdge₂ = 1 := by
  change ((if cycleEdge₂ = cycleEdge₀ then 1 else 0) +
    (if cycleEdge₂ = cycleEdge₁ then 1 else 0) +
    (if cycleEdge₂ = cycleEdge₂ then 1 else 0)) = 1
  simp

theorem unitHead_le_superposition :
    unitFlux domain.graph headEdge ≤ superposition := by
  intro e
  have hu : unitFlux domain.graph headEdge e ≤ 1 := by
    change (if e = headEdge then 1 else 0) ≤ 1
    split <;> omega
  rcases edge_cases e with rfl | rfl | rfl | rfl | rfl <;>
    simp only [superposition_head, superposition_suffix,
      superposition_cycle₀, superposition_cycle₁, superposition_cycle₂] <;>
    omega

theorem oddCycleFlux_le_superposition : oddCycleFlux ≤ superposition := by
  intro e
  rcases edge_cases e with rfl | rfl | rfl | rfl | rfl <;> simp


def headSplit : Finset (Copy domain.graph superposition) :=
  univ.filter (fun i => i.2.val < unitFlux domain.graph headEdge i.1)


def oddCycleSplit : Finset (Copy domain.graph superposition) :=
  univ.filter (fun i => i.2.val < oddCycleFlux i.1)

@[simp] theorem profileFlux_headSplit :
    profileFlux domain.graph superposition headSplit =
      unitFlux domain.graph headEdge := by
  exact profileFlux_surj domain.graph superposition
    (unitFlux domain.graph headEdge) unitHead_le_superposition

@[simp] theorem profileFlux_oddCycleSplit :
    profileFlux domain.graph superposition oddCycleSplit = oddCycleFlux := by
  exact profileFlux_surj domain.graph superposition oddCycleFlux
    oddCycleFlux_le_superposition



def suffixEvenFlux : domain.graph.edgeFinset → Nat := fun e =>
  unitFlux domain.graph suffixEdge e +
    2 * unitFlux domain.graph cycleEdge₀ e +
    2 * unitFlux domain.graph cycleEdge₁ e +
    2 * unitFlux domain.graph cycleEdge₂ e

@[simp] theorem suffixEvenFlux_head : suffixEvenFlux headEdge = 0 := by
  change ((((if headEdge = suffixEdge then 1 else 0) +
    2 * (if headEdge = cycleEdge₀ then 1 else 0)) +
    2 * (if headEdge = cycleEdge₁ then 1 else 0)) +
    2 * (if headEdge = cycleEdge₂ then 1 else 0)) = 0
  simp

@[simp] theorem suffixEvenFlux_suffix : suffixEvenFlux suffixEdge = 1 := by
  change ((((if suffixEdge = suffixEdge then 1 else 0) +
    2 * (if suffixEdge = cycleEdge₀ then 1 else 0)) +
    2 * (if suffixEdge = cycleEdge₁ then 1 else 0)) +
    2 * (if suffixEdge = cycleEdge₂ then 1 else 0)) = 1
  simp

@[simp] theorem suffixEvenFlux_cycle₀ : suffixEvenFlux cycleEdge₀ = 2 := by
  change ((((if cycleEdge₀ = suffixEdge then 1 else 0) +
    2 * (if cycleEdge₀ = cycleEdge₀ then 1 else 0)) +
    2 * (if cycleEdge₀ = cycleEdge₁ then 1 else 0)) +
    2 * (if cycleEdge₀ = cycleEdge₂ then 1 else 0)) = 2
  simp

@[simp] theorem suffixEvenFlux_cycle₁ : suffixEvenFlux cycleEdge₁ = 2 := by
  change ((((if cycleEdge₁ = suffixEdge then 1 else 0) +
    2 * (if cycleEdge₁ = cycleEdge₀ then 1 else 0)) +
    2 * (if cycleEdge₁ = cycleEdge₁ then 1 else 0)) +
    2 * (if cycleEdge₁ = cycleEdge₂ then 1 else 0)) = 2
  simp

@[simp] theorem suffixEvenFlux_cycle₂ : suffixEvenFlux cycleEdge₂ = 2 := by
  change ((((if cycleEdge₂ = suffixEdge then 1 else 0) +
    2 * (if cycleEdge₂ = cycleEdge₀ then 1 else 0)) +
    2 * (if cycleEdge₂ = cycleEdge₁ then 1 else 0)) +
    2 * (if cycleEdge₂ = cycleEdge₂ then 1 else 0)) = 2
  simp

@[simp] theorem unitHead_head :
    unitFlux domain.graph headEdge headEdge = 1 := by
  change (if headEdge = headEdge then 1 else 0) = 1
  simp

@[simp] theorem unitHead_suffix :
    unitFlux domain.graph headEdge suffixEdge = 0 := by
  change (if suffixEdge = headEdge then 1 else 0) = 0
  simp

@[simp] theorem unitHead_cycle₀ :
    unitFlux domain.graph headEdge cycleEdge₀ = 0 := by
  change (if cycleEdge₀ = headEdge then 1 else 0) = 0
  simp

@[simp] theorem unitHead_cycle₁ :
    unitFlux domain.graph headEdge cycleEdge₁ = 0 := by
  change (if cycleEdge₁ = headEdge then 1 else 0) = 0
  simp

@[simp] theorem unitHead_cycle₂ :
    unitFlux domain.graph headEdge cycleEdge₂ = 0 := by
  change (if cycleEdge₂ = headEdge then 1 else 0) = 0
  simp

theorem superposition_sub_unitHead :
    (fun e => superposition e - unitFlux domain.graph headEdge e) =
      suffixEvenFlux := by
  funext e
  rcases edge_cases e with rfl | rfl | rfl | rfl | rfl <;>
    simp only [superposition_head, superposition_suffix,
      superposition_cycle₀, superposition_cycle₁, superposition_cycle₂,
      suffixEvenFlux_head, suffixEvenFlux_suffix, suffixEvenFlux_cycle₀,
      suffixEvenFlux_cycle₁, suffixEvenFlux_cycle₂,
      unitHead_head, unitHead_suffix, unitHead_cycle₀, unitHead_cycle₁,
      unitHead_cycle₂]

@[simp] theorem profileFlux_headSplit_compl :
    profileFlux domain.graph superposition (univ \ headSplit) =
      suffixEvenFlux := by
  rw [profileFlux_compl, profileFlux_headSplit,
    superposition_sub_unitHead]



abbrev residualGraph : SimpleGraph (Fin 6) :=
  domain.graph.deleteEdges (canonicalEdgeSegment domain.graph headEdge).edgeSet

abbrev residualLe : residualGraph ≤ domain.graph :=
  domain.graph.deleteEdges_le (canonicalEdgeSegment domain.graph headEdge).edgeSet

noncomputable def restrictResidual
    (p : domain.graph.edgeFinset → Nat) : residualGraph.edgeFinset → Nat :=
  fun e => p ⟨e.1, edgeFinset_subset residualLe e.2⟩

theorem extendFlux_restrictResidual
    (p : domain.graph.edgeFinset → Nat) (hp : p headEdge = 0) :
    extendFlux residualLe (restrictResidual p) = p := by
  funext e
  by_cases he : e = headEdge
  · subst e
    rw [show extendFlux residualLe (restrictResidual p) headEdge = 0 by
      unfold extendFlux
      rw [dif_neg (firstEdge_not_mem_delete domain headEdge)]]
    exact hp.symm
  · have hmem : e.1 ∈ residualGraph.edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_deleteEdges,
        canonicalEdgeSegment_edgeSet]
      refine ⟨SimpleGraph.mem_edgeFinset.mp e.2, ?_⟩
      simpa only [Set.mem_singleton_iff, Subtype.ext_iff] using he
    unfold extendFlux
    rw [dif_pos hmem]
    rfl

def residualSuffix : residualGraph.edgeFinset :=
  residualEdge domain headEdge suffixEdge headEdge_ne_suffixEdge

def residualCycle₀ : residualGraph.edgeFinset :=
  residualEdge domain headEdge cycleEdge₀ headEdge_ne_cycleEdge₀

def residualCycle₁ : residualGraph.edgeFinset :=
  residualEdge domain headEdge cycleEdge₁ headEdge_ne_cycleEdge₁

def residualCycle₂ : residualGraph.edgeFinset :=
  residualEdge domain headEdge cycleEdge₂ headEdge_ne_cycleEdge₂

theorem residualCycle₀_ne_suffix : residualCycle₀ ≠ residualSuffix := by
  intro h
  apply cycleEdge₀_ne_suffixEdge
  apply Subtype.ext
  simpa [residualCycle₀, residualSuffix, residualEdge] using
    congrArg Subtype.val h



theorem residual_complete_suffixEven :
    BackboneTwoEdgeBondProgram.program.CompleteEvent
      (shb_BackboneExplorationDomain.advance domain
        (canonicalEdgeSegment domain.graph headEdge))
      [canonicalEdgeSegment domain.graph suffixEdge]
      (restrictResidual suffixEvenFlux) := by
  let d' := shb_BackboneExplorationDomain.advance domain
    (canonicalEdgeSegment domain.graph headEdge)
  have hunit := program_complete_canonical_singleton_unitFlux d'
    residualSuffix
    (residualEdge_active_advance domain headEdge suffixEdge
      headEdge_ne_suffixEdge suffix_active)
  have hunit' :
      BackboneTwoEdgeBondProgram.program.CompleteEvent d'
        [canonicalEdgeSegment domain.graph suffixEdge]
        (unitFlux d'.graph residualSuffix) := by
    simpa only [d', residualGraph, residualSuffix,
      residualEdge_canonical_eq] using hunit
  have hodd : ∀ e : d'.graph.edgeFinset,
      oddBit (restrictResidual suffixEvenFlux e) =
        oddBit (unitFlux d'.graph residualSuffix e) := by
    intro e
    let ambient : domain.graph.edgeFinset :=
      ⟨e.1, edgeFinset_subset residualLe e.2⟩
    rcases edge_cases ambient with hhead | hsuffix | hc₀ | hc₁ | hc₂
    · have hmem := e.2
      change e.1 ∈ residualGraph.edgeFinset at hmem
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_deleteEdges,
        canonicalEdgeSegment_edgeSet] at hmem
      have heval : e.1 = headEdge.1 := by
        simpa [ambient] using congrArg Subtype.val hhead
      exact (hmem.2 (by simp [heval])).elim
    · have he : e = residualSuffix := by
        apply Subtype.ext
        simpa [ambient, residualSuffix, residualEdge] using
          congrArg Subtype.val hsuffix
      change oddBit (suffixEvenFlux ambient) =
        oddBit (if e = residualSuffix then 1 else 0)
      rw [hsuffix, suffixEvenFlux_suffix, if_pos he]
    · have he : e = residualCycle₀ := by
        apply Subtype.ext
        simpa [ambient, residualCycle₀, residualEdge] using
          congrArg Subtype.val hc₀
      have hne : e ≠ residualSuffix := fun h =>
        residualCycle₀_ne_suffix (he.symm.trans h)
      change oddBit (suffixEvenFlux ambient) =
        oddBit (if e = residualSuffix then 1 else 0)
      rw [hc₀, suffixEvenFlux_cycle₀, if_neg hne]
      decide
    · have he : e = residualCycle₁ := by
        apply Subtype.ext
        simpa [ambient, residualCycle₁, residualEdge] using
          congrArg Subtype.val hc₁
      have hresne : residualCycle₁ ≠ residualSuffix := by
        intro h
        apply cycleEdge₁_ne_suffixEdge
        apply Subtype.ext
        simpa [residualCycle₁, residualSuffix, residualEdge] using
          congrArg Subtype.val h
      have hne : e ≠ residualSuffix := fun h => hresne (he.symm.trans h)
      change oddBit (suffixEvenFlux ambient) =
        oddBit (if e = residualSuffix then 1 else 0)
      rw [hc₁, suffixEvenFlux_cycle₁, if_neg hne]
      decide
    · have he : e = residualCycle₂ := by
        apply Subtype.ext
        simpa [ambient, residualCycle₂, residualEdge] using
          congrArg Subtype.val hc₂
      have hresne : residualCycle₂ ≠ residualSuffix := by
        intro h
        apply cycleEdge₂_ne_suffixEdge
        apply Subtype.ext
        simpa [residualCycle₂, residualSuffix, residualEdge] using
          congrArg Subtype.val h
      have hne : e ≠ residualSuffix := fun h => hresne (he.symm.trans h)
      change oddBit (suffixEvenFlux ambient) =
        oddBit (if e = residualSuffix then 1 else 0)
      rw [hc₂, suffixEvenFlux_cycle₂, if_neg hne]
      decide
  have hbits :
      fluxBitConfig d'.graph
          (BackboneTwoEdgeBondProgram.program (V := Fin 6)).bit
          (restrictResidual suffixEvenFlux) =
        fluxBitConfig d'.graph
          (BackboneTwoEdgeBondProgram.program (V := Fin 6)).bit
          (unitFlux d'.graph residualSuffix) := by
    change fluxBitConfig d'.graph oddBit (restrictResidual suffixEvenFlux) =
      fluxBitConfig d'.graph oddBit (unitFlux d'.graph residualSuffix)
    funext b
    unfold fluxBitConfig
    split
    · rename_i hleft
      split
      · rename_i hright
        convert hodd ⟨b, hleft⟩ using 1
      · rename_i hright
        exact (hright hleft).elim
    · rename_i hleft
      split
      · rename_i hright
        exact (hleft hright).elim
      · rfl
  change BackboneTwoEdgeBondProgram.program.CompleteEvent d'
    [canonicalEdgeSegment domain.graph suffixEdge]
    (restrictResidual suffixEvenFlux)
  unfold BondwiseSegmentProgram.CompleteEvent
    BondwiseSegmentProgram.TerminalEvent BondwiseSuffixEvent at hunit' ⊢
  constructor
  · have heq := congrArg
      (fun config => (BackboneTwoEdgeBondProgram.program (V := Fin 6)).scan.Selects
        (fun _ e => config e)
        ((BackboneTwoEdgeBondProgram.program (V := Fin 6)).initial d')
        ((BackboneTwoEdgeBondProgram.program (V := Fin 6)).encode d'
          [canonicalEdgeSegment domain.graph suffixEdge])) hbits
    exact Eq.mpr heq hunit'.1
  · let st := BackboneTwoEdgeBondProgram.program.scan.residual
        (BackboneTwoEdgeBondProgram.program.initial d')
        (BackboneTwoEdgeBondProgram.program.encode d'
          [canonicalEdgeSegment domain.graph suffixEdge])
    have heq := congrArg
      (fun omega => (BackboneTwoEdgeBondProgram.program (V := Fin 6)).terminal
        st omega) hbits
    exact Eq.mpr heq hunit'.2


theorem suffixEven_event :
    ((BackboneTwoEdgeBondProgram.program (V := Fin 6)).liftedResidualRunSpec
      domain (canonicalEdgeSegment domain.graph headEdge)
      [canonicalEdgeSegment domain.graph suffixEdge]).Event
      domain.graph suffixEvenFlux := by
  rw [BondwiseSegmentProgram.liftedResidualRunSpec_event]
  exact ⟨restrictResidual suffixEvenFlux,
    extendFlux_restrictResidual suffixEvenFlux suffixEvenFlux_head,
    ((BackboneTwoEdgeBondProgram.program (V := Fin 6)).runSpec_event
      (shb_BackboneExplorationDomain.advance domain
        (canonicalEdgeSegment domain.graph headEdge))
      [canonicalEdgeSegment domain.graph suffixEdge]
      (restrictResidual suffixEvenFlux)).mpr residual_complete_suffixEven⟩

theorem sources_unitFlux_eq_toFinset
    (e : domain.graph.edgeFinset) :
    sources domain.graph (ofEdgeFun domain.graph (unitFlux domain.graph e)) =
      e.1.toFinset := by
  rw [sources_unitFlux]
  change {e.1.out.1, e.1.out.2} = e.1.toFinset
  rw [← Sym2.toFinset_mk_eq]
  exact congrArg Sym2.toFinset e.1.out_eq


theorem oddCycle_sources_empty :
    sources domain.graph (ofEdgeFun domain.graph oddCycleFlux) = ∅ := by
  change sources domain.graph (ofEdgeFun domain.graph
    (fun e => (unitFlux domain.graph cycleEdge₀ e +
      unitFlux domain.graph cycleEdge₁ e) +
      unitFlux domain.graph cycleEdge₂ e)) = ∅
  rw [← ofEdgeFun_add, ← ofEdgeFun_add, sources_add, sources_add,
    sources_unitFlux_eq_toFinset, sources_unitFlux_eq_toFinset,
    sources_unitFlux_eq_toFinset]
  change s((3 : Fin 6), 4).toFinset ∆ s((4 : Fin 6), 5).toFinset ∆
    s((5 : Fin 6), 3).toFinset = ∅
  decide


theorem oddCycle_vacuum_event :
    (residualVacuumRunSpec domain
      (canonicalEdgeSegment domain.graph headEdge)).Event
      domain.graph oddCycleFlux := by
  rw [residualVacuumRunSpec_event]
  unfold liftedResidualVacuum
  refine ⟨restrictResidual oddCycleFlux,
    extendFlux_restrictResidual oddCycleFlux oddCycleFlux_head, ?_⟩
  change sources residualGraph
    (ofEdgeFun residualGraph (restrictResidual oddCycleFlux)) = ∅
  rw [← sources_extendFlux residualLe]
  rw [extendFlux_restrictResidual oddCycleFlux oddCycleFlux_head]
  exact oddCycle_sources_empty



theorem suffix_event_cycle₀_not_odd
    (p : domain.graph.edgeFinset → Nat)
    (h : ((BackboneTwoEdgeBondProgram.program (V := Fin 6)).liftedResidualRunSpec
      domain (canonicalEdgeSegment domain.graph headEdge)
      [canonicalEdgeSegment domain.graph suffixEdge]).Event domain.graph p) :
    ¬ Odd (p cycleEdge₀) := by
  rw [BondwiseSegmentProgram.liftedResidualRunSpec_event] at h
  obtain ⟨r, hrext, hrun⟩ := h
  rw [(BackboneTwoEdgeBondProgram.program (V := Fin 6)).runSpec_event] at hrun
  obtain ⟨e, heSegment, _, _, _, hfinished⟩ :=
    program_complete_singleton_data
      (shb_BackboneExplorationDomain.advance domain
        (canonicalEdgeSegment domain.graph headEdge)) r
      (canonicalEdgeSegment domain.graph suffixEdge) hrun
  have heResidual : e = residualSuffix := by
    apply canonicalEdgeSegment_injective residualGraph
    calc
      canonicalEdgeSegment residualGraph e =
          canonicalEdgeSegment domain.graph suffixEdge := heSegment
      _ = canonicalEdgeSegment residualGraph residualSuffix :=
        (residualEdge_canonical_eq domain headEdge suffixEdge
          headEdge_ne_suffixEdge).symm
  subst e
  intro hpOdd
  have hrOdd : Odd (r residualCycle₀) := by
    have hval := congrFun hrext cycleEdge₀
    have hmem : cycleEdge₀.1 ∈ residualGraph.edgeFinset :=
      secondEdge_mem_delete domain headEdge cycleEdge₀
        headEdge_ne_cycleEdge₀
    have hval' : r residualCycle₀ = p cycleEdge₀ := by
      unfold extendFlux at hval
      split at hval
      · rename_i hm
        convert hval using 1
      · rename_i hm
        exact (hm hmem).elim
    rwa [hval']
  have htrue : fluxBitConfig residualGraph oddBit r cycleEdge₀.1 = true := by
    unfold fluxBitConfig
    split
    · rename_i hm
      have : r ⟨cycleEdge₀.1, hm⟩ = r residualCycle₀ := by
        congr 1
      rw [this]
      exact (oddBit_eq_true_iff _).mpr hrOdd
    · rename_i hm
      exact (hm residualCycle₀.2).elim
  have hfind :
      (residualGraph.edgeFinset.erase residualSuffix.1).1.toList.find?
          (fun b => fluxBitConfig residualGraph oddBit r b) = none := by
    simpa [BackboneTwoEdgeBondProgram.scan,
      shb_DynamicEdgeExploration.firstAdmissible] using hfinished
  have hmemList : cycleEdge₀.1 ∈
      (residualGraph.edgeFinset.erase residualSuffix.1).1.toList := by
    apply Finset.mem_toList.mpr
    apply Finset.mem_erase.mpr
    refine ⟨?_, residualCycle₀.2⟩
    intro hval
    apply residualCycle₀_ne_suffix
    exact Subtype.ext hval
  exact ((List.find?_eq_none.mp hfind) cycleEdge₀.1 hmemList htrue).elim



def cycle₀Copy₀ : Copy domain.graph superposition :=
  ⟨cycleEdge₀, ⟨0, by simp⟩⟩

theorem oddCycleSplit_filter_cycle₀ :
    oddCycleSplit.filter
        (fun i : Copy domain.graph superposition => i.1 = cycleEdge₀) =
      {cycle₀Copy₀} := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hi, hedge⟩
    unfold oddCycleSplit at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rcases i with ⟨e, j⟩
    dsimp only at hedge hi ⊢
    subst e
    unfold cycle₀Copy₀
    rw [Sigma.mk.inj_iff]
    have hflux : oddCycleFlux cycleEdge₀ = 1 := oddCycleFlux_cycle₀
    rw [hflux] at hi
    have hj : j.val = 0 := by omega
    refine ⟨rfl, heq_of_eq ?_⟩
    exact Fin.ext hj
  · intro hi
    subst i
    constructor
    · unfold oddCycleSplit cycle₀Copy₀
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp
    · rfl

theorem filter_symmDiff
    (S T : Finset (Copy domain.graph superposition)) :
    (S ∆ T).filter (fun i => i.1 = cycleEdge₀) =
      S.filter (fun i => i.1 = cycleEdge₀) ∆
        T.filter (fun i => i.1 = cycleEdge₀) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_symmDiff]
  tauto

theorem odd_card_symmDiff_singleton_iff_not
    {A : Type*} [DecidableEq A] (S : Finset A) (a : A) :
    Odd #(S ∆ {a}) ↔ ¬ Odd #S := by
  by_cases ha : a ∈ S
  · have heq : S ∆ {a} = S.erase a := by
      ext x
      simp only [Finset.mem_symmDiff, Finset.mem_singleton,
        Finset.mem_erase]
      by_cases hxa : x = a
      · subst x
        simp [ha]
      · simp [hxa]
    rw [heq, Finset.card_erase_of_mem ha]
    rw [Nat.odd_sub (Finset.card_pos.mpr ⟨a, ha⟩)]
    simp
  · have heq : S ∆ {a} = insert a S := by
      ext x
      simp only [Finset.mem_symmDiff, Finset.mem_singleton,
        Finset.mem_insert]
      by_cases hxa : x = a
      · subst x
        simp [ha]
      · simp [hxa]
    rw [heq, Finset.card_insert_of_notMem ha]
    rw [Nat.odd_add]
    simp



theorem profile_cycle₀_odd_symmDiff_iff_not
    (T : Finset (Copy domain.graph superposition)) :
    Odd (profileFlux domain.graph superposition (T ∆ oddCycleSplit)
      cycleEdge₀) ↔
      ¬ Odd (profileFlux domain.graph superposition T cycleEdge₀) := by
  unfold profileFlux
  let A := T.filter (fun i : Copy domain.graph superposition =>
    i.1 = cycleEdge₀)
  have hset :
      (T ∆ oddCycleSplit).filter (fun i => i.1 = cycleEdge₀) =
        A ∆ {cycle₀Copy₀} := by
    dsimp only [A]
    rw [filter_symmDiff T oddCycleSplit, oddCycleSplit_filter_cycle₀]
    rfl
  change Odd #((T ∆ oddCycleSplit).filter
      (fun i => i.1 = cycleEdge₀)) ↔ ¬ Odd #A
  rw [hset]
  exact odd_card_symmDiff_singleton_iff_not A cycle₀Copy₀



@[simp] theorem profileFlux_empty :
    profileFlux domain.graph superposition
      (∅ : Finset (Copy domain.graph superposition)) = 0 := by
  funext e
  simp [profileFlux]
  rfl





theorem no_residualVacuum_suffix_covariance
    (path : Finset (Copy domain.graph superposition)) :
    ¬ BondwiseRunToggleCovariance
      (residualVacuumRunSpec domain
        (canonicalEdgeSegment domain.graph headEdge))
      ((BackboneTwoEdgeBondProgram.program (V := Fin 6)).liftedResidualRunSpec
        domain (canonicalEdgeSegment domain.graph headEdge)
        [canonicalEdgeSegment domain.graph suffixEdge])
      domain.graph superposition path := by
  intro hcov
  have hvacuumZero :
      (residualVacuumRunSpec domain
        (canonicalEdgeSegment domain.graph headEdge)).Event
        domain.graph (profileFlux domain.graph superposition ∅) := by
    rw [profileFlux_empty]
    exact vacuum_zero domain headEdge
  have hsuffixPath := (hcov ∅).mp hvacuumZero
  have hsuffixPath' :
      ((BackboneTwoEdgeBondProgram.program (V := Fin 6)).liftedResidualRunSpec
        domain (canonicalEdgeSegment domain.graph headEdge)
        [canonicalEdgeSegment domain.graph suffixEdge]).Event domain.graph
        (profileFlux domain.graph superposition path) := by
    have heq : (∅ : Finset (Copy domain.graph superposition)) ∆ path = path :=
      symmDiff_eq_right.mpr rfl
    rw [heq] at hsuffixPath
    exact hsuffixPath
  have hpathEven :
      ¬ Odd (profileFlux domain.graph superposition path cycleEdge₀) :=
    suffix_event_cycle₀_not_odd _ hsuffixPath'
  have hsuffixToggle := (hcov oddCycleSplit).mp (by
    rw [profileFlux_oddCycleSplit]
    exact oddCycle_vacuum_event)
  have htoggleOdd :
      Odd (profileFlux domain.graph superposition
        (oddCycleSplit ∆ path) cycleEdge₀) := by
    rw [symmDiff_comm]
    exact (profile_cycle₀_odd_symmDiff_iff_not path).mpr hpathEven
  exact (suffix_event_cycle₀_not_odd _ hsuffixToggle) htoggleOdd



theorem superposition_weight_pos
    (beta : Real) (J : Sym2 (Fin 6) → Real)
    (hbeta : 0 < beta) (hJ : ∀ g, 0 < J g) :
    0 < weight domain.graph beta J
      (ofEdgeFun domain.graph superposition) := by
  unfold weight
  refine Finset.prod_pos (fun g _ => ?_)
  exact div_pos (pow_pos (mul_pos hbeta (hJ g)) _)
    (by positivity)


theorem right_rawPairFiberMass_pos
    (beta : Real) (J : Sym2 (Fin 6) → Real)
    (hbeta : 0 < beta) (hJ : ∀ g, 0 < J g) :
    0 < rawSourcePairFiberMass domain.graph beta J superposition
      (((BackboneTwoEdgeBondProgram.selectorSpec
          (V := Fin 6)).toPartialSelector.sourceClass domain
          [canonicalEdgeSegment domain.graph headEdge,
            canonicalEdgeSegment domain.graph suffixEdge]) ∆
        stepToggleSource
          (BackboneTwoEdgeBondProgram.selectorSpec
            (V := Fin 6)).toPartialSelector domain
          (canonicalEdgeSegment domain.graph headEdge)
          [canonicalEdgeSegment domain.graph suffixEdge])
      (shb_ActiveSegmentFiber domain
        (canonicalEdgeSegment domain.graph headEdge) head_active)
      (liftedResidualFiber
        (BackboneTwoEdgeBondProgram.selectorSpec
          (V := Fin 6)).toPartialSelector domain
        (canonicalEdgeSegment domain.graph headEdge)
        [canonicalEdgeSegment domain.graph suffixEdge]) := by
  let S := (BackboneTwoEdgeBondProgram.selectorSpec (V := Fin 6)).toPartialSelector
  let s := canonicalEdgeSegment domain.graph headEdge
  let t := canonicalEdgeSegment domain.graph suffixEdge
  let word := [s, t]
  let A := S.sourceClass domain word ∆
    stepToggleSource S domain s [t]
  let Q := fun T : Finset (Copy domain.graph superposition) =>
    shb_ActiveSegmentFiber domain s head_active
        (profileFlux domain.graph superposition T) ∧
      liftedResidualFiber S domain s [t]
        (profileFlux domain.graph superposition (univ \ T))
  have hresidual : liftedResidualFiber S domain s [t] suffixEvenFlux := by
    apply ((BackboneTwoEdgeBondProgram.selectorSpec
      (V := Fin 6)).liftedResidualFiber_iff_liftedRunEvent
        domain s [t] suffixEvenFlux).mpr
    exact (BondwiseSegmentProgram.liftedResidualRunSpec_event
      (BackboneTwoEdgeBondProgram.program (V := Fin 6)) domain s [t]
      suffixEvenFlux).mp suffixEven_event
  have hsource : RandomCurrent.sources (endsM domain.graph superposition)
      headSplit = A := by
    calc
      RandomCurrent.sources (endsM domain.graph superposition) headSplit =
          sources domain.graph (ofEdgeFun domain.graph
            (profileFlux domain.graph superposition headSplit)) :=
        FluxEdgeCopy.sources_eq domain.graph superposition headSplit
      _ = sources domain.graph
          (ofEdgeFun domain.graph (unitFlux domain.graph headEdge)) := by
        rw [profileFlux_headSplit]
      _ = {s.1, s.2.1} := sources_unitFlux domain.graph headEdge
      _ = A := by
        simp [A, stepToggleSource, word]
  have hQ : Q headSplit := by
    constructor
    · rw [profileFlux_headSplit]
      exact activeSegmentFiber_unitFlux domain headEdge head_active
    · rw [profileFlux_headSplit_compl]
      exact hresidual
  let witness : Fiber domain.graph superposition A Q :=
    ⟨headSplit, hsource, hQ⟩
  change 0 < rawSourcePairFiberMass domain.graph beta J superposition A
    (shb_ActiveSegmentFiber domain s head_active)
    (liftedResidualFiber S domain s [t])
  rw [rawSourcePairFiberMass_eq_labeled]
  unfold labeledSourcePairFiberMass
  exact Finset.sum_pos
    (fun _ _ => superposition_weight_pos beta J hbeta hJ)
    ⟨witness, Finset.mem_univ witness⟩



theorem coordinatePairContributes
    (beta : Real) (J : Sym2 (Fin 6) → Real)
    (hbeta : 0 < beta) (hJ : ∀ g, 0 < J g) :
    CoordinatePairContributes
      (BackboneTwoEdgeBondProgram.selectorSpec
        (V := Fin 6)).toPartialSelector
      beta J domain (canonicalEdgeSegment domain.graph headEdge)
      [canonicalEdgeSegment domain.graph suffixEdge] head_active
      superposition := by
  exact Or.inr (ne_of_gt (right_rawPairFiberMass_pos beta J hbeta hJ))



theorem not_canonicalComponentwiseToggleExists
    (beta : Real) (J : Sym2 (Fin 6) → Real)
    (hbeta : 0 < beta) (hJ : ∀ g, 0 < J g) :
    ¬ (BackboneTwoEdgeBondProgram.selectorSpec
      (V := Fin 6)).CanonicalComponentwiseToggleExists
      beta J domain (canonicalEdgeSegment domain.graph headEdge)
      [canonicalEdgeSegment domain.graph suffixEdge] head_active := by
  intro htoggle
  obtain ⟨path, _, hresidual⟩ :=
    htoggle superposition (coordinatePairContributes beta J hbeta hJ)
  exact no_residualVacuum_suffix_covariance path hresidual

end BackboneTwoEdgeCycleObstruction

end

end StatMech.Sharpness
