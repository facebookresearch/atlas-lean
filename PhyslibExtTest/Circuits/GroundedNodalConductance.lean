/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import PhyslibExt.Circuits.GroundedNodalConductance
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# Grounded nodal conductance checks

Focused checks for `PhyslibExt.Circuits.GroundedNodalConductance`
on three nodes and two branches `0 → 1` and `1 → 2`:

- both branches resistors with values `1` and `2`, grounded at
  `0`: the grounded nodal conductance matrix is positive definite
  and invertible;
- only branch `0 → 1` a resistor: node `2` has no resistor, and
  the grounded nodal conductance matrix is not positive definite.

These are elaboration and non-vacuity checks, not new results.
-/

namespace PhyslibExtTest.Circuits.GroundedNodalConductance

open Matrix MathlibExt.Combinatorics.Graph.ArcNetwork
  MathlibExt.Combinatorics.Graph.ArcNetworkLaplacian
  PhyslibExt.Circuits.LinearMNAStamping
  PhyslibExt.Circuits.GroundedNodalConductance

/-- Branch tails. -/
def tail2 : Fin 2 → Fin 3 := ![0, 1]
/-- Branch heads. -/
def head2 : Fin 2 → Fin 3 := ![1, 2]
/-- Resistances. -/
def R2 : Fin 2 → ℝ := ![1, 2]

lemma resistorGraph_connected :
    (resistorGraph tail2 head2 Finset.univ).Connected := by
  have h01 : (resistorGraph tail2 head2 Finset.univ).Adj 0 1 :=
    (SimpleGraph.fromRel_adj _ _ _).mpr
      ⟨by decide, Or.inl ⟨0, Finset.mem_univ _, rfl, rfl⟩⟩
  have h12 : (resistorGraph tail2 head2 Finset.univ).Adj 1 2 :=
    (SimpleGraph.fromRel_adj _ _ _).mpr
      ⟨by decide, Or.inl ⟨1, Finset.mem_univ _, rfl, rfl⟩⟩
  have hr : ∀ v, (resistorGraph tail2 head2 Finset.univ).Reachable 0 v := by
    intro v
    fin_cases v
    · rfl
    · exact h01.reachable
    · exact h01.reachable.trans h12.reachable
  exact ⟨fun u v => (hr u).symm.trans (hr v)⟩

lemma R2_pos : ∀ e ∈ (Finset.univ : Finset (Fin 2)), 0 < R2 e := by
  intro e _
  fin_cases e <;> norm_num [R2]

/-- Two resistors in series, grounded at node `0`: positive definite. -/
example :
    ((nodalConductance (physicalIncidence tail2 head2) Finset.univ R2).submatrix
      (Subtype.val : {v : Fin 3 // v ≠ 0} → Fin 3) Subtype.val).PosDef :=
  nodalConductance_grounded_posDef tail2 head2 Finset.univ R2 R2_pos 0
    resistorGraph_connected

/-- The same network grounded at node `2`: invertible. -/
example :
    IsUnit ((nodalConductance (physicalIncidence tail2 head2) Finset.univ R2).submatrix
      (Subtype.val : {v : Fin 3 // v ≠ 2} → Fin 3) (Subtype.val : {v : Fin 3 // v ≠ 2} → Fin 3)) :=
  nodalConductance_grounded_isUnit tail2 head2 Finset.univ R2 R2_pos 2
    resistorGraph_connected

/-- Negative case: with only branch `0 → 1` a resistor, the indicator of
node `2` is in the kernel and the grounded matrix is not positive definite. -/
example :
    ¬ ((nodalConductance (physicalIncidence tail2 head2) {0} R2).submatrix
      (Subtype.val : {v : Fin 3 // v ≠ 0} → Fin 3) Subtype.val).PosDef := by
  intro h
  set x : Fin 3 → ℝ := Pi.single 2 1 with hxdef
  have hflow : (incidenceMatrix (fun e : ({0} : Finset (Fin 2)) => tail2 e)
      (fun e : ({0} : Finset (Fin 2)) => head2 e))ᵀ *ᵥ x = 0 := by
    funext e
    rw [incidenceMatrix_transpose_mulVec_apply]
    obtain ⟨e, he⟩ := e
    rw [Finset.mem_singleton] at he
    subst he
    simp [hxdef, tail2, head2]
  have hker : nodalConductance (physicalIncidence tail2 head2) {0} R2 *ᵥ x = 0 := by
    rw [nodalConductance_physicalIncidence_eq, ← mulVec_mulVec, ← mulVec_mulVec, hflow,
      mulVec_zero, mulVec_zero]
  have hy : (fun i : {v : Fin 3 // v ≠ 0} => x i.1) ≠ 0 := fun h0 => by
    have := congrFun h0 ⟨2, by decide⟩
    simp [hxdef] at this
  have hpos := h.dotProduct_mulVec_pos hy
  have hzero : ((nodalConductance (physicalIncidence tail2 head2) {0} R2).submatrix
      (Subtype.val : {v : Fin 3 // v ≠ 0} → Fin 3) Subtype.val *ᵥ
        fun i : {v : Fin 3 // v ≠ 0} => x i.1) = 0 := by
    funext i
    have hsum := congrFun hker i.1
    simp only [mulVec, dotProduct, submatrix_apply, Pi.zero_apply] at hsum ⊢
    rw [Fintype.sum_eq_add_sum_subtype_ne _ (0 : Fin 3)] at hsum
    simpa [hxdef] using hsum
  rw [hzero, dotProduct_zero] at hpos
  exact lt_irrefl _ hpos

end PhyslibExtTest.Circuits.GroundedNodalConductance
