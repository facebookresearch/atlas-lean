/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation
import Code.Universality.RSWConnectorCentralFaceRetainedChoiceAudit










open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section



theorem rlc_retainedChoiceAudit_topWall_literalTerminalSquare :
    let f : Site 2 := ![-3, 1]
    let g : Site 2 := ![-3, 2]
    let p : Site 2 := ![-3, 2]
    let q : Site 2 := ![-2, 2]
    (hypercubicLattice 2).Adj f g ∧
      RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
          (rlc_dualReflect f) ∧
      sharedPrimalEdge f g = s(p, q) ∧
      p 1 = 2 ∧ p = g ∧ q ∈
        rlc_pathVertices rlc_retainedChoiceAuditLeft.1 ∧
      phb_doubleDualShift q = f := by
  dsimp only
  refine ⟨by simp [hypercubicLattice_adj, Fin.sum_univ_two], ?_, ?_,
    rfl, rfl, ?_, ?_⟩
  · refine ⟨by norm_num [rlc_dualReflect, rlc_dualReflectFun],
      ⟨![-2, 2], ?_, ?_⟩, ?_, ?_⟩
    · rw [rlc_retainedChoiceAudit_left_vertices]
      simp
    · ext i
      fin_cases i <;>
        simp [rlc_dualReflect, rlc_dualReflectFun,
          rlc_flipX, rlc_flipXFun]
    · rw [rlc_retainedChoiceAudit_right_vertices]
      simp [rlc_dualReflect, rlc_dualReflectFun]
    · rw [rlc_retainedChoiceAudit_left_vertices]
      simp [rlc_dualReflect, rlc_dualReflectFun]
  · simpa using sharedPrimalEdge_top (-3) 1
  · rw [rlc_retainedChoiceAudit_left_vertices]
    simp
  · ext i
    fin_cases i <;> simp [phb_doubleDualShift]



theorem rlc_retainedChoiceAudit_reflectedRight_literalTerminalSquare :
    let f : Site 2 := ![-2, -2]
    let g : Site 2 := ![-2, -1]
    let p : Site 2 := ![-2, -1]
    let q : Site 2 := ![-1, -1]
    (hypercubicLattice 2).Adj f g ∧
      RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
          (rlc_dualReflect f) ∧
      sharedPrimalEdge f g = s(p, q) ∧
      RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft p ∧
      p = g ∧ q ∈ rlc_pathVertices rlc_retainedChoiceAuditLeft.1 ∧
      phb_doubleDualShift q = f := by
  dsimp only
  refine ⟨by simp [hypercubicLattice_adj, Fin.sum_univ_two], ?_, ?_,
    ?_, rfl, ?_, ?_⟩
  · refine ⟨by norm_num [rlc_dualReflect, rlc_dualReflectFun],
      ⟨![-1, -1], ?_, ?_⟩, ?_, ?_⟩
    · rw [rlc_retainedChoiceAudit_left_vertices]
      simp
    · ext i
      fin_cases i <;>
        simp [rlc_dualReflect, rlc_dualReflectFun,
          rlc_flipX, rlc_flipXFun]
    · rw [rlc_retainedChoiceAudit_right_vertices]
      simp [rlc_dualReflect, rlc_dualReflectFun]
    · rw [rlc_retainedChoiceAudit_left_vertices]
      simp [rlc_dualReflect, rlc_dualReflectFun]
  · simpa using sharedPrimalEdge_top (-2) (-2)
  · refine ⟨by norm_num, ⟨![2, -1], ?_, ?_⟩, ?_, ?_⟩
    · rw [rlc_retainedChoiceAudit_right_vertices]
      simp
    · ext i
      fin_cases i <;> simp [rlc_flipX, rlc_flipXFun]
    · rw [rlc_retainedChoiceAudit_right_vertices]
      simp
    · rw [rlc_retainedChoiceAudit_left_vertices]
      simp
  · rw [rlc_retainedChoiceAudit_left_vertices]
    simp
  · ext i
    fin_cases i <;> simp [phb_doubleDualShift]


theorem exists_bookFaithful_topWall_literalTerminalSquare :
    ∃ n : Int, ∃ gamma : RlcRightDiagonalPath n,
      ∃ gamma' : RlcLeftDiagonalPath n,
        RlcBookFaithfulTracePair gamma gamma' ∧
          ∃ f g p q : Site 2,
            (hypercubicLattice 2).Adj f g ∧
              RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
                gamma gamma' (rlc_dualReflect f) ∧
              sharedPrimalEdge f g = s(p, q) ∧
              p 1 = n ∧ p = g ∧ q ∈ rlc_pathVertices gamma'.1 ∧
              phb_doubleDualShift q = f := by
  refine ⟨2, rlc_retainedChoiceAuditRight,
    rlc_retainedChoiceAuditLeft, rlc_retainedChoiceAudit_faithful,
    ![-3, 1], ![-3, 2], ![-3, 2], ![-2, 2], ?_⟩
  exact rlc_retainedChoiceAudit_topWall_literalTerminalSquare



theorem exists_bookFaithful_reflectedRight_literalTerminalSquare :
    ∃ n : Int, ∃ gamma : RlcRightDiagonalPath n,
      ∃ gamma' : RlcLeftDiagonalPath n,
        RlcBookFaithfulTracePair gamma gamma' ∧
          ∃ f g p q : Site 2,
            (hypercubicLattice 2).Adj f g ∧
              RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
                gamma gamma' (rlc_dualReflect f) ∧
              sharedPrimalEdge f g = s(p, q) ∧
              RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
                gamma gamma' p ∧
              p = g ∧ q ∈ rlc_pathVertices gamma'.1 ∧
              phb_doubleDualShift q = f := by
  refine ⟨2, rlc_retainedChoiceAuditRight,
    rlc_retainedChoiceAuditLeft, rlc_retainedChoiceAudit_faithful,
    ![-2, -2], ![-2, -1], ![-2, -1], ![-1, -1], ?_⟩
  exact rlc_retainedChoiceAudit_reflectedRight_literalTerminalSquare

end

end StatMech.Universality
