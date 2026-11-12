/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKRectMedialPrimalLabel
import Code.FrontierD.FKMedialBoundaryToggleParity
import Code.FrontierD.FKRectTorusEdgeFinset
import Code.FrontierD.FKRectTorusEulerDefect
import Code.FrontierD.FKRectTorusConnected

open Equiv

namespace StatMech.FrontierD



theorem fkRectClosedMedialPairing_eq_not_vertexParity
    (R : FKRectTorus) (v : R.medialTorus.Vertex) :
    fkRectClosedMedialPairing R v = !fkMedialVertexParity v := by
  let e := fkRectTorusMedialEdgeEquiv R v
  have hv : v = fkRectMedialVertexOfEdge R e :=
    ((fkRectTorusMedialEdgeEquiv R).symm_apply_apply v).symm
  rw [hv]
  rcases e with ⟨b, x, y⟩
  cases b <;> by_cases hy : Even y.val <;>
    simp [fkRectClosedMedialPairing, fkRectClosedPairingAtEdge,
      fkMedialVertexParity, fkRectMedialVertexOfEdge_fst_val,
      fkRectMedialVertexOfEdge_snd, hy, Bool.toNat]



theorem fkRectConfigurationToMedialPairing_empty (R : FKRectTorus) :
    fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R ∅) = fkRectClosedMedialPairing R := by
  funext v
  simp [fkRectConfigurationToMedialPairing_apply,
    fkRectConfigurationOfEdges, fkRectClosedMedialPairing]


def fkRectFullMedialPairing (R : FKRectTorus) :
    FKMedialLoopPairing R.medialTorus :=
  fkRectConfigurationToMedialPairing R
    (fkRectConfigurationOfEdges R Finset.univ)

theorem fkRectFullMedialPairing_eq_vertexParity
    (R : FKRectTorus) (v : R.medialTorus.Vertex) :
    fkRectFullMedialPairing R v = fkMedialVertexParity v := by
  rw [← Bool.not_not (fkMedialVertexParity v),
    ← fkRectClosedMedialPairing_eq_not_vertexParity]
  simp [fkRectFullMedialPairing, fkRectConfigurationToMedialPairing_apply,
    fkRectConfigurationOfEdges, fkRectClosedMedialPairing]

private theorem closedStep_west (R : FKRectTorus)
    (i : Fin R.medialTorus.width) (j : Fin R.medialTorus.height)
    (h : fkMedialVertexParity (i, j) = false) :
    fkMedialBoundaryStep (fkRectClosedMedialPairing R) ((i, j), .west) =
      ((i, SixVertexArrows.cyclicPred R.medialTorus.height_pos j), .north) := by
  simp [fkMedialBoundaryStep, fkMedialLocalMateEquiv, fkMedialBondMateEquiv,
    fkMedialLocalMate, fkMedialBondMate,
    fkRectClosedMedialPairing_eq_not_vertexParity, h]

private theorem closedStep_east (R : FKRectTorus)
    (i : Fin R.medialTorus.width) (j : Fin R.medialTorus.height)
    (h : fkMedialVertexParity (i, j) = false) :
    fkMedialBoundaryStep (fkRectClosedMedialPairing R) ((i, j), .east) =
      ((i, finitePeriodicSucc R.medialTorus.height_pos j), .south) := by
  simp [fkMedialBoundaryStep, fkMedialLocalMateEquiv, fkMedialBondMateEquiv,
    fkMedialLocalMate, fkMedialBondMate,
    fkRectClosedMedialPairing_eq_not_vertexParity, h]

private theorem closedStep_south (R : FKRectTorus)
    (i : Fin R.medialTorus.width) (j : Fin R.medialTorus.height)
    (h : fkMedialVertexParity (i, j) = true) :
    fkMedialBoundaryStep (fkRectClosedMedialPairing R) ((i, j), .south) =
      ((finitePeriodicSucc R.medialTorus.width_pos i, j), .west) := by
  simp [fkMedialBoundaryStep, fkMedialLocalMateEquiv, fkMedialBondMateEquiv,
    fkMedialLocalMate, fkMedialBondMate,
    fkRectClosedMedialPairing_eq_not_vertexParity, h]

private theorem closedStep_north (R : FKRectTorus)
    (i : Fin R.medialTorus.width) (j : Fin R.medialTorus.height)
    (h : fkMedialVertexParity (i, j) = true) :
    fkMedialBoundaryStep (fkRectClosedMedialPairing R) ((i, j), .north) =
      ((SixVertexArrows.cyclicPred R.medialTorus.width_pos i, j), .east) := by
  simp [fkMedialBoundaryStep, fkMedialLocalMateEquiv, fkMedialBondMateEquiv,
    fkMedialLocalMate, fkMedialBondMate,
    fkRectClosedMedialPairing_eq_not_vertexParity, h]

private theorem fullStep_west (R : FKRectTorus)
    (i : Fin R.medialTorus.width) (j : Fin R.medialTorus.height)
    (h : fkMedialVertexParity (i, j) = false) :
    fkMedialBoundaryStep (fkRectFullMedialPairing R) ((i, j), .west) =
      ((i, finitePeriodicSucc R.medialTorus.height_pos j), .south) := by
  simp [fkMedialBoundaryStep, fkMedialLocalMateEquiv, fkMedialBondMateEquiv,
    fkMedialLocalMate, fkMedialBondMate,
    fkRectFullMedialPairing_eq_vertexParity, h]

private theorem fullStep_east (R : FKRectTorus)
    (i : Fin R.medialTorus.width) (j : Fin R.medialTorus.height)
    (h : fkMedialVertexParity (i, j) = false) :
    fkMedialBoundaryStep (fkRectFullMedialPairing R) ((i, j), .east) =
      ((i, SixVertexArrows.cyclicPred R.medialTorus.height_pos j), .north) := by
  simp [fkMedialBoundaryStep, fkMedialLocalMateEquiv, fkMedialBondMateEquiv,
    fkMedialLocalMate, fkMedialBondMate,
    fkRectFullMedialPairing_eq_vertexParity, h]

private theorem fullStep_south (R : FKRectTorus)
    (i : Fin R.medialTorus.width) (j : Fin R.medialTorus.height)
    (h : fkMedialVertexParity (i, j) = true) :
    fkMedialBoundaryStep (fkRectFullMedialPairing R) ((i, j), .south) =
      ((SixVertexArrows.cyclicPred R.medialTorus.width_pos i, j), .east) := by
  simp [fkMedialBoundaryStep, fkMedialLocalMateEquiv, fkMedialBondMateEquiv,
    fkMedialLocalMate, fkMedialBondMate,
    fkRectFullMedialPairing_eq_vertexParity, h]

private theorem fullStep_north (R : FKRectTorus)
    (i : Fin R.medialTorus.width) (j : Fin R.medialTorus.height)
    (h : fkMedialVertexParity (i, j) = true) :
    fkMedialBoundaryStep (fkRectFullMedialPairing R) ((i, j), .north) =
      ((finitePeriodicSucc R.medialTorus.width_pos i, j), .west) := by
  simp [fkMedialBoundaryStep, fkMedialLocalMateEquiv, fkMedialBondMateEquiv,
    fkMedialLocalMate, fkMedialBondMate,
    fkRectFullMedialPairing_eq_vertexParity, h]


theorem fkRectClosedBlackBoundaryPerm_pow_four (R : FKRectTorus) :
    fkMedialBlackBoundaryPerm (fkRectClosedMedialPairing R) ^ 4 = 1 := by
  apply Equiv.ext
  intro d
  apply Subtype.ext
  rcases d with ⟨⟨⟨i, j⟩, side⟩, hd⟩
  simp only [pow_succ, pow_zero, Equiv.Perm.one_apply, Equiv.Perm.mul_apply,
    fkMedialBlackBoundaryPerm_val_step]
  cases side
  · have hp : fkMedialVertexParity (i, j) = false := by
      simpa [fkMedialCheckerColor, fkMedialSideVertical] using hd
    rw [closedStep_west R i j hp]
    rw [closedStep_north R _ _ (by simp [hp])]
    rw [closedStep_east R _ _ (by simp [hp])]
    rw [closedStep_south R _ _ (by simp [hp])]
    simp [finitePeriodicSucc_cyclicPred]
  · have hp : fkMedialVertexParity (i, j) = false := by
      simpa [fkMedialCheckerColor, fkMedialSideVertical] using hd
    rw [closedStep_east R i j hp]
    rw [closedStep_south R _ _ (by simp [hp])]
    rw [closedStep_west R _ _ (by simp [hp])]
    rw [closedStep_north R _ _ (by simp [hp])]
    simp [svCyclicPred_finitePeriodicSucc]
  · have hp : fkMedialVertexParity (i, j) = true := by
      simpa [fkMedialCheckerColor, fkMedialSideVertical] using hd
    rw [closedStep_south R i j hp]
    rw [closedStep_west R _ _ (by simp [hp])]
    rw [closedStep_north R _ _ (by simp [hp])]
    rw [closedStep_east R _ _ (by simp [hp])]
    simp [svCyclicPred_finitePeriodicSucc, finitePeriodicSucc_cyclicPred]
  · have hp : fkMedialVertexParity (i, j) = true := by
      simpa [fkMedialCheckerColor, fkMedialSideVertical] using hd
    rw [closedStep_north R i j hp]
    rw [closedStep_east R _ _ (by simp [hp])]
    rw [closedStep_south R _ _ (by simp [hp])]
    rw [closedStep_west R _ _ (by simp [hp])]
    simp [svCyclicPred_finitePeriodicSucc, finitePeriodicSucc_cyclicPred]


theorem fkRectClosedBlackBoundaryPerm_sq_ne
    (R : FKRectTorus) (d : FKMedialBlackDart R.medialTorus) :
    ((fkMedialBlackBoundaryPerm (fkRectClosedMedialPairing R)) ^ 2) d ≠ d := by
  intro h
  have hs := congrArg (fun z : FKMedialBlackDart R.medialTorus => z.1.2) h
  rcases d with ⟨⟨⟨i, j⟩, side⟩, hd⟩
  simp only [pow_succ, pow_zero, Equiv.Perm.one_apply, Equiv.Perm.mul_apply,
    fkMedialBlackBoundaryPerm_val_step] at hs
  cases side
  · have hp : fkMedialVertexParity (i, j) = false := by
      simpa [fkMedialCheckerColor, fkMedialSideVertical] using hd
    rw [closedStep_west R i j hp, closedStep_north R _ _ (by simp [hp])] at hs
    contradiction
  · have hp : fkMedialVertexParity (i, j) = false := by
      simpa [fkMedialCheckerColor, fkMedialSideVertical] using hd
    rw [closedStep_east R i j hp, closedStep_south R _ _ (by simp [hp])] at hs
    contradiction
  · have hp : fkMedialVertexParity (i, j) = true := by
      simpa [fkMedialCheckerColor, fkMedialSideVertical] using hd
    rw [closedStep_south R i j hp, closedStep_west R _ _ (by simp [hp])] at hs
    contradiction
  · have hp : fkMedialVertexParity (i, j) = true := by
      simpa [fkMedialCheckerColor, fkMedialSideVertical] using hd
    rw [closedStep_north R i j hp, closedStep_east R _ _ (by simp [hp])] at hs
    contradiction


theorem fkRectFullBlackBoundaryPerm_pow_four (R : FKRectTorus) :
    fkMedialBlackBoundaryPerm (fkRectFullMedialPairing R) ^ 4 = 1 := by
  apply Equiv.ext
  intro d
  apply Subtype.ext
  rcases d with ⟨⟨⟨i, j⟩, side⟩, hd⟩
  simp only [pow_succ, pow_zero, Equiv.Perm.one_apply, Equiv.Perm.mul_apply,
    fkMedialBlackBoundaryPerm_val_step]
  cases side
  · have hp : fkMedialVertexParity (i, j) = false := by
      simpa [fkMedialCheckerColor, fkMedialSideVertical] using hd
    rw [fullStep_west R i j hp]
    rw [fullStep_south R _ _ (by simp [hp])]
    rw [fullStep_east R _ _ (by simp [hp])]
    rw [fullStep_north R _ _ (by simp [hp])]
    simp [svCyclicPred_finitePeriodicSucc, finitePeriodicSucc_cyclicPred]
  · have hp : fkMedialVertexParity (i, j) = false := by
      simpa [fkMedialCheckerColor, fkMedialSideVertical] using hd
    rw [fullStep_east R i j hp]
    rw [fullStep_north R _ _ (by simp [hp])]
    rw [fullStep_west R _ _ (by simp [hp])]
    rw [fullStep_south R _ _ (by simp [hp])]
    simp [svCyclicPred_finitePeriodicSucc, finitePeriodicSucc_cyclicPred]
  · have hp : fkMedialVertexParity (i, j) = true := by
      simpa [fkMedialCheckerColor, fkMedialSideVertical] using hd
    rw [fullStep_south R i j hp]
    rw [fullStep_east R _ _ (by simp [hp])]
    rw [fullStep_north R _ _ (by simp [hp])]
    rw [fullStep_west R _ _ (by simp [hp])]
    simp [finitePeriodicSucc_cyclicPred]
  · have hp : fkMedialVertexParity (i, j) = true := by
      simpa [fkMedialCheckerColor, fkMedialSideVertical] using hd
    rw [fullStep_north R i j hp]
    rw [fullStep_west R _ _ (by simp [hp])]
    rw [fullStep_south R _ _ (by simp [hp])]
    rw [fullStep_east R _ _ (by simp [hp])]
    simp [svCyclicPred_finitePeriodicSucc]


theorem fkRectFullBlackBoundaryPerm_sq_ne
    (R : FKRectTorus) (d : FKMedialBlackDart R.medialTorus) :
    ((fkMedialBlackBoundaryPerm (fkRectFullMedialPairing R)) ^ 2) d ≠ d := by
  intro h
  have hs := congrArg (fun z : FKMedialBlackDart R.medialTorus => z.1.2) h
  rcases d with ⟨⟨⟨i, j⟩, side⟩, hd⟩
  simp only [pow_succ, pow_zero, Equiv.Perm.one_apply, Equiv.Perm.mul_apply,
    fkMedialBlackBoundaryPerm_val_step] at hs
  cases side
  · have hp : fkMedialVertexParity (i, j) = false := by
      simpa [fkMedialCheckerColor, fkMedialSideVertical] using hd
    rw [fullStep_west R i j hp, fullStep_south R _ _ (by simp [hp])] at hs
    contradiction
  · have hp : fkMedialVertexParity (i, j) = false := by
      simpa [fkMedialCheckerColor, fkMedialSideVertical] using hd
    rw [fullStep_east R i j hp, fullStep_north R _ _ (by simp [hp])] at hs
    contradiction
  · have hp : fkMedialVertexParity (i, j) = true := by
      simpa [fkMedialCheckerColor, fkMedialSideVertical] using hd
    rw [fullStep_south R i j hp, fullStep_east R _ _ (by simp [hp])] at hs
    contradiction
  · have hp : fkMedialVertexParity (i, j) = true := by
      simpa [fkMedialCheckerColor, fkMedialSideVertical] using hd
    rw [fullStep_north R i j hp, fullStep_west R _ _ (by simp [hp])] at hs
    contradiction



theorem fkRectClosedMedialLoopCount (R : FKRectTorus) :
    fkMedialLoopCount R.medialTorus (fkRectClosedMedialPairing R) =
      R.width * R.height := by
  have hcount :=
    StatMech.FrontierA.four_mul_permCycleCount_eq_card_of_pow_four_eq_one_of_sq_ne
      (fkMedialBlackBoundaryPerm (fkRectClosedMedialPairing R))
      (fkRectClosedBlackBoundaryPerm_pow_four R)
      (fkRectClosedBlackBoundaryPerm_sq_ne R)
  rw [permCycleCount_fkMedialBlackBoundaryPerm,
    card_fkMedialBlackDart] at hcount
  change 4 * fkMedialLoopCount R.medialTorus
      (fkRectClosedMedialPairing R) =
    2 * (2 * R.width) * R.height at hcount
  have hrhs : 2 * (2 * R.width) * R.height =
      4 * (R.width * R.height) := by ring
  rw [hrhs] at hcount
  omega



theorem fkRectFullMedialLoopCount (R : FKRectTorus) :
    fkMedialLoopCount R.medialTorus (fkRectFullMedialPairing R) =
      R.width * R.height := by
  have hcount :=
    StatMech.FrontierA.four_mul_permCycleCount_eq_card_of_pow_four_eq_one_of_sq_ne
      (fkMedialBlackBoundaryPerm (fkRectFullMedialPairing R))
      (fkRectFullBlackBoundaryPerm_pow_four R)
      (fkRectFullBlackBoundaryPerm_sq_ne R)
  rw [permCycleCount_fkMedialBlackBoundaryPerm,
    card_fkMedialBlackDart] at hcount
  change 4 * fkMedialLoopCount R.medialTorus
      (fkRectFullMedialPairing R) =
    2 * (2 * R.width) * R.height at hcount
  have hrhs : 2 * (2 * R.width) * R.height =
      4 * (R.width * R.height) := by ring
  rw [hrhs] at hcount
  omega



theorem fkRectMedialLoopCount_empty (R : FKRectTorus) :
    fkRectMedialLoopCount R (fkRectConfigurationOfEdges R ∅) =
      R.width * R.height := by
  unfold fkRectMedialLoopCount
  rw [fkRectConfigurationToMedialPairing_empty]
  exact fkRectClosedMedialLoopCount R



theorem fkRectEulerHomologyDefect_empty (R : FKRectTorus) :
    fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R ∅) = 0 := by
  have hclusters := fkRectFinsetClusterCount_empty R
  unfold fkRectFinsetClusterCount at hclusters
  unfold fkRectEulerHomologyDefect
  rw [hclusters, fkRectOpenEdgeCount_configurationOfEdges,
    fkRectMedialLoopCount_empty, fkRectTorus_card_vertex]
  norm_num
  ring



theorem fkRectMedialLoopCount_univ (R : FKRectTorus) :
    fkRectMedialLoopCount R (fkRectConfigurationOfEdges R Finset.univ) =
      R.width * R.height := by
  unfold fkRectMedialLoopCount
  change fkMedialLoopCount R.medialTorus (fkRectFullMedialPairing R) =
    R.width * R.height
  exact fkRectFullMedialLoopCount R



theorem fkRectEulerHomologyDefect_univ (R : FKRectTorus) :
    fkRectEulerHomologyDefect R
      (fkRectConfigurationOfEdges R Finset.univ) = 2 := by
  have hclusters := fkRectFinsetClusterCount_univ R
  unfold fkRectFinsetClusterCount at hclusters
  unfold fkRectEulerHomologyDefect
  rw [hclusters, fkRectOpenEdgeCount_configurationOfEdges,
    fkRectMedialLoopCount_univ, Finset.card_univ,
    fkRectTorus_card_edgeIndex]
  norm_num
  ring

end StatMech.FrontierD
