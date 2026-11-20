/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectTorusDualEdges
import Code.FrontierD.FKMedialBoundaryPermutation










namespace StatMech.FrontierD


def fkRectMedialDualShiftVertex
    (R : FKRectTorus) (v : R.medialTorus.Vertex) : R.medialTorus.Vertex :=
  (SixVertexArrows.cyclicPred R.medialTorus.width_pos v.1, v.2)



def fkRectMedialDualShiftDart
    (R : FKRectTorus) (d : FKMedialDart R.medialTorus) :
    FKMedialDart R.medialTorus :=
  (fkRectMedialDualShiftVertex R d.1, d.2)


def fkRectMedialDualUnshiftVertex
    (R : FKRectTorus) (v : R.medialTorus.Vertex) : R.medialTorus.Vertex :=
  (finitePeriodicSucc R.medialTorus.width_pos v.1, v.2)


def fkRectMedialDualUnshiftDart
    (R : FKRectTorus) (d : FKMedialDart R.medialTorus) :
    FKMedialDart R.medialTorus :=
  (fkRectMedialDualUnshiftVertex R d.1, d.2)

@[simp] theorem fkRectMedialDualUnshiftVertex_shift
    (R : FKRectTorus) (v : R.medialTorus.Vertex) :
    fkRectMedialDualUnshiftVertex R (fkRectMedialDualShiftVertex R v) = v := by
  rcases v with ⟨i, j⟩
  simp [fkRectMedialDualUnshiftVertex, fkRectMedialDualShiftVertex,
    finitePeriodicSucc_cyclicPred]

@[simp] theorem fkRectMedialDualShiftVertex_unshift
    (R : FKRectTorus) (v : R.medialTorus.Vertex) :
    fkRectMedialDualShiftVertex R (fkRectMedialDualUnshiftVertex R v) = v := by
  rcases v with ⟨i, j⟩
  simp [fkRectMedialDualUnshiftVertex, fkRectMedialDualShiftVertex,
    svCyclicPred_finitePeriodicSucc]

@[simp] theorem fkRectMedialDualUnshiftDart_shift
    (R : FKRectTorus) (d : FKMedialDart R.medialTorus) :
    fkRectMedialDualUnshiftDart R (fkRectMedialDualShiftDart R d) = d := by
  rcases d with ⟨v, side⟩
  simp [fkRectMedialDualUnshiftDart, fkRectMedialDualShiftDart]

@[simp] theorem fkRectMedialDualShiftDart_unshift
    (R : FKRectTorus) (d : FKMedialDart R.medialTorus) :
    fkRectMedialDualShiftDart R (fkRectMedialDualUnshiftDart R d) = d := by
  rcases d with ⟨v, side⟩
  simp [fkRectMedialDualUnshiftDart, fkRectMedialDualShiftDart]


def fkRectMedialDualShiftDartEquiv (R : FKRectTorus) :
    FKMedialDart R.medialTorus ≃ FKMedialDart R.medialTorus where
  toFun := fkRectMedialDualShiftDart R
  invFun := fkRectMedialDualUnshiftDart R
  left_inv := fkRectMedialDualUnshiftDart_shift R
  right_inv := fkRectMedialDualShiftDart_unshift R


theorem fkRectTorusMedialEdgeEquiv_dualShiftVertex
    (R : FKRectTorus) (v : R.medialTorus.Vertex) :
    fkRectTorusMedialEdgeEquiv R (fkRectMedialDualShiftVertex R v) =
      fkRectEdgeToDualEdge R (fkRectTorusMedialEdgeEquiv R v) := by
  let e := fkRectTorusMedialEdgeEquiv R v
  have hv : v = (fkRectTorusMedialEdgeEquiv R).symm e := by
    simp [e]
  suffices hshift : fkRectMedialDualShiftVertex R v =
      (fkRectTorusMedialEdgeEquiv R).symm (fkRectEdgeToDualEdge R e) by
    rw [hshift, Equiv.apply_symm_apply]
  rcases e with ⟨b, x, y⟩
  cases b
  · apply Prod.ext
    · apply Fin.ext
      simp only [fkRectMedialDualShiftVertex,
        SixVertexArrows.cyclicPred, Fin.val_mk]
      rw [hv]
      simp only [fkRectTorusMedialEdgeEquiv_symm_fst_val,
        Bool.toNat_false, zero_add, fkRectEdgeToDualEdge]
      change ((2 * x.val + 2 * R.width - 1) % (2 * R.width)) =
        1 + 2 * (SixVertexArrows.cyclicPred R.width_pos x).val
      simp only [SixVertexArrows.cyclicPred, Fin.val_mk]
      have hx : x.val < R.width := x.isLt
      by_cases hzero : x.val = 0
      · simp [hzero]
        omega
      · have hpos : 0 < x.val := Nat.pos_of_ne_zero hzero
        have hleft :
            (2 * x.val + 2 * R.width - 1) % (2 * R.width) =
              2 * x.val - 1 := by
          have heq : 2 * x.val + 2 * R.width - 1 =
              (2 * x.val - 1) + 2 * R.width := by omega
          have hlt : 2 * x.val - 1 < 2 * R.width := by omega
          simp [heq, Nat.mod_eq_of_lt hlt]
        have hright : (x.val + R.width - 1) % R.width =
            x.val - 1 := by
          have heq : x.val + R.width - 1 =
              (x.val - 1) + R.width := by omega
          have hlt : x.val - 1 < R.width := by omega
          simp [heq, Nat.mod_eq_of_lt hlt]
        rw [hleft, hright]
        omega
    · rw [hv]
      simp [fkRectMedialDualShiftVertex, fkRectEdgeToDualEdge]
  · apply Prod.ext
    · apply Fin.ext
      simp only [fkRectMedialDualShiftVertex,
        SixVertexArrows.cyclicPred, Fin.val_mk]
      rw [hv]
      simp only [fkRectTorusMedialEdgeEquiv_symm_fst_val,
        Bool.toNat_true, fkRectEdgeToDualEdge, ↓reduceIte,
        Bool.toNat_false, zero_add]
      change ((1 + 2 * x.val + 2 * R.width - 1) % (2 * R.width)) =
        2 * x.val
      have heq : 1 + 2 * x.val + 2 * R.width - 1 =
          2 * x.val + 2 * R.width := by omega
      have hlt : 2 * x.val < 2 * R.width := by omega
      simp [heq, Nat.mod_eq_of_lt hlt]
    · rw [hv]
      simp [fkRectMedialDualShiftVertex, fkRectEdgeToDualEdge]


theorem fkRectClosedPairingAtEdge_edgeToDualEdge
    (R : FKRectTorus) (e : R.EdgeIndex) :
    fkRectClosedPairingAtEdge (fkRectEdgeToDualEdge R e) =
      !(fkRectClosedPairingAtEdge e) := by
  rcases e with ⟨b, x, y⟩
  cases b <;> cases h : decide (Even y.val) <;>
    simp [fkRectEdgeToDualEdge, fkRectClosedPairingAtEdge, h]


theorem fkRectConfigurationToMedialPairing_dual_shift
    (R : FKRectTorus) (omega : R.Configuration)
    (v : R.medialTorus.Vertex) :
    fkRectConfigurationToMedialPairing R
        (fkRectDualConfigurationEquiv R omega)
        (fkRectMedialDualShiftVertex R v) =
      fkRectConfigurationToMedialPairing R omega v := by
  rw [fkRectConfigurationToMedialPairing_apply,
    fkRectTorusMedialEdgeEquiv_dualShiftVertex,
    fkRectDualConfigurationEquiv_apply_edgeToDualEdge,
    fkRectClosedPairingAtEdge_edgeToDualEdge,
    fkRectConfigurationToMedialPairing_apply]
  cases omega (fkRectTorusMedialEdgeEquiv R v) <;>
    cases fkRectClosedPairingAtEdge (fkRectTorusMedialEdgeEquiv R v) <;> rfl

theorem fkRectMedialDualShiftDart_localMate
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    fkRectMedialDualShiftDart R
        (fkMedialLocalMate (fkRectConfigurationToMedialPairing R omega) d) =
      fkMedialLocalMate
        (fkRectConfigurationToMedialPairing R
          (fkRectDualConfigurationEquiv R omega))
        (fkRectMedialDualShiftDart R d) := by
  rcases d with ⟨v, side⟩
  have hpair := fkRectConfigurationToMedialPairing_dual_shift R omega v
  cases hp : fkRectConfigurationToMedialPairing R omega v <;>
    rw [hp] at hpair <;> cases side <;>
    simp [fkRectMedialDualShiftDart, fkMedialLocalMate, hp, hpair]

theorem fkRectMedialDualShiftDart_bondMate
    (R : FKRectTorus) (d : FKMedialDart R.medialTorus) :
    fkRectMedialDualShiftDart R (fkMedialBondMate R.medialTorus d) =
      fkMedialBondMate R.medialTorus (fkRectMedialDualShiftDart R d) := by
  rcases d with ⟨⟨i, j⟩, side⟩
  cases side <;>
    simp [fkRectMedialDualShiftDart, fkRectMedialDualShiftVertex,
      fkMedialBondMate, finitePeriodicSucc_cyclicPred,
      svCyclicPred_finitePeriodicSucc]

theorem fkRectMedialDualShiftDart_boundaryStep
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    fkRectMedialDualShiftDart R
        (fkMedialBoundaryStep
          (fkRectConfigurationToMedialPairing R omega) d) =
      fkMedialBoundaryStep
        (fkRectConfigurationToMedialPairing R
          (fkRectDualConfigurationEquiv R omega))
        (fkRectMedialDualShiftDart R d) := by
  simp only [fkMedialBoundaryStep_apply,
    fkRectMedialDualShiftDart_bondMate,
    fkRectMedialDualShiftDart_localMate]

theorem fkRectMedialDualShiftDart_boundaryStep_iterate
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) (n : Nat) :
    fkRectMedialDualShiftDart R
        ((fkMedialBoundaryStep
          (fkRectConfigurationToMedialPairing R omega))^[n] d) =
      (fkMedialBoundaryStep
        (fkRectConfigurationToMedialPairing R
          (fkRectDualConfigurationEquiv R omega)))^[n]
        (fkRectMedialDualShiftDart R d) := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      rw [ih, fkRectMedialDualShiftDart_boundaryStep]



def fkRectMedialDualShiftGraphIso
    (R : FKRectTorus) (omega : R.Configuration) :
    fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega) ≃g
      fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R
          (fkRectDualConfigurationEquiv R omega)) where
  toEquiv := fkRectMedialDualShiftDartEquiv R
  map_rel_iff' := by
    intro d e
    rw [fkMedialLoopGraph_adj_iff, fkMedialLoopGraph_adj_iff]
    constructor
    · rintro (hlocal | hbond)
      · left
        apply (fkRectMedialDualShiftDartEquiv R).injective
        change fkRectMedialDualShiftDart R e =
          fkRectMedialDualShiftDart R
            (fkMedialLocalMate
              (fkRectConfigurationToMedialPairing R omega) d)
        rw [fkRectMedialDualShiftDart_localMate]
        exact hlocal
      · right
        apply (fkRectMedialDualShiftDartEquiv R).injective
        change fkRectMedialDualShiftDart R e =
          fkRectMedialDualShiftDart R
            (fkMedialBondMate R.medialTorus d)
        rw [fkRectMedialDualShiftDart_bondMate]
        exact hbond
    · rintro (hlocal | hbond)
      · left
        change fkRectMedialDualShiftDart R e =
          fkMedialLocalMate
            (fkRectConfigurationToMedialPairing R
              (fkRectDualConfigurationEquiv R omega))
            (fkRectMedialDualShiftDart R d)
        rw [hlocal, fkRectMedialDualShiftDart_localMate]
      · right
        change fkRectMedialDualShiftDart R e =
          fkMedialBondMate R.medialTorus
            (fkRectMedialDualShiftDart R d)
        rw [hbond, fkRectMedialDualShiftDart_bondMate]

end StatMech.FrontierD
