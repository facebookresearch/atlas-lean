/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKMedialToggleCount

namespace StatMech.FrontierD

variable {T : EvenTorus}



def fkMedialSideVertical : FKMedialSide → Bool
  | .west | .east => false
  | .south | .north => true


def fkMedialVertexParity (v : T.Vertex) : Bool :=
  decide (Even v.1.val) ^^ decide (Even v.2.val)



def fkMedialCheckerColor (d : FKMedialDart T) : Bool :=
  fkMedialVertexParity d.1 ^^ fkMedialSideVertical d.2

private theorem even_finitePeriodicSucc_iff (T : EvenTorus)
    (i : Fin T.width) :
    Even (finitePeriodicSucc T.width_pos i).val ↔ ¬ Even i.val := by
  change Even ((i.val + 1) % T.width) ↔ ¬ Even i.val
  rw [Even.mod_even_iff T.width_even, Nat.even_add_one]

private theorem even_finitePeriodicSucc_iff_vertical (T : EvenTorus)
    (i : Fin T.height) :
    Even (finitePeriodicSucc T.height_pos i).val ↔ ¬ Even i.val := by
  change Even ((i.val + 1) % T.height) ↔ ¬ Even i.val
  rw [Even.mod_even_iff T.height_even, Nat.even_add_one]

private theorem even_cyclicPred_iff (T : EvenTorus)
    (i : Fin T.width) :
    Even (SixVertexArrows.cyclicPred T.width_pos i).val ↔
      ¬ Even i.val := by
  let j := SixVertexArrows.cyclicPred T.width_pos i
  have h := even_finitePeriodicSucc_iff T j
  rw [finitePeriodicSucc_cyclicPred] at h
  tauto

private theorem even_cyclicPred_iff_vertical (T : EvenTorus)
    (i : Fin T.height) :
    Even (SixVertexArrows.cyclicPred T.height_pos i).val ↔
      ¬ Even i.val := by
  let j := SixVertexArrows.cyclicPred T.height_pos i
  have h := even_finitePeriodicSucc_iff_vertical T j
  rw [finitePeriodicSucc_cyclicPred] at h
  tauto

private theorem decide_ne_of_iff_not {P Q : Prop}
    [Decidable P] [Decidable Q] (h : P ↔ ¬ Q) :
    decide P ≠ decide Q := by
  intro heq
  generalize hp : decide P = p at heq
  generalize hq : decide Q = q at heq
  cases p <;> cases q <;> simp_all

private theorem decide_eq_not_of_iff_not {P Q : Prop}
    [Decidable P] [Decidable Q] (h : P ↔ ¬ Q) :
    decide P = !decide Q := by
  apply Bool.eq_iff_iff.mpr
  simpa using h

private theorem bool_xor_right_ne {a b : Bool} (h : a ≠ b) (c : Bool) :
    (a ^^ c) ≠ (b ^^ c) := by
  cases a <;> cases b <;> cases c <;> simp_all

private theorem bool_xor_left_ne {a b : Bool} (h : a ≠ b) (c : Bool) :
    (c ^^ a) ≠ (c ^^ b) := by
  cases a <;> cases b <;> cases c <;> simp_all


theorem fkMedialCheckerColor_localMate_ne
    (pairing : FKMedialLoopPairing T) (d : FKMedialDart T) :
    fkMedialCheckerColor (fkMedialLocalMate pairing d) ≠
      fkMedialCheckerColor d := by
  rcases d with ⟨v, side⟩
  cases hp : pairing v <;> cases side <;>
    simp [fkMedialCheckerColor, fkMedialVertexParity,
      fkMedialSideVertical, fkMedialLocalMate, hp]


theorem fkMedialCheckerColor_bondMate_ne
    (T : EvenTorus) (d : FKMedialDart T) :
    fkMedialCheckerColor (fkMedialBondMate T d) ≠
      fkMedialCheckerColor d := by
  rcases d with ⟨⟨i, j⟩, side⟩
  cases side
  · have hpar :
        decide (Even (SixVertexArrows.cyclicPred T.width_pos i).val) ≠
          decide (Even i.val) :=
      decide_ne_of_iff_not (even_cyclicPred_iff T i)
    simp only [fkMedialBondMate, fkMedialCheckerColor,
      fkMedialVertexParity, fkMedialSideVertical, Bool.xor_false]
    exact bool_xor_right_ne hpar _
  · have hpar :
        decide (Even (finitePeriodicSucc T.width_pos i).val) ≠
          decide (Even i.val) :=
      decide_ne_of_iff_not (even_finitePeriodicSucc_iff T i)
    simp only [fkMedialBondMate, fkMedialCheckerColor,
      fkMedialVertexParity, fkMedialSideVertical, Bool.xor_false]
    exact bool_xor_right_ne hpar _
  · have hpar :
        decide (Even (SixVertexArrows.cyclicPred T.height_pos j).val) ≠
          decide (Even j.val) :=
      decide_ne_of_iff_not (even_cyclicPred_iff_vertical T j)
    simp only [fkMedialBondMate, fkMedialCheckerColor,
      fkMedialVertexParity, fkMedialSideVertical]
    exact bool_xor_right_ne (bool_xor_left_ne hpar _) _
  · have hpar :
        decide (Even (finitePeriodicSucc T.height_pos j).val) ≠
          decide (Even j.val) :=
      decide_ne_of_iff_not (even_finitePeriodicSucc_iff_vertical T j)
    simp only [fkMedialBondMate, fkMedialCheckerColor,
      fkMedialVertexParity, fkMedialSideVertical]
    exact bool_xor_right_ne (bool_xor_left_ne hpar _) _

@[simp] theorem fkMedialVertexParity_cyclicPred_fst
    (T : EvenTorus) (i : Fin T.width) (j : Fin T.height) :
    fkMedialVertexParity
        (SixVertexArrows.cyclicPred T.width_pos i, j) =
      !fkMedialVertexParity (i, j) := by
  unfold fkMedialVertexParity
  rw [decide_eq_not_of_iff_not (even_cyclicPred_iff T i)]
  cases decide (Even i.val) <;> cases decide (Even j.val) <;> rfl

@[simp] theorem fkMedialVertexParity_succ_fst
    (T : EvenTorus) (i : Fin T.width) (j : Fin T.height) :
    fkMedialVertexParity (finitePeriodicSucc T.width_pos i, j) =
      !fkMedialVertexParity (i, j) := by
  unfold fkMedialVertexParity
  rw [decide_eq_not_of_iff_not (even_finitePeriodicSucc_iff T i)]
  cases decide (Even i.val) <;> cases decide (Even j.val) <;> rfl

@[simp] theorem fkMedialVertexParity_cyclicPred_snd
    (T : EvenTorus) (i : Fin T.width) (j : Fin T.height) :
    fkMedialVertexParity
        (i, SixVertexArrows.cyclicPred T.height_pos j) =
      !fkMedialVertexParity (i, j) := by
  unfold fkMedialVertexParity
  rw [decide_eq_not_of_iff_not (even_cyclicPred_iff_vertical T j)]
  cases decide (Even i.val) <;> cases decide (Even j.val) <;> rfl

@[simp] theorem fkMedialVertexParity_succ_snd
    (T : EvenTorus) (i : Fin T.width) (j : Fin T.height) :
    fkMedialVertexParity (i, finitePeriodicSucc T.height_pos j) =
      !fkMedialVertexParity (i, j) := by
  unfold fkMedialVertexParity
  rw [decide_eq_not_of_iff_not (even_finitePeriodicSucc_iff_vertical T j)]
  cases decide (Even i.val) <;> cases decide (Even j.val) <;> rfl



theorem fkMedialLoopGraph_adj_checkerColor_ne
    (T : EvenTorus) (pairing : FKMedialLoopPairing T)
    {d e : FKMedialDart T}
    (hde : (fkMedialLoopGraph T pairing).Adj d e) :
    fkMedialCheckerColor d ≠ fkMedialCheckerColor e := by
  rw [fkMedialLoopGraph_adj_iff] at hde
  rcases hde with rfl | rfl
  · exact (fkMedialCheckerColor_localMate_ne pairing d).symm
  · exact (fkMedialCheckerColor_bondMate_ne T d).symm

end StatMech.FrontierD
