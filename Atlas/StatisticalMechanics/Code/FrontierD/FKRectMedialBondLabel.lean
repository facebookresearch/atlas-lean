/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKRectMedialPrimalLabel

namespace StatMech.FrontierD

private theorem double_cyclicPred (W x : Nat) (hW : 0 < W) (hx : x < W) :
    (2 * x + 2 * W - 1) % (2 * W) =
      2 * ((x + W - 1) % W) + 1 := by
  by_cases hzero : x = 0
  · subst x
    have hlt : 2 * W - 1 < 2 * W := by omega
    have hpred : (W - 1) % W = W - 1 :=
      Nat.mod_eq_of_lt (by omega)
    simp only [Nat.mul_zero, Nat.zero_add]
    rw [hpred, Nat.mod_eq_of_lt hlt]
    omega
  · have hxpos : 0 < x := Nat.pos_of_ne_zero hzero
    have hleft : 2 * x + 2 * W - 1 = (2 * x - 1) + 2 * W := by omega
    have hright : x + W - 1 = (x - 1) + W := by omega
    rw [hleft, hright, Nat.add_mod_right, Nat.add_mod_right]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

private theorem double_finitePeriodicSucc
    (W x : Nat) (hW : 0 < W) (hx : x < W) :
    (2 * x + 1 + 1) % (2 * W) = 2 * ((x + 1) % W) := by
  by_cases hnext : x + 1 < W
  · rw [Nat.mod_eq_of_lt hnext, Nat.mod_eq_of_lt (by omega)]
    omega
  · have hxlast : x + 1 = W := by omega
    rw [show 2 * x + 1 + 1 = 2 * W by omega, Nat.mod_self,
      hxlast, Nat.mod_self]

private theorem double_add_one_lt (W x : Nat) (hx : x < W) :
    1 + x * 2 < W * 2 := by
  omega

private theorem double_mul_add_one_lt (W x : Nat) (hx : x < W) :
    2 * x + 1 < 2 * W := by
  omega

private theorem double_mul_add_one_mod (W x : Nat) (hx : x < W) :
    (2 * x + 1) % (2 * W) = 1 + 2 * x := by
  rw [Nat.mod_eq_of_lt (double_mul_add_one_lt W x hx)]
  omega

theorem even_finitePeriodicSucc_iff (R : FKRectTorus)
    (y : Fin R.height) :
    Even (finitePeriodicSucc R.height_pos y).val ↔ ¬ Even y.val := by
  change Even ((y.val + 1) % R.height) ↔ ¬ Even y.val
  rw [Even.mod_even_iff R.height_even, Nat.even_add_one]

theorem even_cyclicPred_iff (R : FKRectTorus)
    (y : Fin R.height) :
    Even (SixVertexArrows.cyclicPred R.height_pos y).val ↔
      ¬ Even y.val := by
  let z := SixVertexArrows.cyclicPred R.height_pos y
  have h := even_finitePeriodicSucc_iff R z
  rw [finitePeriodicSucc_cyclicPred] at h
  tauto


theorem finitePeriodicSucc_val {N : Nat} (hN : 0 < N) (i : Fin N) :
    (finitePeriodicSucc hN i).val =
      if i.val + 1 = N then 0 else i.val + 1 := by
  unfold finitePeriodicSucc
  by_cases h : i.val + 1 = N
  · simp [h]
  · have hlt : i.val + 1 < N := by omega
    simp [h, Nat.mod_eq_of_lt hlt]


def fkRectMedialBondEdgeIndex (R : FKRectTorus) (e : R.EdgeIndex)
    (side : FKMedialSide) : R.EdgeIndex :=
  match side with
  | .west =>
      if e.1 then (false, e.2)
      else (true, (SixVertexArrows.cyclicPred R.width_pos e.2.1, e.2.2))
  | .east =>
      if e.1 then
        (false, (finitePeriodicSucc R.width_pos e.2.1, e.2.2))
      else (true, e.2)
  | .south =>
      (e.1, (e.2.1, SixVertexArrows.cyclicPred R.height_pos e.2.2))
  | .north =>
      (e.1, (e.2.1, finitePeriodicSucc R.height_pos e.2.2))



theorem fkRectTorusMedialEdgeEquiv_bondMate
    (R : FKRectTorus) (d : FKMedialDart R.medialTorus) :
    fkRectTorusMedialEdgeEquiv R (fkMedialBondMate R.medialTorus d).1 =
      fkRectMedialBondEdgeIndex R
        (fkRectTorusMedialEdgeEquiv R d.1) d.2 := by
  rcases d with ⟨v, side⟩
  let e := fkRectTorusMedialEdgeEquiv R v
  have hv : v = fkRectMedialVertexOfEdge R e := by
    exact ((fkRectTorusMedialEdgeEquiv R).symm_apply_apply v).symm
  rw [hv]
  rcases e with ⟨b, x, y⟩
  cases b <;> cases side
  all_goals
    apply (fkRectTorusMedialEdgeEquiv R).symm.injective
    simp only [Equiv.symm_apply_apply]
    simp only [fkRectTorusMedialEdgeEquiv_vertexOfEdge]
    apply Prod.ext
    · apply Fin.ext
      rw [fkRectTorusMedialEdgeEquiv_symm_fst_val]
      simp [fkMedialBondMate, fkRectMedialBondEdgeIndex,
        fkRectMedialVertexOfEdge_fst_val,
        fkRectTorusMedialEdgeEquiv_vertexOfEdge, Fin.val_mk,
        Bool.toNat, FKRectTorus.medialTorus, finitePeriodicSucc,
        SixVertexArrows.cyclicPred] <;>
      first
      | (omega; done)
      | simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          double_cyclicPred R.width x.val R.width_pos x.isLt
      | simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          double_finitePeriodicSucc R.width x.val R.width_pos x.isLt
      | (rw [show 1 + 2 * x.val + 2 * R.width - 1 =
            2 * x.val + 2 * R.width by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; done)
      | (rw [Nat.mod_eq_of_lt (by omega)]; done)
      | exact Nat.mod_eq_of_lt (double_add_one_lt R.width x.val x.isLt)
      | exact Nat.mod_eq_of_lt (double_mul_add_one_lt R.width x.val x.isLt)
      | exact double_mul_add_one_mod R.width x.val x.isLt
      | ac_rfl
    · rw [fkRectTorusMedialEdgeEquiv_symm_snd] <;>
      (simp [fkMedialBondMate, fkRectMedialBondEdgeIndex,
        fkRectMedialVertexOfEdge_snd] <;> rfl)


theorem fkRectMedialDartPrimalLabel_bondMate
    (R : FKRectTorus) (d : FKMedialDart R.medialTorus) :
    fkRectMedialDartPrimalLabel R (fkMedialBondMate R.medialTorus d) =
      fkRectMedialDartPrimalLabel R d := by
  rcases d with ⟨v, side⟩
  let e := fkRectTorusMedialEdgeEquiv R v
  have hi := fkRectTorusMedialEdgeEquiv_bondMate R (v, side)
  change fkRectTorusMedialEdgeEquiv R
      (fkMedialBondMate R.medialTorus (v, side)).1 =
    fkRectMedialBondEdgeIndex R e side at hi
  cases side <;>
    simp only [fkMedialBondMate] at hi ⊢ <;>
    unfold fkRectMedialDartPrimalLabel <;>
    rw [hi, show fkRectTorusMedialEdgeEquiv R v = e from rfl] <;>
    rcases e with ⟨b, x, y⟩ <;> cases b <;>
    by_cases hy : Even y.val <;>
    simp [fkRectMedialBondEdgeIndex, fkRectMedialWestPrimal,
      fkRectMedialEastPrimal, fkRectClosedPairingAtEdge, hy,
      even_finitePeriodicSucc_iff, even_cyclicPred_iff,
      finitePeriodicSucc_cyclicPred, svCyclicPred_finitePeriodicSucc]

end StatMech.FrontierD
