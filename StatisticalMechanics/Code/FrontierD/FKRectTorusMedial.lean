/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKMedialLoopTopology

namespace StatMech.FrontierD



structure FKRectTorus where
  width : Nat
  height : Nat
  width_gt_two : 2 < width
  height_gt_two : 2 < height
  height_even : Even height

def FKRectTorus.width_pos (R : FKRectTorus) : 0 < R.width := by
  exact lt_trans (by norm_num : 0 < 2) R.width_gt_two

def FKRectTorus.height_pos (R : FKRectTorus) : 0 < R.height := by
  exact lt_trans (by norm_num : 0 < 2) R.height_gt_two

def FKRectTorus.medialTorus (R : FKRectTorus) : EvenTorus where
  width := 2 * R.width
  height := R.height
  width_pos := mul_pos (by norm_num) R.width_pos
  height_pos := R.height_pos
  width_even := ⟨R.width, by omega⟩
  height_even := R.height_even

abbrev FKRectTorus.Vertex (R : FKRectTorus) := Fin R.width × Fin R.height



abbrev FKRectTorus.EdgeIndex (R : FKRectTorus) := Bool × R.Vertex



def fkRectTorusMedialEdgeEquiv (R : FKRectTorus) :
    R.medialTorus.Vertex ≃ R.EdgeIndex :=
  (Equiv.prodCongr
      (((finCongr (Nat.mul_comm 2 R.width)).trans
        (finProdFinEquiv.symm : Fin (R.width * 2) ≃ Fin R.width × Fin 2)).trans
          (Equiv.prodComm (Fin R.width) (Fin 2)))
      (Equiv.refl (Fin R.height))).trans
    ((Equiv.prodAssoc (Fin 2) (Fin R.width) (Fin R.height)).trans
      (Equiv.prodCongr finTwoEquiv (Equiv.refl R.Vertex)))


abbrev FKRectTorus.Configuration (R : FKRectTorus) :=
  ConfigSpace R.EdgeIndex

def fkRectBoolXorEquiv (b : Bool) : Bool ≃ Bool where
  toFun x := x ^^ b
  invFun x := x ^^ b
  left_inv x := by cases x <;> cases b <;> rfl
  right_inv x := by cases x <;> cases b <;> rfl




def fkRectClosedPairingAtEdge {R : FKRectTorus} (a : R.EdgeIndex) : Bool :=
  decide (Even a.2.2.val) ^^ a.1



def fkRectConfigurationToMedialPairing (R : FKRectTorus) :
    R.Configuration ≃ FKMedialLoopPairing R.medialTorus :=
  (Equiv.arrowCongr (fkRectTorusMedialEdgeEquiv R) (Equiv.refl Bool)).symm |>.trans
    (Equiv.piCongrRight fun v =>
      fkRectBoolXorEquiv
        (fkRectClosedPairingAtEdge (fkRectTorusMedialEdgeEquiv R v)))

@[simp] theorem fkRectConfigurationToMedialPairing_apply
    (R : FKRectTorus) (omega : R.Configuration)
    (v : R.medialTorus.Vertex) :
    fkRectConfigurationToMedialPairing R omega v =
      (omega (fkRectTorusMedialEdgeEquiv R v) ^^
        fkRectClosedPairingAtEdge (fkRectTorusMedialEdgeEquiv R v)) := rfl


def fkRectTorusIndexedEdge (R : FKRectTorus) (a : R.EdgeIndex) :
    Sym2 R.Vertex :=
  if a.1 then
    s(a.2, (a.2.1, SixVertexArrows.cyclicPred R.height_pos a.2.2))
  else if Even a.2.2.val then
    s(a.2, (SixVertexArrows.cyclicPred R.width_pos a.2.1,
      SixVertexArrows.cyclicPred R.height_pos a.2.2))
  else
    s((SixVertexArrows.cyclicPred R.width_pos a.2.1, a.2.2),
      (a.2.1, SixVertexArrows.cyclicPred R.height_pos a.2.2))

theorem finitePeriodicSucc_ne_self {N : Nat} (hN : 1 < N) (i : Fin N) :
    finitePeriodicSucc (lt_trans Nat.zero_lt_one hN) i ≠ i := by
  intro h
  have hval := congrArg Fin.val h
  simp only [finitePeriodicSucc, Fin.val_mk] at hval
  by_cases hi : i.val + 1 < N
  · rw [Nat.mod_eq_of_lt hi] at hval
    omega
  · have hieq : i.val + 1 = N := by omega
    rw [hieq, Nat.mod_self] at hval
    omega

theorem cyclicPred_ne_self {N : Nat} (hN : 1 < N) (i : Fin N) :
    SixVertexArrows.cyclicPred (lt_trans Nat.zero_lt_one hN) i ≠ i := by
  intro h
  have hsucc := congrArg
    (finitePeriodicSucc (lt_trans Nat.zero_lt_one hN)) h
  rw [finitePeriodicSucc_cyclicPred] at hsucc
  exact finitePeriodicSucc_ne_self hN i hsucc.symm

theorem fkRectTorusIndexedEdge_ne_diag (R : FKRectTorus)
    (a : R.EdgeIndex) (x : R.Vertex) :
    fkRectTorusIndexedEdge R a ≠ s(x, x) := by
  intro ha
  rcases a with ⟨dir, a⟩
  cases dir
  · simp only [fkRectTorusIndexedEdge, Bool.false_eq_true, ↓reduceIte] at ha
    split at ha <;> rcases Sym2.eq_iff.mp ha with heq | heq
    all_goals
      have hy := congrArg Prod.snd heq.1
      have hpred := congrArg Prod.snd heq.2
      exact cyclicPred_ne_self (lt_trans Nat.one_lt_two R.height_gt_two) a.2
        (hpred.trans hy.symm)
  · simp only [fkRectTorusIndexedEdge, ↓reduceIte] at ha
    rcases Sym2.eq_iff.mp ha with heq | heq
    · have hbase := congrArg Prod.snd heq.1
      have hpred := congrArg Prod.snd heq.2
      exact cyclicPred_ne_self (lt_trans Nat.one_lt_two R.height_gt_two) a.2
        (hpred.trans hbase.symm)
    · have hbase := congrArg Prod.snd heq.1
      have hpred := congrArg Prod.snd heq.2
      exact cyclicPred_ne_self (lt_trans Nat.one_lt_two R.height_gt_two) a.2
        (hpred.trans hbase.symm)


def fkRectTorusGraph (R : FKRectTorus) : SimpleGraph R.Vertex where
  Adj x y := ∃ a : R.EdgeIndex, fkRectTorusIndexedEdge R a = s(x, y)
  symm := by
    rintro x y ⟨a, ha⟩
    exact ⟨a, by simpa [Sym2.eq_swap] using ha⟩
  loopless := ⟨by
    intro x h
    obtain ⟨a, ha⟩ := h
    exact fkRectTorusIndexedEdge_ne_diag R a x ha⟩



def fkRectOpenGraph (R : FKRectTorus) (omega : R.Configuration) :
    SimpleGraph R.Vertex where
  Adj x y := ∃ a : R.EdgeIndex,
    omega a = true ∧ fkRectTorusIndexedEdge R a = s(x, y)
  symm := by
    rintro x y ⟨a, hopen, ha⟩
    exact ⟨a, hopen, by simpa [Sym2.eq_swap] using ha⟩
  loopless := ⟨by
    intro x h
    obtain ⟨a, _, ha⟩ := h
    exact fkRectTorusIndexedEdge_ne_diag R a x ha⟩

end StatMech.FrontierD
