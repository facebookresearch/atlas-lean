/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexDisagreementComponentCType
import Code.FrontierD.FKMedialLoopTopology
import Code.FrontierD.FKRectTorusMedial
import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Cycle.Factors










open Finset

namespace StatMech.FrontierD

noncomputable section


def sixVertexLocalDisagreementSides
    (p q : SixVertexLocalIncomingPattern) : Finset (Fin 4) :=
  Finset.univ.filter fun d => p d != q d

@[simp] theorem mem_sixVertexLocalDisagreementSides
    (p q : SixVertexLocalIncomingPattern) (d : Fin 4) :
    d ∈ sixVertexLocalDisagreementSides p q ↔ p d ≠ q d := by
  simp [sixVertexLocalDisagreementSides]

theorem card_sixVertexLocalDisagreementSides
    (p q : SixVertexLocalIncomingPattern) :
    (sixVertexLocalDisagreementSides p q).card =
      ∑ d, if p d ≠ q d then 1 else 0 := by
  classical
  rw [Finset.card_eq_sum_ones, sixVertexLocalDisagreementSides,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h : p d = q d <;> simp [h]


theorem existsUnique_mem_ne_of_card_eq_two
    {α : Type*} [DecidableEq α] (s : Finset α) (d : α)
    (hcard : s.card = 2) (hd : d ∈ s) :
    ∃! e, e ∈ s ∧ e ≠ d := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl
  · refine ⟨b, by simp [hab.symm], ?_⟩
    intro e he
    rcases he with ⟨he, hne⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact False.elim (hne rfl)
    · rfl
  · refine ⟨a, by simp [hab], ?_⟩
    intro e he
    rcases he with ⟨he, hne⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · rfl
    · exact False.elim (hne rfl)


noncomputable def finsetOther
    {α : Type*} [DecidableEq α] (s : Finset α) (d : α)
    (hcard : s.card = 2) (hd : d ∈ s) : α :=
  Classical.choose (existsUnique_mem_ne_of_card_eq_two s d hcard hd)

theorem finsetOther_mem
    {α : Type*} [DecidableEq α] (s : Finset α) (d : α)
    (hcard : s.card = 2) (hd : d ∈ s) :
    finsetOther s d hcard hd ∈ s :=
  (Classical.choose_spec
    (existsUnique_mem_ne_of_card_eq_two s d hcard hd)).1.1

theorem finsetOther_ne
    {α : Type*} [DecidableEq α] (s : Finset α) (d : α)
    (hcard : s.card = 2) (hd : d ∈ s) :
    finsetOther s d hcard hd ≠ d :=
  (Classical.choose_spec
    (existsUnique_mem_ne_of_card_eq_two s d hcard hd)).1.2

theorem finsetOther_involutive
    {α : Type*} [DecidableEq α] (s : Finset α) (d : α)
    (hcard : s.card = 2) (hd : d ∈ s) :
    finsetOther s (finsetOther s d hcard hd) hcard
        (finsetOther_mem s d hcard hd) = d := by
  symm
  apply (Classical.choose_spec
    (existsUnique_mem_ne_of_card_eq_two s
      (finsetOther s d hcard hd) hcard
      (finsetOther_mem s d hcard hd))).2
  exact ⟨hd, (finsetOther_ne s d hcard hd).symm⟩



def SixVertexLocallyDegreeTwo
    {T : EvenTorus} (omega eta : SixVertexArrows T) : Prop :=
  ∀ v, (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 0 ∨
    (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2


abbrev SixVertexTorusDart (T : EvenTorus) := T.Vertex × Fin 4


def sixVertexTorusDartEdge
    (T : EvenTorus) (d : SixVertexTorusDart T) : SixVertexTorusEdge T :=
  sixVertexTorusIncidentEdge T d.1 d.2


def sixVertexTorusDartBondMate
    (T : EvenTorus) (d : SixVertexTorusDart T) : SixVertexTorusDart T :=
  ![((SixVertexArrows.cyclicPred T.width_pos d.1.1, d.1.2), (1 : Fin 4)),
    ((finitePeriodicSucc T.width_pos d.1.1, d.1.2), (0 : Fin 4)),
    ((d.1.1, SixVertexArrows.cyclicPred T.height_pos d.1.2), (3 : Fin 4)),
    ((d.1.1, finitePeriodicSucc T.height_pos d.1.2), (2 : Fin 4))] d.2

theorem sixVertexTorusDartBondMate_involutive
    (T : EvenTorus) (d : SixVertexTorusDart T) :
    sixVertexTorusDartBondMate T (sixVertexTorusDartBondMate T d) = d := by
  rcases d with ⟨⟨i, j⟩, side⟩
  fin_cases side <;>
    simp [sixVertexTorusDartBondMate, finitePeriodicSucc_cyclicPred,
      svCyclicPred_finitePeriodicSucc]

theorem EvenTorus.one_lt_width (T : EvenTorus) : 1 < T.width := by
  obtain ⟨k, hk⟩ := T.width_even
  have hpos := T.width_pos
  rw [hk] at hpos ⊢
  omega

theorem EvenTorus.one_lt_height (T : EvenTorus) : 1 < T.height := by
  obtain ⟨k, hk⟩ := T.height_even
  have hpos := T.height_pos
  rw [hk] at hpos ⊢
  omega

theorem sixVertexTorusDartBondMate_vertex_ne
    (T : EvenTorus) (d : SixVertexTorusDart T) :
    (sixVertexTorusDartBondMate T d).1 ≠ d.1 := by
  rcases d with ⟨⟨i, j⟩, side⟩
  fin_cases side
  · intro h
    exact cyclicPred_ne_self T.one_lt_width i
      (congrArg Prod.fst h)
  · intro h
    exact finitePeriodicSucc_ne_self T.one_lt_width i
      (congrArg Prod.fst h)
  · intro h
    exact cyclicPred_ne_self T.one_lt_height j
      (congrArg Prod.snd h)
  · intro h
    exact finitePeriodicSucc_ne_self T.one_lt_height j
      (congrArg Prod.snd h)

theorem sixVertexTorusDartEdge_bondMate
    (T : EvenTorus) (d : SixVertexTorusDart T) :
    sixVertexTorusDartEdge T (sixVertexTorusDartBondMate T d) =
      sixVertexTorusDartEdge T d := by
  rcases d with ⟨⟨i, j⟩, side⟩
  fin_cases side <;>
    simp [sixVertexTorusDartBondMate, sixVertexTorusDartEdge,
      sixVertexTorusIncidentEdge, svCyclicPred_finitePeriodicSucc]



abbrev SixVertexDisagreementDart
    {T : EvenTorus} (omega eta : SixVertexArrows T) :=
  {d : SixVertexTorusDart T //
    sixVertexTorusEdgeDisagrees omega eta (sixVertexTorusDartEdge T d)}


def sixVertexDisagreementBondMate
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (d : SixVertexDisagreementDart omega eta) :
    SixVertexDisagreementDart omega eta :=
  ⟨sixVertexTorusDartBondMate T d.1, by
    rw [sixVertexTorusDartEdge_bondMate]
    exact d.2⟩

theorem sixVertexDisagreementBondMate_involutive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (d : SixVertexDisagreementDart omega eta) :
    sixVertexDisagreementBondMate
        (sixVertexDisagreementBondMate d) = d := by
  apply Subtype.ext
  exact sixVertexTorusDartBondMate_involutive T d.1

theorem sixVertexDisagreementDart_side_mem
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (d : SixVertexDisagreementDart omega eta) :
    d.1.2 ∈ sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega d.1.1)
      (sixVertexLocalIncomingPattern eta d.1.1) := by
  rw [mem_sixVertexLocalDisagreementSides,
    sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees]
  exact d.2

theorem sixVertexDisagreementDart_local_card_eq_two
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexDisagreementDart omega eta) :
    (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega d.1.1)
      (sixVertexLocalIncomingPattern eta d.1.1)).card = 2 := by
  rcases hdegree d.1.1 with hzero | htwo
  · have hmem := sixVertexDisagreementDart_side_mem d
    rw [Finset.card_eq_zero.mp hzero] at hmem
    exact False.elim (by simpa using hmem)
  · exact htwo


noncomputable def sixVertexDegreeTwoLocalMate
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexDisagreementDart omega eta) :
    SixVertexDisagreementDart omega eta :=
  let sides := sixVertexLocalDisagreementSides
    (sixVertexLocalIncomingPattern omega d.1.1)
    (sixVertexLocalIncomingPattern eta d.1.1)
  let hcard : sides.card = 2 :=
    sixVertexDisagreementDart_local_card_eq_two hdegree d
  let hd : d.1.2 ∈ sides := sixVertexDisagreementDart_side_mem d
  let other := finsetOther sides d.1.2 hcard hd
  ⟨(d.1.1, other), by
    change sixVertexTorusEdgeDisagrees omega eta
      (sixVertexTorusIncidentEdge T d.1.1 other)
    rw [← sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees]
    exact (mem_sixVertexLocalDisagreementSides _ _ other).mp
      (finsetOther_mem sides d.1.2 hcard hd)⟩

@[simp] theorem sixVertexDegreeTwoLocalMate_vertex
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexDisagreementDart omega eta) :
    (sixVertexDegreeTwoLocalMate hdegree d).1.1 = d.1.1 := by
  simp [sixVertexDegreeTwoLocalMate]

theorem sixVertexDegreeTwoLocalMate_involutive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexDisagreementDart omega eta) :
    sixVertexDegreeTwoLocalMate hdegree
        (sixVertexDegreeTwoLocalMate hdegree d) = d := by
  apply Subtype.ext
  apply Prod.ext
  · simp [sixVertexDegreeTwoLocalMate]
  · simp only [sixVertexDegreeTwoLocalMate]
    exact finsetOther_involutive _ _ _ _

theorem sixVertexDegreeTwoLocalMate_side_mem
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexDisagreementDart omega eta) :
    (sixVertexDegreeTwoLocalMate hdegree d).1.2 ∈
      sixVertexLocalDisagreementSides
        (sixVertexLocalIncomingPattern omega d.1.1)
        (sixVertexLocalIncomingPattern eta d.1.1) := by
  simp only [sixVertexDegreeTwoLocalMate]
  apply finsetOther_mem

theorem sixVertexDegreeTwoLocalMate_side_ne
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexDisagreementDart omega eta) :
    (sixVertexDegreeTwoLocalMate hdegree d).1.2 ≠ d.1.2 := by
  simp only [sixVertexDegreeTwoLocalMate]
  apply finsetOther_ne

theorem sixVertexDegreeTwoLocalMate_ne_bondMate
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexDisagreementDart omega eta) :
    sixVertexDegreeTwoLocalMate hdegree d ≠
      sixVertexDisagreementBondMate d := by
  intro h
  have hvertex := congrArg (fun e : SixVertexDisagreementDart omega eta =>
    e.1.1) h
  change (sixVertexDegreeTwoLocalMate hdegree d).1.1 =
    (sixVertexDisagreementBondMate d).1.1 at hvertex
  rw [sixVertexDegreeTwoLocalMate_vertex] at hvertex
  exact sixVertexTorusDartBondMate_vertex_ne T d.1 hvertex.symm



theorem sixVertexLocalIncoming_ne_at_two_disagreements
    (p q : SixVertexLocalIncomingPattern) (d e : Fin 4)
    (hp : p.Ice) (hq : q.Ice)
    (hcard : (sixVertexLocalDisagreementSides p q).card = 2)
    (hd : d ∈ sixVertexLocalDisagreementSides p q)
    (he : e ∈ sixVertexLocalDisagreementSides p q) (hne : e ≠ d) :
    p e ≠ p d := by
  decide +revert

theorem sixVertexDegreeTwoLocalMate_incoming_ne
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexDisagreementDart omega eta) :
    sixVertexLocalIncomingPattern omega
        (sixVertexDegreeTwoLocalMate hdegree d).1.1
        (sixVertexDegreeTwoLocalMate hdegree d).1.2 ≠
      sixVertexLocalIncomingPattern omega d.1.1 d.1.2 := by
  rw [sixVertexDegreeTwoLocalMate_vertex]
  exact sixVertexLocalIncoming_ne_at_two_disagreements
    (sixVertexLocalIncomingPattern omega d.1.1)
    (sixVertexLocalIncomingPattern eta d.1.1) d.1.2
    (sixVertexDegreeTwoLocalMate hdegree d).1.2
    (sixVertexLocalIncomingPattern_ice omega homega d.1.1)
    (sixVertexLocalIncomingPattern_ice eta heta d.1.1)
    (sixVertexDisagreementDart_local_card_eq_two hdegree d)
    (sixVertexDisagreementDart_side_mem d)
    (sixVertexDegreeTwoLocalMate_side_mem hdegree d)
    (sixVertexDegreeTwoLocalMate_side_ne hdegree d)



theorem sixVertexLocalIncomingPattern_bondMate_ne
    {T : EvenTorus} (omega : SixVertexArrows T)
    (d : SixVertexTorusDart T) :
    sixVertexLocalIncomingPattern omega
        (sixVertexTorusDartBondMate T d).1
        (sixVertexTorusDartBondMate T d).2 ≠
      sixVertexLocalIncomingPattern omega d.1 d.2 := by
  rcases d with ⟨⟨i, j⟩, side⟩
  fin_cases side <;>
    simp [sixVertexTorusDartBondMate, sixVertexLocalIncomingPattern,
      fkLoopWestIncoming, fkLoopEastIncoming, fkLoopSouthIncoming,
      fkLoopNorthIncoming, svCyclicPred_finitePeriodicSucc]


def sixVertexDisagreementBondMateEquiv
    {T : EvenTorus} {omega eta : SixVertexArrows T} :
    SixVertexDisagreementDart omega eta ≃
      SixVertexDisagreementDart omega eta where
  toFun := sixVertexDisagreementBondMate
  invFun := sixVertexDisagreementBondMate
  left_inv := sixVertexDisagreementBondMate_involutive
  right_inv := sixVertexDisagreementBondMate_involutive



def sixVertexDegreeTwoLocalMateEquiv
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    SixVertexDisagreementDart omega eta ≃
      SixVertexDisagreementDart omega eta where
  toFun := sixVertexDegreeTwoLocalMate hdegree
  invFun := sixVertexDegreeTwoLocalMate hdegree
  left_inv := sixVertexDegreeTwoLocalMate_involutive hdegree
  right_inv := sixVertexDegreeTwoLocalMate_involutive hdegree



def sixVertexDegreeTwoStrandSuccessor
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    Equiv.Perm (SixVertexDisagreementDart omega eta) :=
  (sixVertexDegreeTwoLocalMateEquiv hdegree).trans
    sixVertexDisagreementBondMateEquiv

@[simp] theorem sixVertexDegreeTwoStrandSuccessor_apply
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexDisagreementDart omega eta) :
    sixVertexDegreeTwoStrandSuccessor hdegree d =
      sixVertexDisagreementBondMate
        (sixVertexDegreeTwoLocalMate hdegree d) :=
  rfl

theorem sixVertexDegreeTwoStrandSuccessor_ne
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexDisagreementDart omega eta) :
    sixVertexDegreeTwoStrandSuccessor hdegree d ≠ d := by
  intro hfixed
  have hbond := congrArg sixVertexDisagreementBondMate hfixed
  rw [sixVertexDegreeTwoStrandSuccessor_apply,
    sixVertexDisagreementBondMate_involutive] at hbond
  exact sixVertexDegreeTwoLocalMate_ne_bondMate hdegree d hbond



theorem sixVertexDegreeTwoStrandSuccessor_incoming
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexDisagreementDart omega eta) :
    sixVertexLocalIncomingPattern omega
        (sixVertexDegreeTwoStrandSuccessor hdegree d).1.1
        (sixVertexDegreeTwoStrandSuccessor hdegree d).1.2 =
      sixVertexLocalIncomingPattern omega d.1.1 d.1.2 := by
  rw [sixVertexDegreeTwoStrandSuccessor_apply]
  change sixVertexLocalIncomingPattern omega
      (sixVertexTorusDartBondMate T
        (sixVertexDegreeTwoLocalMate hdegree d).1).1
      (sixVertexTorusDartBondMate T
        (sixVertexDegreeTwoLocalMate hdegree d).1).2 = _
  have hlocal := sixVertexDegreeTwoLocalMate_incoming_ne
    homega heta hdegree d
  have hbond := sixVertexLocalIncomingPattern_bondMate_ne omega
    (sixVertexDegreeTwoLocalMate hdegree d).1
  generalize hd : sixVertexLocalIncomingPattern omega d.1.1 d.1.2 = bd at hlocal ⊢
  generalize hl : sixVertexLocalIncomingPattern omega
    (sixVertexDegreeTwoLocalMate hdegree d).1.1
    (sixVertexDegreeTwoLocalMate hdegree d).1.2 = bl at hlocal hbond
  generalize hs : sixVertexLocalIncomingPattern omega
    (sixVertexTorusDartBondMate T
      (sixVertexDegreeTwoLocalMate hdegree d).1).1
    (sixVertexTorusDartBondMate T
      (sixVertexDegreeTwoLocalMate hdegree d).1).2 = bs at hbond ⊢
  cases bd <;> cases bl <;> cases bs <;> simp_all



abbrev SixVertexOrientedDisagreementDart
    {T : EvenTorus} (omega eta : SixVertexArrows T) :=
  {d : SixVertexDisagreementDart omega eta //
    sixVertexLocalIncomingPattern omega d.1.1 d.1.2 = true}


def sixVertexOrientedDegreeTwoStrandSuccessor
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    Equiv.Perm (SixVertexOrientedDisagreementDart omega eta) :=
  (sixVertexDegreeTwoStrandSuccessor hdegree).subtypePerm fun d => by
    rw [sixVertexDegreeTwoStrandSuccessor_incoming homega heta hdegree]

@[simp] theorem sixVertexOrientedDegreeTwoStrandSuccessor_val
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexOrientedDisagreementDart omega eta) :
    (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree d).1 =
        sixVertexDegreeTwoStrandSuccessor hdegree d.1 :=
  rfl

theorem sixVertexOrientedDegreeTwoStrandSuccessor_ne
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexOrientedDisagreementDart omega eta) :
    sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree d ≠ d := by
  intro h
  exact sixVertexDegreeTwoStrandSuccessor_ne hdegree d.1
    (congrArg Subtype.val h)

theorem sixVertexOrientedDegreeTwoStrandSuccessor_support
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    (sixVertexOrientedDegreeTwoStrandSuccessor
      homega heta hdegree).support = Finset.univ := by
  apply Finset.eq_univ_iff_forall.mpr
  intro d
  exact Equiv.Perm.mem_support.mpr
    (sixVertexOrientedDegreeTwoStrandSuccessor_ne
      homega heta hdegree d)


def sixVertexTorusEdgeOutgoingDart
    {T : EvenTorus} (omega : SixVertexArrows T)
    (e : SixVertexTorusEdge T) : SixVertexTorusDart T :=
  if e.1 = 0 then
    if omega.horizontal e.2 then (e.2, (1 : Fin 4))
    else ((finitePeriodicSucc T.width_pos e.2.1, e.2.2), (0 : Fin 4))
  else
    if omega.vertical e.2 then (e.2, (3 : Fin 4))
    else ((e.2.1, finitePeriodicSucc T.height_pos e.2.2), (2 : Fin 4))

@[simp] theorem sixVertexTorusDartEdge_outgoingDart
    {T : EvenTorus} (omega : SixVertexArrows T)
    (e : SixVertexTorusEdge T) :
    sixVertexTorusDartEdge T (sixVertexTorusEdgeOutgoingDart omega e) = e := by
  rcases e with ⟨dir, ⟨i, j⟩⟩
  fin_cases dir <;> cases h : omega.horizontal (i, j) <;>
    cases hv : omega.vertical (i, j) <;>
    simp [sixVertexTorusEdgeOutgoingDart, sixVertexTorusDartEdge,
      sixVertexTorusIncidentEdge, h, hv,
      svCyclicPred_finitePeriodicSucc]

@[simp] theorem sixVertexTorusEdgeOutgoingDart_incoming
    {T : EvenTorus} (omega : SixVertexArrows T)
    (e : SixVertexTorusEdge T) :
    sixVertexLocalIncomingPattern omega
        (sixVertexTorusEdgeOutgoingDart omega e).1
        (sixVertexTorusEdgeOutgoingDart omega e).2 = false := by
  rcases e with ⟨dir, ⟨i, j⟩⟩
  fin_cases dir <;> cases h : omega.horizontal (i, j) <;>
    cases hv : omega.vertical (i, j) <;>
    simp [sixVertexTorusEdgeOutgoingDart, sixVertexLocalIncomingPattern,
      fkLoopWestIncoming, fkLoopEastIncoming, fkLoopSouthIncoming,
      fkLoopNorthIncoming, h, hv, svCyclicPred_finitePeriodicSucc]



theorem sixVertexTorusEdgeOutgoingDart_edge_of_incoming_false
    {T : EvenTorus} (omega : SixVertexArrows T)
    (d : SixVertexTorusDart T)
    (hout : sixVertexLocalIncomingPattern omega d.1 d.2 = false) :
    sixVertexTorusEdgeOutgoingDart omega
      (sixVertexTorusDartEdge T d) = d := by
  rcases d with ⟨⟨i, j⟩, side⟩
  fin_cases side <;>
    simp [sixVertexTorusEdgeOutgoingDart, sixVertexTorusDartEdge,
      sixVertexTorusIncidentEdge, sixVertexLocalIncomingPattern,
      fkLoopWestIncoming, fkLoopEastIncoming, fkLoopSouthIncoming,
      fkLoopNorthIncoming, finitePeriodicSucc_cyclicPred,
      svCyclicPred_finitePeriodicSucc] at hout ⊢ <;>
    exact hout


abbrev SixVertexDisagreementEdge
    {T : EvenTorus} (omega eta : SixVertexArrows T) :=
  {e : SixVertexTorusEdge T // sixVertexTorusEdgeDisagrees omega eta e}




noncomputable def sixVertexOrientedDisagreementDartEquivEdge
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    SixVertexOrientedDisagreementDart omega eta ≃
      SixVertexDisagreementEdge omega eta := by
  let toEdge : SixVertexOrientedDisagreementDart omega eta →
      SixVertexDisagreementEdge omega eta := fun d =>
    ⟨sixVertexTorusDartEdge T
      (sixVertexDegreeTwoLocalMate hdegree d.1).1,
      (sixVertexDegreeTwoLocalMate hdegree d.1).2⟩
  apply Equiv.ofBijective toEdge
  constructor
  · intro a b hab
    have haNe := sixVertexDegreeTwoLocalMate_incoming_ne
      homega heta hdegree a.1
    have hbNe := sixVertexDegreeTwoLocalMate_incoming_ne
      homega heta hdegree b.1
    have haFalse : sixVertexLocalIncomingPattern omega
        (sixVertexDegreeTwoLocalMate hdegree a.1).1.1
        (sixVertexDegreeTwoLocalMate hdegree a.1).1.2 = false := by
      generalize hma : sixVertexLocalIncomingPattern omega
        (sixVertexDegreeTwoLocalMate hdegree a.1).1.1
        (sixVertexDegreeTwoLocalMate hdegree a.1).1.2 = ma at haNe ⊢
      rw [a.2] at haNe
      cases ma <;> simp_all
    have hbFalse : sixVertexLocalIncomingPattern omega
        (sixVertexDegreeTwoLocalMate hdegree b.1).1.1
        (sixVertexDegreeTwoLocalMate hdegree b.1).1.2 = false := by
      generalize hmb : sixVertexLocalIncomingPattern omega
        (sixVertexDegreeTwoLocalMate hdegree b.1).1.1
        (sixVertexDegreeTwoLocalMate hdegree b.1).1.2 = mb at hbNe ⊢
      rw [b.2] at hbNe
      cases mb <;> simp_all
    have haOut := sixVertexTorusEdgeOutgoingDart_edge_of_incoming_false
      omega (sixVertexDegreeTwoLocalMate hdegree a.1).1 haFalse
    have hbOut := sixVertexTorusEdgeOutgoingDart_edge_of_incoming_false
      omega (sixVertexDegreeTwoLocalMate hdegree b.1).1 hbFalse
    have hmate : sixVertexDegreeTwoLocalMate hdegree a.1 =
        sixVertexDegreeTwoLocalMate hdegree b.1 := by
      have hedge := congrArg
        (fun e : SixVertexDisagreementEdge omega eta => e.1) hab
      change sixVertexTorusDartEdge T
          (sixVertexDegreeTwoLocalMate hdegree a.1).1 =
        sixVertexTorusDartEdge T
          (sixVertexDegreeTwoLocalMate hdegree b.1).1 at hedge
      apply Subtype.ext
      rw [← haOut, ← hbOut]
      exact congrArg (sixVertexTorusEdgeOutgoingDart omega) hedge
    have horiented : a.1 = b.1 := by
      rw [← sixVertexDegreeTwoLocalMate_involutive hdegree a.1,
        ← sixVertexDegreeTwoLocalMate_involutive hdegree b.1,
        hmate]
    exact Subtype.ext horiented
  · intro e
    let outgoing : SixVertexDisagreementDart omega eta :=
      ⟨sixVertexTorusEdgeOutgoingDart omega e.1, by
        rw [sixVertexTorusDartEdge_outgoingDart]
        exact e.2⟩
    have hout : sixVertexLocalIncomingPattern omega
        outgoing.1.1 outgoing.1.2 = false := by
      exact sixVertexTorusEdgeOutgoingDart_incoming omega e.1
    have hmateNe := sixVertexDegreeTwoLocalMate_incoming_ne
      homega heta hdegree outgoing
    have hmateTrue : sixVertexLocalIncomingPattern omega
        (sixVertexDegreeTwoLocalMate hdegree outgoing).1.1
        (sixVertexDegreeTwoLocalMate hdegree outgoing).1.2 = true := by
      generalize hm : sixVertexLocalIncomingPattern omega
        (sixVertexDegreeTwoLocalMate hdegree outgoing).1.1
        (sixVertexDegreeTwoLocalMate hdegree outgoing).1.2 = m at hmateNe ⊢
      rw [hout] at hmateNe
      cases m <;> simp_all
    let source : SixVertexOrientedDisagreementDart omega eta :=
      ⟨sixVertexDegreeTwoLocalMate hdegree outgoing, hmateTrue⟩
    refine ⟨source, ?_⟩
    apply Subtype.ext
    change sixVertexTorusDartEdge T
      (sixVertexDegreeTwoLocalMate hdegree source.1).1 = e.1
    rw [show source.1 = sixVertexDegreeTwoLocalMate hdegree outgoing by rfl,
      sixVertexDegreeTwoLocalMate_involutive,
      sixVertexTorusDartEdge_outgoingDart]


def sixVertexTorusEdgeSeamSign
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (e : SixVertexTorusEdge T) : Int :=
  if e.1 = 1 ∧ e.2.2 = svFinLast T.height_pos then
    (eta.vertical e.2).toNat - (omega.vertical e.2).toNat
  else 0

theorem sixVertexTorusEdgeSeamSign_eq_zero_or_one_or_neg_one
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (e : SixVertexTorusEdge T) :
    sixVertexTorusEdgeSeamSign omega eta e = 0 ∨
      sixVertexTorusEdgeSeamSign omega eta e = 1 ∨
      sixVertexTorusEdgeSeamSign omega eta e = -1 := by
  unfold sixVertexTorusEdgeSeamSign
  split
  · cases omega.vertical e.2 <;> cases eta.vertical e.2 <;> simp
  · simp

theorem sixVertexTorusEdgeSeamSign_eq_zero_of_not_disagrees
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (e : SixVertexTorusEdge T)
    (hagree : ¬ sixVertexTorusEdgeDisagrees omega eta e) :
    sixVertexTorusEdgeSeamSign omega eta e = 0 := by
  rcases e with ⟨dir, ⟨i, j⟩⟩
  fin_cases dir
  · simp [sixVertexTorusEdgeSeamSign]
  · simp [sixVertexTorusEdgeDisagrees, sixVertexTorusEdgeArrow] at hagree
    by_cases hj : j = svFinLast T.height_pos
    · subst j
      simp [sixVertexTorusEdgeSeamSign, ← hagree]
    · simp [sixVertexTorusEdgeSeamSign, hj]



theorem sum_sixVertexDisagreementEdge_seamSign
    {T : EvenTorus} (omega eta : SixVertexArrows T) :
    (∑ e : SixVertexDisagreementEdge omega eta,
        sixVertexTorusEdgeSeamSign omega eta e.1) =
      ∑ e : SixVertexTorusEdge T,
        sixVertexTorusEdgeSeamSign omega eta e := by
  classical
  rw [← Finset.sum_subtype
    (Finset.univ.filter fun e : SixVertexTorusEdge T =>
      sixVertexTorusEdgeDisagrees omega eta e) (by simp)
    (sixVertexTorusEdgeSeamSign omega eta), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hdis : sixVertexTorusEdgeDisagrees omega eta e
  · simp [hdis]
  · simp [hdis,
      sixVertexTorusEdgeSeamSign_eq_zero_of_not_disagrees omega eta e hdis]



theorem sum_sixVertexTorusEdge_seamSign_eq_fullTransfer
    {T : EvenTorus} (omega eta : SixVertexArrows T) :
    (∑ e : SixVertexTorusEdge T,
        sixVertexTorusEdgeSeamSign omega eta e) =
      sixVertexTorusMaskSeamTransfer
        (sixVertexFullDisagreementMask omega eta) omega eta := by
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  have hzero : (∑ y : T.Vertex,
      sixVertexTorusEdgeSeamSign omega eta (0, y)) = 0 := by
    simp [sixVertexTorusEdgeSeamSign]
  rw [hzero, zero_add, Fintype.sum_prod_type]
  have hinner (i : Fin T.width) :
      (∑ j : Fin T.height,
        sixVertexTorusEdgeSeamSign omega eta (1, (i, j))) =
        (eta.vertical (i, svFinLast T.height_pos)).toNat -
          (omega.vertical (i, svFinLast T.height_pos)).toNat := by
    rw [Finset.sum_eq_single (svFinLast T.height_pos)]
    · simp [sixVertexTorusEdgeSeamSign]
    · intro j hj hne
      simp [sixVertexTorusEdgeSeamSign, hne]
    · simp
  simp_rw [hinner]
  unfold sixVertexTorusMaskSeamTransfer
  apply Finset.sum_congr rfl
  intro i hi
  cases ho : omega.vertical (i, svFinLast T.height_pos) <;>
    cases he : eta.vertical (i, svFinLast T.height_pos) <;>
    simp [sixVertexFullDisagreementMask, ho, he]


def sixVertexDegreeTwoStrandStepSeamSign
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexOrientedDisagreementDart omega eta) : Int :=
  sixVertexTorusEdgeSeamSign omega eta
    (sixVertexTorusDartEdge T
      (sixVertexDegreeTwoLocalMate hdegree d.1).1)

theorem sixVertexDegreeTwoStrandStepSeamSign_of_ne_zero
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexOrientedDisagreementDart omega eta)
    (hne : sixVertexDegreeTwoStrandStepSeamSign hdegree d ≠ 0) :
    sixVertexDegreeTwoStrandStepSeamSign hdegree d = 1 ∨
      sixVertexDegreeTwoStrandStepSeamSign hdegree d = -1 := by
  rcases sixVertexTorusEdgeSeamSign_eq_zero_or_one_or_neg_one
    omega eta
    (sixVertexTorusDartEdge T
      (sixVertexDegreeTwoLocalMate hdegree d.1).1) with hzero | hone | hneg
  · exact False.elim (hne hzero)
  · exact Or.inl hone
  · exact Or.inr hneg



theorem sum_sixVertexDegreeTwoStrandStepSeamSign_eq_edges
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    (∑ d : SixVertexOrientedDisagreementDart omega eta,
        sixVertexDegreeTwoStrandStepSeamSign hdegree d) =
      ∑ e : SixVertexDisagreementEdge omega eta,
        sixVertexTorusEdgeSeamSign omega eta e.1 := by
  let edgeEquiv := sixVertexOrientedDisagreementDartEquivEdge
    homega heta hdegree
  calc
    (∑ d : SixVertexOrientedDisagreementDart omega eta,
        sixVertexDegreeTwoStrandStepSeamSign hdegree d) =
        ∑ d : SixVertexOrientedDisagreementDart omega eta,
          sixVertexTorusEdgeSeamSign omega eta (edgeEquiv d).1 := by
      apply Finset.sum_congr rfl
      intro d hd
      rfl
    _ = ∑ e : SixVertexDisagreementEdge omega eta,
          sixVertexTorusEdgeSeamSign omega eta e.1 :=
      edgeEquiv.sum_comp
        (fun e => sixVertexTorusEdgeSeamSign omega eta e.1)



theorem sum_sixVertexDegreeTwoStrandStepSeamSign_eq_fullTransfer
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    (∑ d : SixVertexOrientedDisagreementDart omega eta,
        sixVertexDegreeTwoStrandStepSeamSign hdegree d) =
      sixVertexTorusMaskSeamTransfer
        (sixVertexFullDisagreementMask omega eta) omega eta := by
  rw [sum_sixVertexDegreeTwoStrandStepSeamSign_eq_edges
      homega heta hdegree,
    sum_sixVertexDisagreementEdge_seamSign,
    sum_sixVertexTorusEdge_seamSign_eq_fullTransfer]



theorem sum_sixVertexDegreeTwoStrandStepSeamSign_eq_two
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n) :
    (∑ d : SixVertexOrientedDisagreementDart omega eta,
        sixVertexDegreeTwoStrandStepSeamSign hdegree d) = 2 := by
  rw [sum_sixVertexDegreeTwoStrandStepSeamSign_eq_fullTransfer
    homega heta hdegree]
  exact sixVertexFullDisagreementMask_seamTransfer_eq_two
    omega eta n homegaSector hetaSector hn



noncomputable def permCycleFinEquivSupport
    {D : Type*} [Fintype D] [DecidableEq D]
    (cycle : Equiv.Perm D) (hcycle : cycle.IsCycle)
    (seed : cycle.support) : Fin (orderOf cycle) ≃ cycle.support := by
  let forward : Fin (orderOf cycle) → cycle.support := fun k =>
    ⟨(cycle ^ k.val) seed.1,
      Equiv.Perm.pow_apply_mem_support.mpr seed.2⟩
  apply Equiv.ofBijective forward
  apply (Fintype.bijective_iff_surjective_and_card forward).mpr
  constructor
  · intro target
    have hsame := hcycle.sameCycle
      (Equiv.Perm.mem_support.mp seed.2)
      (Equiv.Perm.mem_support.mp target.2)
    obtain ⟨k, hk⟩ := hsame.exists_fin_pow_eq
    exact ⟨k, Subtype.ext hk⟩
  · simp only [Fintype.card_fin, Fintype.card_coe, hcycle.orderOf]



noncomputable def permOrderedCycleFactor
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma cycle : Equiv.Perm D)
    (hcycle : cycle ∈ sigma.cycleFactorsFinset) : List D :=
  let hc : cycle.IsCycle :=
    (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hcycle).1
  let hs : cycle.support.Nonempty := hc.nonempty_support
  let seed : cycle.support :=
    ⟨Classical.choose hs, Classical.choose_spec hs⟩
  List.ofFn fun k => (permCycleFinEquivSupport cycle hc seed k).1

theorem sum_map_permOrderedCycleFactor
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma cycle : Equiv.Perm D)
    (hcycle : cycle ∈ sigma.cycleFactorsFinset) (f : D → Int) :
    ((permOrderedCycleFactor sigma cycle hcycle).map f).sum =
      ∑ d ∈ cycle.support, f d := by
  let hc : cycle.IsCycle :=
    (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hcycle).1
  let hs : cycle.support.Nonempty := hc.nonempty_support
  let seed : cycle.support :=
    ⟨Classical.choose hs, Classical.choose_spec hs⟩
  let enumerate := permCycleFinEquivSupport cycle hc seed
  rw [show permOrderedCycleFactor sigma cycle hcycle =
      List.ofFn (fun k => (enumerate k).1) by rfl]
  rw [List.map_ofFn, List.sum_ofFn]
  change (∑ k, f (enumerate k).1) = _
  rw [enumerate.sum_comp (fun d => f d.1)]
  exact Finset.sum_coe_sort cycle.support f

theorem sum_map_list_flatMap
    {A B : Type*} (items : List A) (pieces : A → List B)
    (f : B → Int) :
    ((items.flatMap pieces).map f).sum =
      (items.map fun a => ((pieces a).map f).sum).sum := by
  induction items with
  | nil => simp
  | cons a items ih => simp [ih]

theorem sum_map_finset_toList
    {A : Type*} (items : Finset A) (f : A → Int) :
    (items.toList.map f).sum = ∑ a ∈ items, f a := by
  classical
  induction items using Finset.induction with
  | empty => simp
  | @insert a items ha ih => simp [ha]



noncomputable def permOrderedAllCycles
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) : List D :=
  sigma.cycleFactorsFinset.toList.flatMap fun cycle =>
    if hcycle : cycle ∈ sigma.cycleFactorsFinset then
      permOrderedCycleFactor sigma cycle hcycle
    else []

set_option maxHeartbeats 800000 in

theorem sum_map_permOrderedAllCycles
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (hsupport : sigma.support = Finset.univ)
    (f : D → Int) :
    ((permOrderedAllCycles sigma).map f).sum = ∑ d, f d := by
  classical
  unfold permOrderedAllCycles
  rw [sum_map_list_flatMap, sum_map_finset_toList]
  have hone : (∑ cycle ∈ sigma.cycleFactorsFinset,
      ((if hcycle : cycle ∈ sigma.cycleFactorsFinset then
          permOrderedCycleFactor sigma cycle hcycle else []).map f).sum) =
      ∑ cycle ∈ sigma.cycleFactorsFinset,
        ∑ d ∈ cycle.support, f d := by
    apply Finset.sum_congr rfl
    intro cycle hcycle
    rw [dif_pos hcycle, sum_map_permOrderedCycleFactor]
  rw [hone]
  have hdisjoint :
      (↑sigma.cycleFactorsFinset : Set (Equiv.Perm D)).PairwiseDisjoint
        (fun cycle => cycle.support) := by
    intro c hc d hd hcd
    exact (sigma.cycleFactorsFinset_pairwise_disjoint
      hc hd hcd).disjoint_support
  have hunion : sigma.cycleFactorsFinset.biUnion
      (fun cycle => cycle.support) = Finset.univ := by
    ext d
    rw [Finset.mem_biUnion]
    simp only [Finset.mem_univ, iff_true]
    rw [← Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset,
      hsupport]
    simp
  rw [← Finset.sum_biUnion hdisjoint, hunion]


noncomputable def sixVertexDegreeTwoOrderedAllStrands
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    List (SixVertexOrientedDisagreementDart omega eta) :=
  permOrderedAllCycles
    (sixVertexOrientedDegreeTwoStrandSuccessor homega heta hdegree)

theorem sum_map_sixVertexDegreeTwoOrderedAllStrands
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (f : SixVertexOrientedDisagreementDart omega eta → Int) :
    ((sixVertexDegreeTwoOrderedAllStrands
      homega heta hdegree).map f).sum = ∑ d, f d :=
  sum_map_permOrderedAllCycles
    (sixVertexOrientedDegreeTwoStrandSuccessor homega heta hdegree)
    (sixVertexOrientedDegreeTwoStrandSuccessor_support
      homega heta hdegree) f

def intKeepNonzero (z : Int) : Bool :=
  if z = 0 then false else true

theorem ne_zero_of_intKeepNonzero (z : Int)
    (h : intKeepNonzero z = true) : z ≠ 0 := by
  intro hz
  simp [intKeepNonzero, hz] at h

theorem sum_filter_intKeepNonzero (steps : List Int) :
    (steps.filter intKeepNonzero).sum = steps.sum := by
  induction steps with
  | nil => simp
  | cons step steps ih =>
      by_cases hstep : step = 0 <;>
        simp [intKeepNonzero, hstep, ih]


noncomputable def sixVertexDegreeTwoAllStrandsSeamWord
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) : List Int :=
  ((sixVertexDegreeTwoOrderedAllStrands homega heta hdegree).map
      (sixVertexDegreeTwoStrandStepSeamSign hdegree)).filter
    intKeepNonzero

theorem sixVertexDegreeTwoAllStrandsSeamWord_unitSteps
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    ∀ z ∈ sixVertexDegreeTwoAllStrandsSeamWord
        homega heta hdegree,
      z = 1 ∨ z = -1 := by
  intro z hz
  simp only [sixVertexDegreeTwoAllStrandsSeamWord,
    List.mem_filter, List.mem_map] at hz
  obtain ⟨⟨d, hd, rfl⟩, hne⟩ := hz
  exact sixVertexDegreeTwoStrandStepSeamSign_of_ne_zero hdegree d
    (ne_zero_of_intKeepNonzero _ hne)



theorem sixVertexDegreeTwoAllStrandsSeamWord_sum_eq_two
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n) :
    (sixVertexDegreeTwoAllStrandsSeamWord
      homega heta hdegree).sum = 2 := by
  unfold sixVertexDegreeTwoAllStrandsSeamWord
  rw [sum_filter_intKeepNonzero,
    sum_map_sixVertexDegreeTwoOrderedAllStrands]
  exact sum_sixVertexDegreeTwoStrandStepSeamSign_eq_two
    homega heta hdegree n homegaSector hetaSector hn

local instance sixVertexDegreeTwoSameCycleDecidable
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    DecidableRel
      (sixVertexOrientedDegreeTwoStrandSuccessor
        homega heta hdegree).SameCycle :=
  Classical.decRel _


noncomputable def sixVertexDegreeTwoOrderedStrand
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    List (SixVertexOrientedDisagreementDart omega eta) :=
  let sigma := sixVertexOrientedDegreeTwoStrandSuccessor
    homega heta hdegree
  let cycle := sigma.cycleOf seed
  List.ofFn fun k : Fin (orderOf cycle) => (sigma ^ k.val) seed


noncomputable def sixVertexDegreeTwoStrandSeamWord
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) : List Int :=
  ((sixVertexDegreeTwoOrderedStrand homega heta hdegree seed).map
      (sixVertexDegreeTwoStrandStepSeamSign hdegree)).filter
    fun z => z ≠ 0


theorem sixVertexDegreeTwoStrandSeamWord_unitSteps
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (seed : SixVertexOrientedDisagreementDart omega eta) :
    ∀ z ∈ sixVertexDegreeTwoStrandSeamWord
        homega heta hdegree seed,
      z = 1 ∨ z = -1 := by
  intro z hz
  simp only [sixVertexDegreeTwoStrandSeamWord, List.mem_filter,
    List.mem_map] at hz
  obtain ⟨⟨d, hd, rfl⟩, hne⟩ := hz
  exact sixVertexDegreeTwoStrandStepSeamSign_of_ne_zero hdegree d
    (of_decide_eq_true hne)

end

end StatMech.FrontierD
