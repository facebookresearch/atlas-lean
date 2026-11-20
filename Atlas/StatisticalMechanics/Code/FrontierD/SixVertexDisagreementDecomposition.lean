/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexMarkedPairSwitchInterface
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected











open Finset

namespace StatMech.FrontierD

noncomputable section


abbrev SixVertexTorusEdge (T : EvenTorus) := Fin 2 × T.Vertex

def sixVertexTorusEdgeArrow
    {T : EvenTorus} (omega : SixVertexArrows T)
    (e : SixVertexTorusEdge T) : Bool :=
  if e.1 = 0 then omega.horizontal e.2 else omega.vertical e.2

def sixVertexTorusEdgeDisagrees
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (e : SixVertexTorusEdge T) : Prop :=
  sixVertexTorusEdgeArrow omega e ≠ sixVertexTorusEdgeArrow eta e


def sixVertexTorusIncidentEdge
    (T : EvenTorus) (v : T.Vertex) (d : Fin 4) : SixVertexTorusEdge T :=
  ![(0, (SixVertexArrows.cyclicPred T.width_pos v.1, v.2)),
    (0, v),
    (1, (v.1, SixVertexArrows.cyclicPred T.height_pos v.2)),
    (1, v)] d

theorem sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (v : T.Vertex) (d : Fin 4) :
    sixVertexLocalIncomingPattern omega v d ≠
        sixVertexLocalIncomingPattern eta v d ↔
      sixVertexTorusEdgeDisagrees omega eta
        (sixVertexTorusIncidentEdge T v d) := by
  fin_cases d <;>
    simp [sixVertexLocalIncomingPattern, sixVertexTorusIncidentEdge,
      sixVertexTorusEdgeDisagrees, sixVertexTorusEdgeArrow,
      fkLoopWestIncoming, fkLoopEastIncoming, fkLoopSouthIncoming,
      fkLoopNorthIncoming]




def sixVertexTorusDisagreementGraph
    {T : EvenTorus} (omega eta : SixVertexArrows T) :
    SimpleGraph (SixVertexTorusEdge T) where
  Adj e f := e ≠ f /\
    sixVertexTorusEdgeDisagrees omega eta e /\
    sixVertexTorusEdgeDisagrees omega eta f /\
    ∃ v d r, sixVertexTorusIncidentEdge T v d = e /\
      sixVertexTorusIncidentEdge T v r = f
  symm := by
    rintro e f ⟨hef, he, hf, v, d, r, hd, hr⟩
    exact ⟨hef.symm, hf, he, v, r, d, hr, hd⟩
  loopless := ⟨by
    intro e h
    exact h.1 rfl⟩



def sixVertexPositiveSeamDisagreements
    (T : EvenTorus) (omega eta : SixVertexArrows T) : Finset (Fin T.width) :=
  Finset.univ.filter fun i =>
    omega.vertical (i, svFinLast T.height_pos) = false /\
      eta.vertical (i, svFinLast T.height_pos) = true

theorem sixVertexPositiveSeamDisagreements_nonempty
    (T : EvenTorus) (omega eta : SixVertexArrows T) (n : Nat)
    (homega : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (heta : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n) :
    (sixVertexPositiveSeamDisagreements T omega eta).Nonempty := by
  classical
  let A : Finset (Fin T.width) :=
    Finset.univ.filter fun i => omega.vertical (i, svFinLast T.height_pos)
  let B : Finset (Fin T.width) :=
    Finset.univ.filter fun i => eta.vertical (i, svFinLast T.height_pos)
  have hA : A.card = n - 1 := by
    simpa [A, sixVertexUpCount, svTorusVerticalRows] using homega
  have hB : B.card = n + 1 := by
    simpa [B, sixVertexUpCount, svTorusVerticalRows] using heta
  have hcard : A.card < B.card := by omega
  obtain ⟨i, hiB, hiA⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hetaTrue : eta.vertical (i, svFinLast T.height_pos) = true := by
    simpa [B] using hiB
  have homegaFalse : omega.vertical (i, svFinLast T.height_pos) = false := by
    cases h : omega.vertical (i, svFinLast T.height_pos)
    · rfl
    · exact False.elim (hiA (by simp [A, h]))
  exact ⟨i, by
    simp [sixVertexPositiveSeamDisagreements, homegaFalse, hetaTrue]⟩


def sixVertexLexPositiveSeamSeed
    (T : EvenTorus) (omega eta : SixVertexArrows T)
    (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
    Fin T.width :=
  (sixVertexPositiveSeamDisagreements T omega eta).min' h

theorem sixVertexLexPositiveSeamSeed_mem
    (T : EvenTorus) (omega eta : SixVertexArrows T)
    (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
    sixVertexLexPositiveSeamSeed T omega eta h ∈
      sixVertexPositiveSeamDisagreements T omega eta :=
  Finset.min'_mem _ _


def sixVertexLexPositiveSeamEdge
    (T : EvenTorus) (omega eta : SixVertexArrows T)
    (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
    SixVertexTorusEdge T :=
  (1, (sixVertexLexPositiveSeamSeed T omega eta h,
    svFinLast T.height_pos))

theorem sixVertexLexPositiveSeamEdge_disagrees
    (T : EvenTorus) (omega eta : SixVertexArrows T)
    (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
    sixVertexTorusEdgeDisagrees omega eta
      (sixVertexLexPositiveSeamEdge T omega eta h) := by
  have hm := sixVertexLexPositiveSeamSeed_mem T omega eta h
  simp only [sixVertexPositiveSeamDisagreements, Finset.mem_filter,
    Finset.mem_univ, true_and] at hm
  simp [sixVertexLexPositiveSeamEdge, sixVertexTorusEdgeDisagrees,
    sixVertexTorusEdgeArrow, hm.1, hm.2]


noncomputable def sixVertexLexDisagreementComponentMask
    (T : EvenTorus) (omega eta : SixVertexArrows T)
    (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
    SixVertexArrows T := by
  classical
  let seed := sixVertexLexPositiveSeamEdge T omega eta h
  let G := sixVertexTorusDisagreementGraph omega eta
  exact
    { horizontal := fun v => decide (G.Reachable seed (0, v))
      vertical := fun v => decide (G.Reachable seed (1, v)) }

theorem sixVertexLexDisagreementComponentMask_seed
    (T : EvenTorus) (omega eta : SixVertexArrows T)
    (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
    (sixVertexLexDisagreementComponentMask T omega eta h).vertical
      (sixVertexLexPositiveSeamSeed T omega eta h,
        svFinLast T.height_pos) = true := by
  classical
  simp [sixVertexLexDisagreementComponentMask,
    sixVertexLexPositiveSeamEdge]



theorem sixVertexLocalDisagreementCount_eq_two_or_four
    (p q : SixVertexLocalIncomingPattern)
    (hp : p.Ice) (hq : q.Ice) (hne : p ≠ q) :
    (∑ d, if p d ≠ q d then 1 else 0) = 2 \/
      (∑ d, if p d ≠ q d then 1 else 0) = 4 := by
  decide +revert


def sixVertexTorusMaskSelects
    {T : EvenTorus} (mask : SixVertexArrows T)
    (e : SixVertexTorusEdge T) : Bool :=
  if e.1 = 0 then mask.horizontal e.2 else mask.vertical e.2

theorem sixVertexTorusLocalSwitchMask_apply
    {T : EvenTorus} (mask : SixVertexArrows T)
    (v : T.Vertex) (d : Fin 4) :
    sixVertexTorusLocalSwitchMask mask v d =
      sixVertexTorusMaskSelects mask (sixVertexTorusIncidentEdge T v d) := by
  fin_cases d <;>
    simp [sixVertexTorusLocalSwitchMask, sixVertexTorusMaskSelects,
      sixVertexTorusIncidentEdge]

theorem sixVertexLexDisagreementComponentMask_selects_iff
    (T : EvenTorus) (omega eta : SixVertexArrows T)
    (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty)
    (e : SixVertexTorusEdge T) :
    sixVertexTorusMaskSelects
        (sixVertexLexDisagreementComponentMask T omega eta h) e = true ↔
      (sixVertexTorusDisagreementGraph omega eta).Reachable
        (sixVertexLexPositiveSeamEdge T omega eta h) e := by
  classical
  rcases e with ⟨dir, v⟩
  fin_cases dir <;>
    simp [sixVertexTorusMaskSelects,
      sixVertexLexDisagreementComponentMask]

theorem sixVertexDisagreementGraph_reachable_disagrees
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {seed e : SixVertexTorusEdge T}
    (hseed : sixVertexTorusEdgeDisagrees omega eta seed)
    (hreach : (sixVertexTorusDisagreementGraph omega eta).Reachable seed e) :
    sixVertexTorusEdgeDisagrees omega eta e := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  induction hreach with
  | refl => exact hseed
  | tail hab hbc ih => exact hbc.2.2.1

theorem sixVertexLexDisagreementComponentMask_selects_only_disagreement
    (T : EvenTorus) (omega eta : SixVertexArrows T)
    (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty)
    (e : SixVertexTorusEdge T)
    (he : sixVertexTorusMaskSelects
      (sixVertexLexDisagreementComponentMask T omega eta h) e = true) :
    sixVertexTorusEdgeDisagrees omega eta e := by
  apply sixVertexDisagreementGraph_reachable_disagrees
    (sixVertexLexPositiveSeamEdge_disagrees T omega eta h)
  exact (sixVertexLexDisagreementComponentMask_selects_iff
    T omega eta h e).mp he

theorem sixVertexLexDisagreementComponentMask_incident_closure
    (T : EvenTorus) (omega eta : SixVertexArrows T)
    (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty)
    (v : T.Vertex) (d r : Fin 4)
    (hd : sixVertexTorusLocalSwitchMask
      (sixVertexLexDisagreementComponentMask T omega eta h) v d = true)
    (hr : sixVertexLocalIncomingPattern omega v r ≠
      sixVertexLocalIncomingPattern eta v r) :
    sixVertexTorusLocalSwitchMask
      (sixVertexLexDisagreementComponentMask T omega eta h) v r = true := by
  rw [sixVertexTorusLocalSwitchMask_apply] at hd ⊢
  rw [sixVertexLexDisagreementComponentMask_selects_iff] at hd ⊢
  by_cases hdr : sixVertexTorusIncidentEdge T v d =
      sixVertexTorusIncidentEdge T v r
  · simpa [hdr] using hd
  · apply hd.trans
    apply SimpleGraph.Adj.reachable
    refine ⟨hdr, ?_, ?_, v, d, r, rfl, rfl⟩
    · exact sixVertexLexDisagreementComponentMask_selects_only_disagreement
        T omega eta h _ (by
          rw [sixVertexLexDisagreementComponentMask_selects_iff]
          exact hd)
    · exact (sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
        omega eta v r).mp hr

theorem sixVertexLexDisagreementComponentMask_local_eq_disagreement
    (T : EvenTorus) (omega eta : SixVertexArrows T)
    (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty)
    (v : T.Vertex)
    (hactive : ∃ d, sixVertexTorusLocalSwitchMask
      (sixVertexLexDisagreementComponentMask T omega eta h) v d = true) :
    forall r,
      sixVertexTorusLocalSwitchMask
          (sixVertexLexDisagreementComponentMask T omega eta h) v r =
        decide (sixVertexLocalIncomingPattern omega v r ≠
          sixVertexLocalIncomingPattern eta v r) := by
  obtain ⟨d, hd⟩ := hactive
  intro r
  by_cases hr : sixVertexLocalIncomingPattern omega v r ≠
      sixVertexLocalIncomingPattern eta v r
  · rw [sixVertexLexDisagreementComponentMask_incident_closure
      T omega eta h v d r hd hr]
    simp [hr]
  · have hnotSelected : sixVertexTorusLocalSwitchMask
        (sixVertexLexDisagreementComponentMask T omega eta h) v r ≠ true := by
      intro hselected
      have hedge := sixVertexLexDisagreementComponentMask_selects_only_disagreement
        T omega eta h (sixVertexTorusIncidentEdge T v r) (by
          rw [← sixVertexTorusLocalSwitchMask_apply]
          exact hselected)
      exact hr ((sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
        omega eta v r).mpr hedge)
    cases hm : sixVertexTorusLocalSwitchMask
      (sixVertexLexDisagreementComponentMask T omega eta h) v r
    · simp [hr]
    · exact False.elim (hnotSelected hm)

theorem sixVertexLexDisagreementComponentMask_local_route_size
    (T : EvenTorus) (omega eta : SixVertexArrows T)
    (homega : omega.IceRule) (heta : eta.IceRule)
    (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty)
    (v : T.Vertex) :
    sixVertexLocalSwitchMaskCount
        (sixVertexTorusLocalSwitchMask
          (sixVertexLexDisagreementComponentMask T omega eta h) v) = 0 \/
      sixVertexLocalSwitchMaskCount
          (sixVertexTorusLocalSwitchMask
            (sixVertexLexDisagreementComponentMask T omega eta h) v) = 2 \/
      sixVertexLocalSwitchMaskCount
          (sixVertexTorusLocalSwitchMask
            (sixVertexLexDisagreementComponentMask T omega eta h) v) = 4 := by
  by_cases hactive : ∃ d, sixVertexTorusLocalSwitchMask
      (sixVertexLexDisagreementComponentMask T omega eta h) v d = true
  · have hmask := sixVertexLexDisagreementComponentMask_local_eq_disagreement
      T omega eta h v hactive
    have hp := sixVertexLocalIncomingPattern_ice omega homega v
    have hq := sixVertexLocalIncomingPattern_ice eta heta v
    have hne : sixVertexLocalIncomingPattern omega v ≠
        sixVertexLocalIncomingPattern eta v := by
      obtain ⟨d, hd⟩ := hactive
      intro heq
      have hedge := sixVertexLexDisagreementComponentMask_selects_only_disagreement
        T omega eta h (sixVertexTorusIncidentEdge T v d) (by
          rw [← sixVertexTorusLocalSwitchMask_apply]
          exact hd)
      exact ((sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees
        omega eta v d).mpr hedge) (congrFun heq d)
    have hcount := sixVertexLocalDisagreementCount_eq_two_or_four
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v) hp hq hne
    have hsum :
        (∑ d, (sixVertexTorusLocalSwitchMask
          (sixVertexLexDisagreementComponentMask T omega eta h) v d).toNat) =
        ∑ d, if sixVertexLocalIncomingPattern omega v d ≠
            sixVertexLocalIncomingPattern eta v d then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [hmask d]
      by_cases hdiff : sixVertexLocalIncomingPattern omega v d ≠
          sixVertexLocalIncomingPattern eta v d <;> simp [hdiff]
    right
    unfold sixVertexLocalSwitchMaskCount
    rw [hsum]
    exact hcount
  · left
    unfold sixVertexLocalSwitchMaskCount
    apply Finset.sum_eq_zero
    intro d hd
    have hfalse : sixVertexTorusLocalSwitchMask
        (sixVertexLexDisagreementComponentMask T omega eta h) v d = false := by
      cases hm : sixVertexTorusLocalSwitchMask
        (sixVertexLexDisagreementComponentMask T omega eta h) v d
      · rfl
      · exact False.elim (hactive ⟨d, hm⟩)
    simp [hfalse]

theorem sixVertexLocalSwapMask_eq_pair_of_disagreementMask
    (p q mask : SixVertexLocalIncomingPattern)
    (hmask : forall d, mask d = decide (p d ≠ q d)) :
    sixVertexLocalSwapMask p q mask = (q, p) := by
  apply Prod.ext <;> funext d <;>
    by_cases h : p d = q d <;>
      simp [sixVertexLocalSwapMask, hmask, h]

theorem sixVertexLexDisagreementComponentSwitch_ice
    (T : EvenTorus) (omega eta : SixVertexArrows T)
    (homega : omega.IceRule) (heta : eta.IceRule)
    (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
    (sixVertexTorusSwitchFirst
      (sixVertexLexDisagreementComponentMask T omega eta h)
      omega eta).IceRule /\
    (sixVertexTorusSwitchSecond
      (sixVertexLexDisagreementComponentMask T omega eta h)
      omega eta).IceRule := by
  constructor <;> intro v
  · rw [← sixVertexLocalIncomingPattern_count]
    have hpair := sixVertexTorusLocalIncomingPattern_pairSwitch
      (sixVertexLexDisagreementComponentMask T omega eta h) omega eta v
    have hfirst := congrArg Prod.fst hpair
    change sixVertexLocalIncomingPattern
      (sixVertexTorusSwitchFirst
        (sixVertexLexDisagreementComponentMask T omega eta h) omega eta) v =
      (sixVertexLocalSwapMask (sixVertexLocalIncomingPattern omega v)
        (sixVertexLocalIncomingPattern eta v)
        (sixVertexTorusLocalSwitchMask
          (sixVertexLexDisagreementComponentMask T omega eta h) v)).1 at hfirst
    rw [hfirst]
    by_cases hactive : ∃ d, sixVertexTorusLocalSwitchMask
        (sixVertexLexDisagreementComponentMask T omega eta h) v d = true
    · rw [sixVertexLocalSwapMask_eq_pair_of_disagreementMask _ _ _
        (sixVertexLexDisagreementComponentMask_local_eq_disagreement
          T omega eta h v hactive)]
      exact sixVertexLocalIncomingPattern_ice eta heta v
    · have hzero : sixVertexTorusLocalSwitchMask
          (sixVertexLexDisagreementComponentMask T omega eta h) v =
          fun _ => false := by
        funext d
        cases hm : sixVertexTorusLocalSwitchMask
          (sixVertexLexDisagreementComponentMask T omega eta h) v d
        · rfl
        · exact False.elim (hactive ⟨d, hm⟩)
      simpa [sixVertexLocalSwapMask, hzero] using
        (sixVertexLocalIncomingPattern_ice omega homega v)
  · rw [← sixVertexLocalIncomingPattern_count]
    have hpair := sixVertexTorusLocalIncomingPattern_pairSwitch
      (sixVertexLexDisagreementComponentMask T omega eta h) omega eta v
    have hsecond := congrArg Prod.snd hpair
    change sixVertexLocalIncomingPattern
      (sixVertexTorusSwitchSecond
        (sixVertexLexDisagreementComponentMask T omega eta h) omega eta) v =
      (sixVertexLocalSwapMask (sixVertexLocalIncomingPattern omega v)
        (sixVertexLocalIncomingPattern eta v)
        (sixVertexTorusLocalSwitchMask
          (sixVertexLexDisagreementComponentMask T omega eta h) v)).2 at hsecond
    rw [hsecond]
    by_cases hactive : ∃ d, sixVertexTorusLocalSwitchMask
        (sixVertexLexDisagreementComponentMask T omega eta h) v d = true
    · rw [sixVertexLocalSwapMask_eq_pair_of_disagreementMask _ _ _
        (sixVertexLexDisagreementComponentMask_local_eq_disagreement
          T omega eta h v hactive)]
      exact sixVertexLocalIncomingPattern_ice omega homega v
    · have hzero : sixVertexTorusLocalSwitchMask
          (sixVertexLexDisagreementComponentMask T omega eta h) v =
          fun _ => false := by
        funext d
        cases hm : sixVertexTorusLocalSwitchMask
          (sixVertexLexDisagreementComponentMask T omega eta h) v d
        · rfl
        · exact False.elim (hactive ⟨d, hm⟩)
      simpa [sixVertexLocalSwapMask, hzero] using
        (sixVertexLocalIncomingPattern_ice eta heta v)



theorem sixVertexTorusEdgeDisagrees_pairSwitch_iff
    {T : EvenTorus} (mask omega eta : SixVertexArrows T)
    (e : SixVertexTorusEdge T) :
    sixVertexTorusEdgeDisagrees
        (sixVertexTorusSwitchFirst mask omega eta)
        (sixVertexTorusSwitchSecond mask omega eta) e ↔
      sixVertexTorusEdgeDisagrees omega eta e := by
  rcases e with ⟨dir, v⟩
  fin_cases dir
  · by_cases hmask : mask.horizontal v = true <;>
      simp [sixVertexTorusEdgeDisagrees, sixVertexTorusEdgeArrow,
        sixVertexTorusSwitchFirst, sixVertexTorusSwitchSecond,
        hmask, ne_comm]
  · by_cases hmask : mask.vertical v = true <;>
      simp [sixVertexTorusEdgeDisagrees, sixVertexTorusEdgeArrow,
        sixVertexTorusSwitchFirst, sixVertexTorusSwitchSecond,
        hmask, ne_comm]



theorem sixVertexTorusDisagreementGraph_pairSwitch
    {T : EvenTorus} (mask omega eta : SixVertexArrows T) :
    sixVertexTorusDisagreementGraph
        (sixVertexTorusSwitchFirst mask omega eta)
        (sixVertexTorusSwitchSecond mask omega eta) =
      sixVertexTorusDisagreementGraph omega eta := by
  ext e f
  simp only [sixVertexTorusDisagreementGraph]
  rw [sixVertexTorusEdgeDisagrees_pairSwitch_iff,
    sixVertexTorusEdgeDisagrees_pairSwitch_iff]

end

end StatMech.FrontierD
