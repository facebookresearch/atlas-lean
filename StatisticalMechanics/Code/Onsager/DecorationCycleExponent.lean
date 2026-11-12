/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationLoopClassification
import Mathlib.Combinatorics.SimpleGraph.Acyclic









namespace StatMech.Onsager

open Finset SimpleGraph

theorem ons_portLine_isTree : (SimpleGraph.pathGraph 4).IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  constructor
  · simpa using SimpleGraph.pathGraph_connected 3
  · rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
      Nat.card_eq_fintype_card]
    have hedges : (SimpleGraph.pathGraph 4).edgeFinset =
        {s((0 : Fin 4), (1 : Fin 4)), s((1 : Fin 4), (2 : Fin 4)),
          s((2 : Fin 4), (3 : Fin 4))} := by
      ext edge
      induction edge using Sym2.inductionOn with
      | _ u v =>
          fin_cases u <;> fin_cases v <;>
            simp [SimpleGraph.mem_edgeFinset,
              SimpleGraph.pathGraph_adj, Sym2.eq_iff]
    rw [hedges]
    decide



theorem ons_internalPath_unique
    {L : ℕ} (site : ZMod L × ZMod L) (a b : Fin 4)
    (p q : (ons_decGraph L).Walk (site, a) (site, b))
    (hpint : ∀ d ∈ p.darts, ons_decInternalAdj d.fst d.snd)
    (hqint : ∀ d ∈ q.darts, ons_decInternalAdj d.fst d.snd)
    (hp : p.IsPath) (hq : q.IsPath) :
    p = q := by
  let pp := p.support.map (fun x ↦ x.2)
  let qq := q.support.map (fun x ↦ x.2)
  have hppne : pp ≠ [] := by simp [pp]
  have hqqne : qq ≠ [] := by simp [qq]
  have hppchain : List.IsChain (SimpleGraph.pathGraph 4).Adj pp := by
    apply (ons_support_directions_isChain_portLine p hpint).imp
    intro x y hxy
    rw [SimpleGraph.pathGraph_adj]
    exact hxy
  have hqqchain : List.IsChain (SimpleGraph.pathGraph 4).Adj qq := by
    apply (ons_support_directions_isChain_portLine q hqint).imp
    intro x y hxy
    rw [SimpleGraph.pathGraph_adj]
    exact hxy
  have hpsite := ons_internalWalk_support_site p hpint
  have hqsite := ons_internalWalk_support_site q hqint
  have hppnodup : pp.Nodup := by
    apply hp.support_nodup.map_on
    intro x hx y hy hxy
    apply Prod.ext
    · exact (hpsite x hx).trans (hpsite y hy).symm
    · exact hxy
  have hqqnodup : qq.Nodup := by
    apply hq.support_nodup.map_on
    intro x hx y hy hxy
    apply Prod.ext
    · exact (hqsite x hx).trans (hqsite y hy).symm
    · exact hxy
  let ppWalk : (SimpleGraph.pathGraph 4).Walk a b :=
    (SimpleGraph.Walk.ofSupport pp hppne hppchain).copy
      (by simp [pp]) (by simp [pp])
  let qqWalk : (SimpleGraph.pathGraph 4).Walk a b :=
    (SimpleGraph.Walk.ofSupport qq hqqne hqqchain).copy
      (by simp [qq]) (by simp [qq])
  have hppath : ppWalk.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simpa [ppWalk] using hppnodup
  have hqpath : qqWalk.IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simpa [qqWalk] using hqqnodup
  have hwalk : ppWalk = qqWalk := by
    exact congrArg Subtype.val
      (ons_portLine_isTree.isAcyclic.path_unique
        ⟨ppWalk, hppath⟩ ⟨qqWalk, hqpath⟩)
  have hports : pp = qq := by
    have hs := congrArg SimpleGraph.Walk.support hwalk
    simpa [ppWalk, qqWalk] using hs
  apply SimpleGraph.Walk.ext_support
  calc
    p.support = pp.map (fun mu ↦ (site, mu)) := by
      change p.support =
        (p.support.map (fun x ↦ x.2)).map (fun mu ↦ (site, mu))
      rw [List.map_map]
      symm
      calc
        p.support.map (fun x ↦ (site, x.2)) =
            p.support.map id := by
          apply List.map_congr_left
          intro x hx
          apply Prod.ext
          · exact (hpsite x hx).symm
          · rfl
        _ = p.support := List.map_id _
    _ = qq.map (fun mu ↦ (site, mu)) := by rw [hports]
    _ = q.support := by
      change (q.support.map (fun x ↦ x.2)).map
          (fun mu ↦ (site, mu)) = q.support
      rw [List.map_map]
      calc
        q.support.map (fun x ↦ (site, x.2)) =
            q.support.map id := by
          apply List.map_congr_left
          intro x hx
          apply Prod.ext
          · exact (hqsite x hx).symm
          · rfl
        _ = q.support := List.map_id _

theorem ons_decPortChainPath_internal
    (L : ℕ) [Fact (2 < L)] (site : ZMod L × ZMod L)
    (a b : Fin 4) :
    ∀ d ∈ (ons_decPortChainPath L site a b).darts,
      ons_decInternalAdj d.fst d.snd := by
  intro d hd
  have hadj := d.adj
  change ons_decAdj L d.fst d.snd at hadj
  rcases hadj with hext | hint
  · have hdmem : d.fst ∈
        ons_decWalkExternalDarts (ons_decPortChainPath L site a b) := by
      unfold ons_decWalkExternalDarts
      apply List.mem_map.mpr
      refine ⟨d, List.mem_filter.mpr ⟨hd, ?_⟩, rfl⟩
      simpa [ons_decDartIsExternal] using hext
    rw [ons_decPortChainPath_externalDarts_eq_nil] at hdmem
    exact (by simpa using hdmem : False).elim
  · exact hint



theorem ons_internalPath_eq_decPortChainPath
    (L : ℕ) [Fact (2 < L)] (source target : ons_Dart L)
    (hstep : target.1 = ons_dirStep L source.2 source.1)
    (p : (ons_decGraph L).Walk (ons_dartRev L source) target)
    (hpint : ∀ d ∈ p.darts, ons_decInternalAdj d.fst d.snd)
    (hp : p.IsPath) :
    p = (ons_decPortChainPath L target.1 (source.2 + 2) target.2).copy
      (by
        apply Prod.ext
        · exact hstep.trans (ons_dartRev_fst_eq_step L source).symm
        · simp [ons_dartRev]) rfl := by
  have hstart : (target.1, source.2 + 2) = ons_dartRev L source := by
    apply Prod.ext
    · exact hstep.trans (ons_dartRev_fst_eq_step L source).symm
    · simp [ons_dartRev]
  let chain := ons_decPortChainPath L target.1 (source.2 + 2) target.2
  let p' : (ons_decGraph L).Walk
      (target.1, source.2 + 2) target := p.copy hstart.symm rfl
  have hp'int : ∀ d ∈ p'.darts,
      ons_decInternalAdj d.fst d.snd := by
    intro d hd
    apply hpint d
    simpa [p'] using hd
  have hp' : p'.IsPath := by
    exact (SimpleGraph.Walk.isPath_copy p hstart.symm rfl).mpr hp
  have heq : p' = chain :=
    ons_internalPath_unique target.1 (source.2 + 2) target.2
      p' chain hp'int
      (ons_decPortChainPath_internal L target.1
        (source.2 + 2) target.2)
      hp' (ons_decPortChainPath_isPath L target.1
        (source.2 + 2) target.2)
  apply SimpleGraph.Walk.ext_support
  have hs := congrArg SimpleGraph.Walk.support heq
  simpa [p', chain] using hs

def ons_decExternalStepWalk (L : ℕ) (d : ons_Dart L) :
    (ons_decGraph L).Walk d (ons_dartRev L d) :=
  .cons (Or.inl rfl) .nil

theorem ons_decWalkOfKWChain_edges_congr
    (L : ℕ) (current : ons_Dart L)
    (tail tail' : List (ons_Dart L))
    (htail : tail = tail')
    (hchain : List.IsChain (ons_decGeometricStep L) (current :: tail))
    (hchain' : List.IsChain (ons_decGeometricStep L) (current :: tail')) :
    (ons_decWalkOfKWChain L current tail hchain).edges =
      (ons_decWalkOfKWChain L current tail' hchain').edges := by
  subst tail'
  rfl

theorem ons_decWalkOfKWChain_edges_congr_root
    (L : ℕ) (current current' : ons_Dart L)
    (tail tail' : List (ons_Dart L))
    (hcurrent : current = current') (htail : tail = tail')
    (hchain : List.IsChain (ons_decGeometricStep L) (current :: tail))
    (hchain' : List.IsChain (ons_decGeometricStep L) (current' :: tail')) :
    (ons_decWalkOfKWChain L current tail hchain).edges =
      (ons_decWalkOfKWChain L current' tail' hchain').edges := by
  subst current'
  subst tail'
  rfl



theorem ons_decWalkOfKWChain_rebuild
    (L : ℕ) [Fact (2 < L)] (current : ons_Dart L)
    {u finish : ons_Dart L}
    (r : (ons_decGraph L).Walk (ons_dartRev L current) u)
    (p : (ons_decGraph L).Walk u finish)
    (hrint : ∀ d ∈ r.darts, ons_decInternalAdj d.fst d.snd)
    (hrpath : r.IsPath)
    (hallpath : (r.append p).IsPath)
    (hchain : List.IsChain (ons_decGeometricStep L)
      (current :: (ons_decWalkExternalDarts p ++ [finish]))) :
    ((ons_decExternalStepWalk L current).append (r.append p)).edges =
      (ons_decWalkOfKWChain L current
        (ons_decWalkExternalDarts p ++ [finish]) hchain).edges := by
  induction p generalizing current with
  | @nil endpoint =>
      have hstep : endpoint.1 =
          ons_dirStep L current.2 current.1 := hchain.rel
      have hrEq := ons_internalPath_eq_decPortChainPath
        L current endpoint hstep r hrint hrpath
      simp only [ons_decWalkExternalDarts,
        SimpleGraph.Walk.darts_nil, List.filter_nil, List.map_nil,
        List.nil_append] at hchain ⊢
      rw [hrEq]
      simp only [ons_decWalkOfKWChain]
      unfold ons_decTransitionWalk ons_decExternalStepWalk
      simp only [SimpleGraph.Walk.edges_append,
        SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_cons,
        SimpleGraph.Walk.edges_nil, List.append_nil]
      change _ = _ ++ ([] : List (ons_DecEdge L))
      rw [List.append_nil]
  | @cons u w finish huw p ih =>
      by_cases hrev : w = ons_dartRev L u
      · subst w
        have hext : ons_decWalkExternalDarts
            (SimpleGraph.Walk.cons huw p) =
              u :: ons_decWalkExternalDarts p :=
          ons_decWalkExternalDarts_cons_external huw p rfl
        have hchain' : List.IsChain (ons_decGeometricStep L)
            (current :: u ::
              (ons_decWalkExternalDarts p ++ [finish])) := by
          simpa only [hext] using hchain
        have hstep : u.1 =
            ons_dirStep L current.2 current.1 := hchain'.rel
        have hrEq := ons_internalPath_eq_decPortChainPath
          L current u hstep r hrint hrpath
        have hdecomp : r.append
              (SimpleGraph.Walk.cons huw p) =
            (r.append (ons_decExternalStepWalk L u)).append p := by
          calc
            r.append (SimpleGraph.Walk.cons huw p) =
                (r.concat huw).append p :=
              (SimpleGraph.Walk.concat_append r huw p).symm
            _ = (r.append (ons_decExternalStepWalk L u)).append p := rfl
        have hppath : p.IsPath := by
          apply SimpleGraph.Walk.isPath_of_isSubwalk
            (SimpleGraph.Walk.isSubwalk_of_append_right hdecomp)
            hallpath
        have hrest := ih u (.nil)
          (by simp) (.nil) (by simpa using hppath) hchain'.tail
        have hrestEdges :
            (ons_decExternalStepWalk L u).edges ++ p.edges =
              (ons_decWalkOfKWChain L u
                (ons_decWalkExternalDarts p ++ [finish])
                hchain'.tail).edges := by
          simpa only [SimpleGraph.Walk.nil_append,
            SimpleGraph.Walk.edges_append] using hrest
        have htransition :
            (ons_decExternalStepWalk L current).edges ++ r.edges =
              (ons_decTransitionWalk L u current hstep).edges := by
          rw [hrEq]
          unfold ons_decExternalStepWalk ons_decTransitionWalk
          simp only [SimpleGraph.Walk.edges_append,
            SimpleGraph.Walk.edges_copy]
        have hmain :
            ((ons_decExternalStepWalk L current).append
              (r.append (SimpleGraph.Walk.cons huw p))).edges =
            ((ons_decTransitionWalk L u current hstep).append
              (ons_decWalkOfKWChain L u
                (ons_decWalkExternalDarts p ++ [finish])
                hchain'.tail)).edges := by
          rw [hdecomp]
          simp only [SimpleGraph.Walk.edges_append]
          calc
            (ons_decExternalStepWalk L current).edges ++
                ((r.edges ++ (ons_decExternalStepWalk L u).edges) ++
                  p.edges) =
                ((ons_decExternalStepWalk L current).edges ++ r.edges) ++
                  ((ons_decExternalStepWalk L u).edges ++ p.edges) := by
              simp only [List.append_assoc]
            _ = (ons_decTransitionWalk L u current hstep).edges ++
                  (ons_decWalkOfKWChain L u
                    (ons_decWalkExternalDarts p ++ [finish])
                    hchain'.tail).edges := by
              rw [htransition, hrestEdges]
        calc
          ((ons_decExternalStepWalk L current).append
              (r.append (SimpleGraph.Walk.cons huw p))).edges =
              (ons_decWalkOfKWChain L current
                (u :: (ons_decWalkExternalDarts p ++ [finish]))
                hchain').edges := hmain
          _ = (ons_decWalkOfKWChain L current
                (ons_decWalkExternalDarts
                    (SimpleGraph.Walk.cons huw p) ++ [finish])
                hchain).edges :=
            ons_decWalkOfKWChain_edges_congr L current _ _
              (by simp [hext]) hchain' hchain
      · have huwint : ons_decInternalAdj u w := by
          change ons_decAdj L u w at huw
          exact huw.resolve_left hrev
        have hext : ons_decWalkExternalDarts
            (SimpleGraph.Walk.cons huw p) =
              ons_decWalkExternalDarts p := by
          unfold ons_decWalkExternalDarts
          simp [ons_decDartIsExternal, hrev]
        have hchain' : List.IsChain (ons_decGeometricStep L)
            (current :: (ons_decWalkExternalDarts p ++ [finish])) := by
          simpa only [hext] using hchain
        let r' := r.concat huw
        have hr'int : ∀ d ∈ r'.darts,
            ons_decInternalAdj d.fst d.snd := by
          intro d hd
          change d ∈ (r.concat huw).darts at hd
          simp only [SimpleGraph.Walk.darts_concat] at hd
          simp at hd
          rcases hd with hd | rfl
          · exact hrint d hd
          · exact huwint
        have hr'allpath : (r'.append p).IsPath := by
          change ((r.concat huw).append p).IsPath
          rw [SimpleGraph.Walk.concat_append]
          exact hallpath
        have hr'path : r'.IsPath := hr'allpath.of_append_left
        have hrest := ih current r' hr'int hr'path hr'allpath
          hchain'
        have hmain :
            ((ons_decExternalStepWalk L current).append
              (r.append (SimpleGraph.Walk.cons huw p))).edges =
            (ons_decWalkOfKWChain L current
              (ons_decWalkExternalDarts p ++ [finish]) hchain').edges := by
          simpa only [r', SimpleGraph.Walk.concat_append] using hrest
        calc
          ((ons_decExternalStepWalk L current).append
              (r.append (SimpleGraph.Walk.cons huw p))).edges =
              (ons_decWalkOfKWChain L current
                (ons_decWalkExternalDarts p ++ [finish]) hchain').edges := hmain
          _ = (ons_decWalkOfKWChain L current
                (ons_decWalkExternalDarts
                    (SimpleGraph.Walk.cons huw p) ++ [finish])
                hchain).edges :=
            ons_decWalkOfKWChain_edges_congr L current _ _
              (by rw [hext]) hchain' hchain

theorem ons_decGeometricLoopStates_cycle_eq_externalDarts
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d) :
    List.ofFn (ons_decGeometricLoopStates (ons_decCycleDartLoop q)) =
      ons_decWalkExternalDarts q := by
  let loop := ons_decCycleDartLoop q
  let states := List.ofFn (ons_decGeometricLoopStates loop)
  let ext := ons_decWalkExternalDarts q
  have hextHead : ext.head? = some d :=
    ons_decWalkExternalDarts_head q hq hsnd
  have hext : ext = d :: ext.tail := by
    apply List.eq_cons_of_mem_head?
    simpa [hextHead]
  have hstatesne : states ≠ [] := by
    rw [List.ne_nil_iff_length_pos, List.length_ofFn]
    exact NeZero.pos (ons_decCycleDartList q).length
  have hstatesHead : states.head? = some d := by
    rw [List.head?_eq_head hstatesne]
    rw [List.head_ofFn]
    simp [states, loop, ons_decGeometricLoopStates,
      ons_decCycleDartLoop_zero]
  have hstates : states = d :: states.tail := by
    apply List.eq_cons_of_mem_head?
    simpa [hstatesHead]
  have hrev := ons_decGeometricLoopStates_tail_reverse loop
  have hrev' : d :: states.tail.reverse = d :: ext.tail.reverse := by
    calc
      d :: states.tail.reverse =
          List.ofFn loop := by
        simpa [states, loop, ons_decCycleDartLoop_zero] using hrev
      _ = ons_decCycleDartList q := ons_decCycleDartList_ofFn q
      _ = d :: ext.tail.reverse := by
        simpa [ext] using ons_decCycleDartList_eq q
  have htailRev : states.tail.reverse = ext.tail.reverse :=
    List.cons.inj hrev' |>.2
  have htail : states.tail = ext.tail := by
    exact List.reverse_injective htailRev
  change states = ext
  rw [hstates, hext, htail]



theorem ons_decLoopWalk_cycle_edges
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d) :
    (ons_decLoopWalk L (ons_decCycleDartLoop q)
      (ons_decCycleDartLoop_valid q hq hsnd)).edges = q.edges := by
  let loop := ons_decCycleDartLoop q
  let states := List.ofFn (ons_decGeometricLoopStates loop)
  let p : (ons_decGraph L).Walk (ons_dartRev L d) d :=
    q.tail.copy hsnd rfl
  have hqne : ¬ q.Nil := hq.not_nil
  have hqcons : q = (ons_decExternalStepWalk L d).append p := by
    calc
      q = SimpleGraph.Walk.cons (q.adj_snd hqne) q.tail :=
        (q.cons_tail_eq hqne).symm
      _ = (ons_decExternalStepWalk L d).append p := by
        simp [ons_decExternalStepWalk, p]
  have hpPath : p.IsPath := by
    exact (SimpleGraph.Walk.isPath_copy q.tail hsnd rfl).mpr hq.isPath_tail
  have hextCons : ons_decWalkExternalDarts q =
      d :: ons_decWalkExternalDarts p := by
    rw [hqcons, ons_decWalkExternalDarts_append]
    have hstep : ons_decWalkExternalDarts
        (ons_decExternalStepWalk L d) = [d] := by
      unfold ons_decExternalStepWalk
      rw [ons_decWalkExternalDarts_cons_external]
      · simp [ons_decWalkExternalDarts]
      · rfl
    rw [hstep]
    simp [p, ons_decWalkExternalDarts]
  have hchain : List.IsChain (ons_decGeometricStep L)
      (d :: (ons_decWalkExternalDarts p ++ [d])) := by
    have hclosed := ons_decWalkExternalDarts_isChain_closed q
    rw [hextCons] at hclosed
    apply hclosed.imp
    intro x y hxy
    exact hxy.symm
  have hrebuild := ons_decWalkOfKWChain_rebuild L d
    (.nil : (ons_decGraph L).Walk (ons_dartRev L d)
      (ons_dartRev L d)) p (by simp) (.nil)
      (by simpa using hpPath) hchain
  have hstates :=
    ons_decGeometricLoopStates_cycle_eq_externalDarts q hq hsnd
  have htail : states.tail = ons_decWalkExternalDarts p := by
    rw [show states = ons_decWalkExternalDarts q by simpa [states, loop] using hstates]
    rw [hextCons]
    rfl
  unfold ons_decLoopWalk
  simp only [SimpleGraph.Walk.edges_copy]
  change (ons_decWalkOfKWChain L (loop 0)
      (states.tail ++ [loop 0]) _).edges =
    q.edges
  have hroot : loop 0 = d := by
    simpa [loop] using ons_decCycleDartLoop_zero q
  calc
    (ons_decWalkOfKWChain L (loop 0)
        (states.tail ++ [loop 0]) _).edges =
        (ons_decWalkOfKWChain L d
          (ons_decWalkExternalDarts p ++ [d]) hchain).edges :=
      ons_decWalkOfKWChain_edges_congr_root L _ _ _ _ hroot
        (by rw [hroot, htail]) _ hchain
    _ = ((ons_decExternalStepWalk L d).append
          ((SimpleGraph.Walk.nil).append p)).edges := hrebuild.symm
    _ = q.edges := by simpa [hqcons]

theorem ons_decCycleDartLoop_exponent
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d) :
    ons_decLoopExponent L (ons_decCycleDartLoop q) =
      ons_finsetExponent q.edges.toFinset := by
  let loop := ons_decCycleDartLoop q
  let hvalid := ons_decCycleDartLoop_valid q hq hsnd
  rw [← ons_decLoopWalk_edgeCount L loop hvalid]
  unfold ons_decWalkEdgeCount
  rw [show (ons_decLoopWalk L loop hvalid).edges = q.edges by
    simpa [loop, hvalid] using ons_decLoopWalk_cycle_edges q hq hsnd]
  exact (ons_finsetExponent_toFinset_eq_edgeCount
    q.edges hq.edges_nodup).symm

theorem ons_decCycleDartLoop_scalar
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d) (a b : Fin 2) :
    ons_decLoopScalar L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)
        (ons_decCycleDartLoop q) =
      -((ons_spinCharacter a b
        (ons_evenHomology L (ons_walkOriginalEdges q))) : ℂ) := by
  let Lambda := ons_KWmatWeightedPhase L (fun _ ↦ 1) ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b)
  rw [ons_decLoopScalar_eq_loopWeight_one]
  rw [← ons_decCycleFirstReturn_edgeWeight_eq_loopWeight q Lambda]
  simpa [Lambda] using
    ons_decCycleFirstReturn_weight_eq_neg_spinCharacter
      q hq hsnd (fun _ ↦ 1) a b

theorem ons_decCycleDartLoop_scalar_ne_zero
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d) (a b : Fin 2) :
    ons_decLoopScalar L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)
        (ons_decCycleDartLoop q) ≠ 0 := by
  rw [ons_decCycleDartLoop_scalar q hq hsnd a b]
  simp [ons_spinCharacter]

theorem ons_decCycleDartLoop_mem_squarefreeLoopFinset
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d) (a b : Fin 2) :
    ons_decCycleDartLoop q ∈
      ons_decSquarefreeLoopFinset L a b q.edges.toFinset := by
  rw [ons_mem_decSquarefreeLoopFinset]
  exact ⟨ons_decCycleDartLoop_exponent q hq hsnd,
    ons_decCycleDartLoop_scalar_ne_zero q hq hsnd a b⟩

theorem ons_decFormalLogCoeff_squarefree_of_mem_neZero
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (S : Finset (ons_DecEdge L)) {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L)
    (hd : d ∈ ons_decSquarefreeLoopFinset L a b S) :
    ons_decFormalLogCoeff L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)
        (ons_finsetExponent S) =
      (ons_spinCharacter a b
        (ons_evenHomology L
          (ons_walkOriginalEdges
            (ons_decLoopWalk L d
              (ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
                (ons_spinPhase L a) (ons_spinPhase L b) d
                ((ons_mem_decSquarefreeLoopFinset L a b S d).mp hd).2)))) : ℂ) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact ons_decFormalLogCoeff_squarefree_of_mem L a b S r d hd



theorem ons_decFormalLogCoeff_cycle
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d) (a b : Fin 2) :
    ons_decFormalLogCoeff L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)
        (ons_finsetExponent q.edges.toFinset) =
      (ons_spinCharacter a b
        (ons_evenHomology L (ons_walkOriginalEdges q)) : ℂ) := by
  let loop := ons_decCycleDartLoop q
  have hd : loop ∈
      ons_decSquarefreeLoopFinset L a b q.edges.toFinset := by
    simpa [loop] using
      ons_decCycleDartLoop_mem_squarefreeLoopFinset q hq hsnd a b
  have hcoeff := ons_decFormalLogCoeff_squarefree_of_mem_neZero
    L a b q.edges.toFinset loop hd
  let hvalid := ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) loop
    ((ons_mem_decSquarefreeLoopFinset L a b q.edges.toFinset loop).mp hd).2
  have hedges :
      (ons_decLoopWalk L loop hvalid).edges.toFinset = q.edges.toFinset := by
    rw [show (ons_decLoopWalk L loop hvalid).edges = q.edges by
      simpa [loop, hvalid] using ons_decLoopWalk_cycle_edges q hq hsnd]
  have horiginal :
      ons_walkOriginalEdges (ons_decLoopWalk L loop hvalid) =
        ons_walkOriginalEdges q :=
    ons_walkOriginalEdges_eq_of_edges_toFinset_eq
      (ons_decLoopWalk L loop hvalid) q hedges
  simpa only [hvalid, horiginal] using hcoeff

theorem ons_decFormalLogCoeff_unrooted_cycle
    {L : ℕ} [Fact (2 < L)] {root : ons_Dart L}
    (p : (ons_decGraph L).Walk root root) (hp : p.IsCycle)
    (a b : Fin 2) :
    ons_decFormalLogCoeff L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)
        (ons_finsetExponent p.edges.toFinset) =
      (ons_spinCharacter a b
        (ons_evenHomology L (ons_walkOriginalEdges p)) : ℂ) := by
  obtain ⟨d, q, hq, hsnd, hedges⟩ :=
    ons_decCycle_root_external p hp
  have hcoeff := ons_decFormalLogCoeff_cycle q hq hsnd a b
  have horiginal : ons_walkOriginalEdges q = ons_walkOriginalEdges p :=
    ons_walkOriginalEdges_eq_of_edges_toFinset_eq q p hedges
  rw [hedges] at hcoeff
  simpa only [horiginal] using hcoeff

end StatMech.Onsager
