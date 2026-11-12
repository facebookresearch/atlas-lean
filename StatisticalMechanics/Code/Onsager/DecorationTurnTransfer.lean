/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.PeriodicTurnClosure
import Code.Onsager.TorusPrimitiveWinding









namespace StatMech.Onsager

open StatMech.Onsager.BaseCase
open BigOperators

def ons_portLineAdj (a b : Fin 4) : Prop :=
  a.val + 1 = b.val ∨ b.val + 1 = a.val

def ons_internalMicroDirections : List (Fin 4) → List (Fin 4)
  | a :: b :: rest =>
      [b, b, a + 2, a + 2] ++ ons_internalMicroDirections (b :: rest)
  | _ => []

theorem ons_internalMicroDirections_turn
    (a : Fin 4) (ports : List (Fin 4))
    (hne : ports ≠ [])
    (hhead : ports.head? = some (a + 2))
    (hchain : List.IsChain ons_portLineAdj ports)
    (hnodup : ports.Nodup) :
    let dirs := List.replicate 4 a ++ ons_internalMicroDirections ports
    ons_openTurnSum dirs + ons_turnPow dirs.getLast! ports.getLast! =
      ons_turnPow a ports.getLast! := by
  cases ports with
  | nil => exact (hne rfl).elim
  | cons p₀ ps =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst p₀
      cases ps with
      | nil =>
          fin_cases a
          all_goals decide
      | cons p₁ ps =>
          cases ps with
          | nil =>
              simp only [List.isChain_cons_cons, List.IsChain.singleton,
                and_true] at hchain
              fin_cases a
              all_goals try fin_cases p₁
              all_goals
                first
                | decide
                | exfalso; revert hchain; decide
                | norm_num [ons_portLineAdj, Fin.add_def] at hchain
          | cons p₂ ps =>
              cases ps with
              | nil =>
                  simp only [List.isChain_cons_cons, List.IsChain.singleton,
                    and_true] at hchain
                  simp only [List.nodup_cons, List.mem_cons,
                    List.mem_singleton, not_or, not_false_eq_true,
                    and_true] at hnodup
                  fin_cases a
                  all_goals try fin_cases p₁
                  all_goals try fin_cases p₂
                  all_goals
                    first
                    | decide
                    | exfalso; revert hchain; decide
                    | exfalso; revert hnodup; decide
                    | norm_num [ons_portLineAdj, Fin.add_def] at hchain
                    | norm_num [Fin.add_def] at hnodup
              | cons p₃ ps =>
                  cases ps with
                  | nil =>
                      simp only [List.isChain_cons_cons,
                        List.IsChain.singleton, and_true] at hchain
                      simp only [List.nodup_cons, List.mem_cons,
                        List.mem_singleton, not_or, not_false_eq_true,
                        and_true] at hnodup
                      fin_cases a
                      all_goals try fin_cases p₁
                      all_goals try fin_cases p₂
                      all_goals try fin_cases p₃
                      all_goals
                        first
                        | decide
                        | exfalso; revert hchain; decide
                        | exfalso; revert hnodup; decide
                        | norm_num [ons_portLineAdj, Fin.add_def] at hchain
                        | norm_num [Fin.add_def] at hnodup
                  | cons p₄ ps =>
                      have hlen := hnodup.length_le_card
                      simp at hlen
                      omega

theorem ons_decEdgeMicroDarts_directions_external
    (L : ℕ) (d e : ons_Dart L)
    (hrev : e = ons_dartRev L d) :
    (ons_decEdgeMicroDarts L d e).map (fun a ↦ a.2) =
      List.replicate 4 d.2 := by
  subst e
  simp [ons_decEdgeMicroDarts, ons_decEdgeRouteDirs]

theorem ons_decEdgeMicroDarts_directions_internal
    (L : ℕ) (d e : ons_Dart L)
    (hint : ons_decInternalAdj d e) :
    (ons_decEdgeMicroDarts L d e).map (fun a ↦ a.2) =
      [e.2, e.2, d.2 + 2, d.2 + 2] := by
  rcases d with ⟨p, mu⟩
  rcases e with ⟨q, nu⟩
  have hpq : p = q := hint.1
  subst q
  fin_cases mu <;> fin_cases nu <;>
    simp [ons_decInternalAdj, ons_decEdgeMicroDarts,
      ons_decEdgeRouteDirs, ons_dartRev, ons_dirStep] at hint ⊢

theorem ons_walk_support_eq_cons
    {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) :
    p.support = u :: p.support.tail := by
  cases p <;> rfl

theorem ons_decExpanded_internal_directions
    (L : ℕ) [Fact (2 < L)] {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v)
    (hint : ∀ a ∈ p.darts, ons_decInternalAdj a.fst a.snd) :
    (ons_decExpandedDartList L p).map (fun a ↦ a.2) =
      ons_internalMicroDirections (p.support.map (fun a ↦ a.2)) := by
  induction p with
  | nil => simp [ons_decExpandedDartList, ons_internalMicroDirections]
  | @cons u w v huw p ih =>
      have huw' : ons_decInternalAdj u w := by
        exact hint ⟨(u, w), huw⟩ (by simp)
      have htail : ∀ a ∈ p.darts,
          ons_decInternalAdj a.fst a.snd := by
        intro a ha
        exact hint a (by simp [ha])
      rw [ons_decExpandedDartList, SimpleGraph.Walk.darts_cons,
        List.flatMap_cons, List.map_append,
        ons_decEdgeMicroDarts_directions_internal L u w huw']
      have ih' := ih htail
      have hsupport := ons_walk_support_eq_cons p
      have hmap : w.2 :: p.support.tail.map (fun a ↦ a.2) =
          p.support.map (fun a ↦ a.2) := by
        simpa only [List.map_cons] using
          congrArg (List.map (fun a ↦ a.2)) hsupport.symm
      rw [SimpleGraph.Walk.support_cons, List.map_cons,
        hsupport, List.map_cons]
      rw [ons_internalMicroDirections]
      rw [hmap]
      exact congrArg
        (List.append [w.2, w.2, u.2 + 2, u.2 + 2]) ih'

theorem ons_support_directions_isChain_portLine
    {L : ℕ} {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v)
    (hint : ∀ a ∈ p.darts, ons_decInternalAdj a.fst a.snd) :
    List.IsChain ons_portLineAdj (p.support.map (fun a ↦ a.2)) := by
  induction p with
  | nil => exact .singleton _
  | @cons u w v huw p ih =>
      rw [SimpleGraph.Walk.support_cons, List.map_cons]
      have hsupport := ons_walk_support_eq_cons p
      have hmap : w.2 :: p.support.tail.map (fun a ↦ a.2) =
          p.support.map (fun a ↦ a.2) := by
        simpa only [List.map_cons] using
          congrArg (List.map (fun a ↦ a.2)) hsupport.symm
      rw [hsupport, List.map_cons, List.isChain_cons_cons]
      constructor
      · have h := hint ⟨(u, w), huw⟩ (by simp)
        exact h.2
      · rw [hmap]
        apply ih
        intro a ha
        exact hint a (by simp [ha])

theorem ons_internalWalk_support_site
    {L : ℕ} {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v)
    (hint : ∀ a ∈ p.darts, ons_decInternalAdj a.fst a.snd) :
    ∀ a ∈ p.support, a.1 = u.1 := by
  induction p with
  | nil => simp
  | @cons u w v huw p ih =>
      have huw' := hint ⟨(u, w), huw⟩ (by simp)
      have htail : ∀ a ∈ p.darts,
          ons_decInternalAdj a.fst a.snd := by
        intro a ha
        exact hint a (by simp [ha])
      intro a ha
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at ha
      rcases ha with rfl | ha
      · rfl
      · exact (ih htail a ha).trans huw'.1.symm

theorem ons_internalWalk_refined_turn
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    {v : ons_Dart L}
    (p : (ons_decGraph L).Walk (ons_dartRev L d) v)
    (hint : ∀ a ∈ p.darts, ons_decInternalAdj a.fst a.snd)
    (hpath : p.IsPath) :
    let dirs := List.replicate 4 d.2 ++
      (ons_decExpandedDartList L p).map (fun a ↦ a.2)
    ons_openTurnSum dirs + ons_turnPow dirs.getLast! v.2 =
      ons_turnPow d.2 v.2 := by
  let ports := p.support.map (fun a ↦ a.2)
  have hpne : ports ≠ [] := by simp [ports]
  have hphead : ports.head? = some (d.2 + 2) := by
    change (p.support.map (fun a ↦ a.2)).head? = _
    rw [ons_walk_support_eq_cons p, List.map_cons]
    simp [ons_dartRev]
  have hpchain : List.IsChain ons_portLineAdj ports :=
    ons_support_directions_isChain_portLine p hint
  have hpnodup : ports.Nodup := by
    rw [SimpleGraph.Walk.isPath_def] at hpath
    apply hpath.map_on
    intro a ha b hb hab
    have hsiteA := ons_internalWalk_support_site p hint a ha
    have hsiteB := ons_internalWalk_support_site p hint b hb
    exact Prod.ext (hsiteA.trans hsiteB.symm) hab
  have hplast : ports.getLast! = v.2 := by
    change (p.support.map (fun a ↦ a.2)).getLast! = _
    rw [ons_getLast!_eq_getLast ports hpne]
    rw [List.getLast_map]
    rw [p.getLast_support]
  rw [ons_decExpanded_internal_directions L p hint]
  have hturn := ons_internalMicroDirections_turn
    d.2 ports hpne hphead hpchain hpnodup
  rw [hplast] at hturn
  exact hturn

def ons_walkExpandedDirections
    (L : ℕ) [Fact (2 < L)] {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) : List (Fin 4) :=
  (ons_decExpandedDartList L p).map (fun a ↦ a.2)

def ons_walkExternalDirections
    {L : ℕ} {u v : ons_Dart L}
  (p : (ons_decGraph L).Walk u v) : List (Fin 4) :=
  (ons_decWalkExternalDarts p).map (fun a ↦ a.2)

@[simp] theorem ons_walkExpandedDirections_nil
    (L : ℕ) [Fact (2 < L)] (u : ons_Dart L) :
    ons_walkExpandedDirections L
      (SimpleGraph.Walk.nil : (ons_decGraph L).Walk u u) = [] := by
  simp [ons_walkExpandedDirections, ons_decExpandedDartList]

@[simp] theorem ons_walkExternalDirections_nil
    (L : ℕ) (u : ons_Dart L) :
    ons_walkExternalDirections
      (SimpleGraph.Walk.nil : (ons_decGraph L).Walk u u) = [] := by
  simp [ons_walkExternalDirections, ons_decWalkExternalDarts]

theorem ons_walkExpandedDirections_append
    (L : ℕ) [Fact (2 < L)] {u v w : ons_Dart L}
    (p : (ons_decGraph L).Walk u v)
    (q : (ons_decGraph L).Walk v w) :
    ons_walkExpandedDirections L (p.append q) =
      ons_walkExpandedDirections L p ++ ons_walkExpandedDirections L q := by
  simp [ons_walkExpandedDirections, ons_decExpandedDartList,
    SimpleGraph.Walk.darts_append, List.flatMap_append]

theorem ons_walkExpandedDirections_cons
    (L : ℕ) [Fact (2 < L)] {u v w : ons_Dart L}
    (h : (ons_decGraph L).Adj u v)
    (p : (ons_decGraph L).Walk v w) :
    ons_walkExpandedDirections L (SimpleGraph.Walk.cons h p) =
      (ons_decEdgeMicroDarts L u v).map (fun a ↦ a.2) ++
        ons_walkExpandedDirections L p := by
  simp [ons_walkExpandedDirections, ons_decExpandedDartList]

theorem ons_decTurnTransfer_invariant
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L)
    {u v : ons_Dart L}
    (r : (ons_decGraph L).Walk (ons_dartRev L d) u)
    (p : (ons_decGraph L).Walk u v)
    (hrint : ∀ a ∈ r.darts, ons_decInternalAdj a.fst a.snd)
    (hrpath : r.IsPath)
    (hallpath : (r.append p).IsPath) :
    let full := List.replicate 4 d.2 ++
      ons_walkExpandedDirections L r ++ ons_walkExpandedDirections L p
    let ext := d.2 :: ons_walkExternalDirections p
    ons_openTurnSum full + ons_turnPow full.getLast! v.2 =
      ons_openTurnSum ext + ons_turnPow ext.getLast! v.2 := by
  induction p generalizing d with
  | nil =>
      simpa [ons_decExpandedDartList, ons_openTurnSum, List.getLast!] using
        ons_internalWalk_refined_turn L d r hrint hrpath
  | @cons u w v huw p ih =>
      by_cases hrev : w = ons_dartRev L u
      · subst w
        let e : (ons_decGraph L).Walk u (ons_dartRev L u) :=
          SimpleGraph.Walk.cons huw .nil
        have hdecomp : r.append (SimpleGraph.Walk.cons huw p) =
            (r.append e).append p := by
          calc
            r.append (SimpleGraph.Walk.cons huw p) =
                r.append (e.append p) := by simp [e]
            _ = (r.append e).append p :=
              SimpleGraph.Walk.append_assoc r e p
        have hppath : p.IsPath := by
          apply SimpleGraph.Walk.isPath_of_isSubwalk
            (SimpleGraph.Walk.isSubwalk_of_append_right hdecomp)
            hallpath
        have htail := ih u (.nil) (by simp) (.nil) (by simpa using hppath)
        let seg := List.replicate 4 d.2 ++ ons_walkExpandedDirections L r
        let rest := List.replicate 4 u.2 ++ ons_walkExpandedDirections L p
        let extRest := u.2 :: ons_walkExternalDirections p
        have hseg : ons_openTurnSum seg +
            ons_turnPow seg.getLast! u.2 = ons_turnPow d.2 u.2 := by
          simpa [seg, ons_walkExpandedDirections] using
            ons_internalWalk_refined_turn L d r hrint hrpath
        have hrest : ons_openTurnSum rest +
            ons_turnPow rest.getLast! v.2 =
              ons_openTurnSum extRest +
                ons_turnPow extRest.getLast! v.2 := by
          simpa [rest, extRest, ons_walkExpandedDirections,
            ons_walkExternalDirections] using htail
        have hsegne : seg ≠ [] := by simp [seg]
        have hrestne : rest ≠ [] := by simp [rest]
        have hextne : extRest ≠ [] := by simp [extRest]
        have hrestHead : rest.head! = u.2 := by simp [rest]
        have hfullDirs : List.replicate 4 d.2 ++
              ons_walkExpandedDirections L r ++
              ons_walkExpandedDirections L (SimpleGraph.Walk.cons huw p) =
            seg ++ rest := by
          rw [ons_walkExpandedDirections_cons,
            ons_decEdgeMicroDarts_directions_external L u
              (ons_dartRev L u) rfl]
        have hextDirs : d.2 ::
              ons_walkExternalDirections (SimpleGraph.Walk.cons huw p) =
            d.2 :: extRest := by
          rw [ons_walkExternalDirections,
            ons_decWalkExternalDarts_cons_external huw p rfl,
            List.map_cons]
          rfl
        dsimp only
        rw [hfullDirs, hextDirs,
          ons_openTurnSum_append seg rest hsegne hrestne,
          ons_getLast!_append_of_right_ne_nil seg rest hrestne,
          hrestHead, hseg]
        have hopen : ons_openTurnSum (d.2 :: extRest) =
            ons_turnPow d.2 u.2 + ons_openTurnSum extRest := by
          change ons_openTurnSum (d.2 :: u.2 ::
            ons_walkExternalDirections p) = _
          rfl
        have hget : (d.2 :: extRest).getLast! = extRest.getLast! := by
          change ([d.2] ++ extRest).getLast! = extRest.getLast!
          exact ons_getLast!_append_of_right_ne_nil [d.2] extRest hextne
        rw [hopen, hget]
        linear_combination hrest
      · have hintEdge : ons_decInternalAdj u w := by
          change ons_decAdj L u w at huw
          exact huw.resolve_left hrev
        let e : (ons_decGraph L).Walk u w :=
          SimpleGraph.Walk.cons huw .nil
        let r' := r.append e
        have hr'int : ∀ a ∈ r'.darts,
            ons_decInternalAdj a.fst a.snd := by
          intro a ha
          rw [show r' = r.append e from rfl,
            SimpleGraph.Walk.darts_append, List.mem_append] at ha
          rcases ha with ha | ha
          · exact hrint a ha
          · have haeq : a = ⟨(u, w), huw⟩ := by simpa [e] using ha
            subst a
            exact hintEdge
        have hdecomp : r'.append p =
            r.append (SimpleGraph.Walk.cons huw p) := by
          calc
            r'.append p = (r.append e).append p := rfl
            _ = r.append (e.append p) :=
              (SimpleGraph.Walk.append_assoc r e p).symm
            _ = r.append (SimpleGraph.Walk.cons huw p) := by simp [e]
        have hr'path : r'.IsPath := by
          apply SimpleGraph.Walk.isPath_of_isSubwalk
            (SimpleGraph.Walk.isSubwalk_of_append_left hdecomp.symm)
            hallpath
        have hallpath' : (r'.append p).IsPath := by
          rw [hdecomp]
          exact hallpath
        have hnext := ih d r' hr'int hr'path hallpath'
        have hexternal : ons_walkExternalDirections
            (SimpleGraph.Walk.cons huw p) =
              ons_walkExternalDirections p := by
          simp [ons_walkExternalDirections, ons_decWalkExternalDarts,
            ons_decDartIsExternal, hrev]
        have hexpanded : ons_walkExpandedDirections L r' =
            ons_walkExpandedDirections L r ++
              ons_walkExpandedDirections L e :=
          ons_walkExpandedDirections_append L r e
        rw [hexternal]
        rw [ons_walkExpandedDirections_cons,
          ons_decEdgeMicroDarts_directions_internal L u w hintEdge]
        rw [hexpanded] at hnext
        have hedirs : ons_walkExpandedDirections L e =
            [w.2, w.2, u.2 + 2, u.2 + 2] := by
          rw [ons_walkExpandedDirections_cons,
            ons_decEdgeMicroDarts_directions_internal L u w hintEdge]
          simp [ons_walkExpandedDirections, ons_decExpandedDartList]
        rw [hedirs] at hnext
        simpa only [List.append_assoc] using hnext

theorem ons_decExpanded_geometric_cyclicTurnSum_eq_external
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d) :
    ons_cyclicTurnSum
        ((ons_decExpandedDartList L q).map (fun a ↦ a.2)) =
      ons_cyclicTurnSum
        ((ons_decWalkExternalDarts q).map (fun a ↦ a.2)) := by
  have hqnil : ¬q.Nil := hq.not_nil
  let p : (ons_decGraph L).Walk (ons_dartRev L d) d :=
    q.tail.copy hsnd rfl
  have hpPath : p.IsPath := by
    simpa [p] using hq.isPath_tail
  have hinv := ons_decTurnTransfer_invariant L d
    (SimpleGraph.Walk.nil :
      (ons_decGraph L).Walk (ons_dartRev L d) (ons_dartRev L d))
    p (by simp) (.nil) (by simpa using hpPath)
  have hfull :
      List.replicate 4 d.2 ++ ons_walkExpandedDirections L p =
        (ons_decExpandedDartList L q).map (fun a ↦ a.2) := by
    change List.replicate 4 d.2 ++ ons_walkExpandedDirections L p =
      ons_walkExpandedDirections L q
    rw [← q.cons_tail_eq hqnil,
      ons_walkExpandedDirections_cons,
      ons_decEdgeMicroDarts_directions_external L d q.snd hsnd]
    simp [p, ons_walkExpandedDirections, ons_decExpandedDartList]
  have hext :
      d.2 :: ons_walkExternalDirections p =
        (ons_decWalkExternalDarts q).map (fun a ↦ a.2) := by
    change d.2 :: ons_walkExternalDirections p =
      ons_walkExternalDirections q
    rw [← q.cons_tail_eq hqnil]
    unfold ons_walkExternalDirections
    rw [ons_decWalkExternalDarts_cons_external]
    · simp [p, ons_walkExternalDirections, ons_decWalkExternalDarts]
    · simpa using hsnd
  rw [← hfull, ← hext]
  simpa [p, ons_cyclicTurnSum, ons_walkExpandedDirections,
    ons_decExpandedDartList] using hinv

theorem ons_ofFn_neg_get_cons_reverse
    {X : Type*} (x : X) (xs : List X) :
    List.ofFn (fun k : Fin (x :: xs.reverse).length ↦
      (x :: xs.reverse).get (-k)) = x :: xs := by
  apply List.ext_getElem
  · simp
  · intro i hi _
    simp only [List.length_ofFn, List.length_cons,
      List.length_reverse] at hi
    by_cases hi0 : i = 0
    · subst i
      simp
    · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
      simp only [List.getElem_ofFn]
      let k : Fin xs.reverse.length := ⟨xs.length - i, by
        simp only [List.length_reverse]
        omega⟩
      let j : Fin xs.length := ⟨i - 1, by omega⟩
      have hneg : -(⟨i, by simpa using hi⟩ :
          Fin (x :: xs.reverse).length) =
          k.succ := by
        apply Fin.ext
        simp only [Fin.val_neg', Fin.val_mk, Fin.val_succ]
        simp only [List.length_cons, List.length_reverse]
        change (xs.length + 1 - i) % (xs.length + 1) =
          xs.length - i + 1
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      have hisucc : (⟨i, by simpa using hi⟩ : Fin (x :: xs).length) =
          j.succ := by
        apply Fin.ext
        simp [j]
        omega
      rw [hneg]
      have hrhs : (x :: xs)[i] = xs.get j := by
        change (x :: xs).get ⟨i, by omega⟩ = xs.get j
        rw [hisucc]
        rfl
      rw [hrhs]
      change xs.reverse.get k = xs.get j
      rw [List.get_reverse' xs k (by simp [k]; omega)]
      congr 1
      apply Fin.ext
      simp [k, j]
      omega

theorem ons_decCycleDartLoop_liftDir_ofFn
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d) :
    List.ofFn (ons_liftDir (ons_decCycleDartLoop q)) =
      (ons_decWalkExternalDarts q).map (fun a ↦ a.2) := by
  let ext := ons_decWalkExternalDarts q
  have hhead : ext.head? = some d :=
    ons_decWalkExternalDarts_head q hq hsnd
  have hext : ext = d :: ext.tail := by
    apply List.eq_cons_of_mem_head?
    simpa [hhead]
  change List.ofFn (fun k ↦
      ((ons_decCycleDartList q).get (-k)).2) =
    ext.map (fun a ↦ a.2)
  rw [ons_decCycleDartList_eq, hext]
  simpa [List.map_ofFn] using congrArg
    (List.map (fun a : ons_Dart L ↦ a.2))
    (ons_ofFn_neg_get_cons_reverse d ext.tail)

theorem ons_decExpandedKWLoop_liftDir_ofFn
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle) :
    letI : NeZero (ons_decExpandedDartList L q).length :=
      ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
    List.ofFn (ons_liftDir (ons_decExpandedKWLoop L q hq)) =
      (ons_decExpandedDartList L q).map (fun a ↦ a.2) := by
  letI : NeZero (ons_decExpandedDartList L q).length :=
    ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
  simpa [ons_liftDir, ons_decExpandedKWLoop,
    ons_decExpandedGeometricLoop, List.map_ofFn] using congrArg
      (List.map (fun a : ons_Dart (8 * L) ↦ a.2))
      (List.ofFn_get (ons_decExpandedDartList L q))

theorem ons_nonUturn_of_valid_portEdge_injective
    {L n : ℕ} [NeZero n] (v : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
    (hinj : Function.Injective (fun k ↦ ons_portEdge L (v k))) :
    ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2 := by
  intro k hturn
  have hdart : v k = ons_dartRev L (v (k + 1)) := by
    apply Prod.ext
    · exact hvalid k
    · simpa [ons_dartRev] using hturn
  have hedge : ons_portEdge L (v k) =
      ons_portEdge L (v (k + 1)) := by
    rw [hdart, ons_portEdge_rev]
  have hk := hinj hedge
  have hv : v k = v (k + 1) := congrArg v hk
  have hself : ons_dartRev L (v (k + 1)) = v (k + 1) :=
    hdart.symm.trans hv
  exact (ons_dartRev_ne_self L (v (k + 1))) hself

theorem ons_turnProduct_eq_zpow_cyclic_liftDir
    {L n : ℕ} [NeZero n] (omega : ℂ) (homega : omega ≠ 0)
    (v : Fin n → ons_Dart L)
    (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2) :
    (∏ k, ons_turnW omega (v (k + 1)).2 (v k).2) =
      omega ^ ons_cyclicTurnSum (List.ofFn (ons_liftDir v)) := by
  rw [ons_liftDir_turnProduct omega v]
  calc
    (∏ k, ons_turnW omega (ons_liftDir v k)
        (ons_liftDir v (k + 1))) =
        ∏ k, omega ^ ons_turnPow (ons_liftDir v k)
          (ons_liftDir v (k + 1)) := by
      apply Finset.prod_congr rfl
      intro k hk
      exact ons_turnW_eq_zpow omega _ _
        (ons_liftDir_nonUturn v hnu k)
    _ = omega ^ (∑ k, ons_turnPow (ons_liftDir v k)
          (ons_liftDir v (k + 1))) :=
      ons_prod_zpow omega homega _ _
    _ = omega ^ ons_cyclicTurnSum
          (List.ofFn (ons_liftDir v)) := by
      rw [ons_cyclicTurnSum_ofFn']

theorem ons_decCycleDartLoop_nonUturn
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d) :
    ∀ k : Fin (ons_decCycleDartList q).length,
      (ons_decCycleDartLoop q k).2 ≠
        (ons_decCycleDartLoop q (k + 1)).2 + 2 :=
  ons_nonUturn_of_valid_portEdge_injective
    (ons_decCycleDartLoop q)
    (ons_decCycleDartLoop_valid q hq hsnd)
    (ons_decCycleDartLoop_portEdge_injective q hq hsnd)

theorem ons_decCycle_turnProduct_eq_expanded
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d) :
    letI : NeZero (ons_decExpandedDartList L q).length :=
      ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
    (∏ k, ons_turnW ons_turnRoot
        (ons_decCycleDartLoop q (k + 1)).2
        (ons_decCycleDartLoop q k).2) =
      ∏ k, ons_turnW ons_turnRoot
        (ons_decExpandedKWLoop L q hq (k + 1)).2
        (ons_decExpandedKWLoop L q hq k).2 := by
  letI : NeZero (ons_decExpandedDartList L q).length :=
    ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
  have hroot : ons_turnRoot ≠ 0 := by
    intro h
    have hs := ons_turnRoot_sq
    rw [h] at hs
    have hs' : (0 : ℂ) = Complex.I := by simpa using hs
    exact Complex.I_ne_zero hs'.symm
  rw [ons_turnProduct_eq_zpow_cyclic_liftDir ons_turnRoot hroot
      (ons_decCycleDartLoop q)
      (ons_decCycleDartLoop_nonUturn L q hq hsnd),
    ons_turnProduct_eq_zpow_cyclic_liftDir ons_turnRoot hroot
      (ons_decExpandedKWLoop L q hq)
      (ons_decExpandedKWLoop_nonUturn L q hq),
    ons_decCycleDartLoop_liftDir_ofFn L q hq hsnd,
    ons_decExpandedKWLoop_liftDir_ofFn L q hq,
    ons_decExpanded_geometric_cyclicTurnSum_eq_external L q hq hsnd]

theorem ons_decExpanded_winding_eq_zero_of_zeroHomology
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d)
    (hhom : ons_evenHomology L (ons_walkOriginalEdges q) = 0) :
    letI : NeZero (ons_decExpandedDartList L q).length :=
      ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
    (∑ k, ons_dirExponentX (ons_decExpandedKWLoop L q hq k).2) = 0 ∧
      (∑ k, ons_dirExponentY (ons_decExpandedKWLoop L q hq k).2) = 0 := by
  letI : Fact (2 < 8 * L) := ⟨by
    have := (Fact.out : 2 < L)
    omega⟩
  letI : NeZero (ons_decExpandedDartList L q).length :=
    ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
  let v := ons_decExpandedKWLoop L q hq
  have hF : ons_dartEdgeSet v ∈
      StatMech.Ising.evenSubgraphs (onsTorusGraph (8 * L)) := by
    rw [show ons_dartEdgeSet v = (ons_decEmbedWalk L q).edges.toFinset by
      exact ons_decExpandedKWLoop_edgeSet L q hq]
    exact ons_cycle_edges_evenSubgraph (onsTorusGraph (8 * L))
      (ons_decEmbedWalk L q) (ons_decEmbedWalk_isCycle L q hq)
  have hrefined : ons_evenHomology (8 * L) (ons_dartEdgeSet v) = 0 := by
    rw [show ons_dartEdgeSet v = (ons_decEmbedWalk L q).edges.toFinset by
      exact ons_decExpandedKWLoop_edgeSet L q hq]
    rw [ons_decEmbedWalk_evenHomology_eq L q hq hsnd, hhom]
  exact ons_simpleLoop_zeroHomology_winding_eq_zero v
    (ons_decExpandedKWLoop_valid L q hq)
    (ons_decExpandedKWLoop_site_injective L q hq)
    (ons_decExpandedKWLoop_nonUturn L q hq) hF hrefined

theorem ons_neg_spinCharacter_zero_zero
    (h : Fin 2 × Fin 2) :
    -(ons_spinCharacter 0 0 h : ℂ) =
      if h = 0 then -1 else 1 := by
  rcases h with ⟨hx, hy⟩
  fin_cases hx <;> fin_cases hy <;>
    norm_num [ons_spinCharacter, Prod.ext_iff]

theorem ons_decCycle_turnProduct_eq_neg_spinCharacter
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d) :
    (∏ k, ons_turnW ons_turnRoot
        (ons_decCycleDartLoop q (k + 1)).2
        (ons_decCycleDartLoop q k).2) =
      -(ons_spinCharacter 0 0
        (ons_evenHomology L (ons_walkOriginalEdges q)) : ℂ) := by
  letI : NeZero (ons_decExpandedDartList L q).length :=
    ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
  rw [ons_decCycle_turnProduct_eq_expanded L q hq hsnd,
    ons_neg_spinCharacter_zero_zero]
  by_cases hhom : ons_evenHomology L (ons_walkOriginalEdges q) = 0
  · rw [if_pos hhom]
    obtain ⟨hx, hy⟩ :=
      ons_decExpanded_winding_eq_zero_of_zeroHomology L q hq hsnd hhom
    exact ons_decExpanded_turnProduct_eq_neg_one_of_zero_winding
      L q hq hx hy
  · rw [if_neg hhom]
    exact ons_decExpanded_turnProduct_eq_one_of_nonzeroHomology
      L q hq hsnd hhom

end StatMech.Onsager
