/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardLocalAngularSplit
import Code.FrontierA.KacWardAngularSplitSpinor





namespace StatMech.FrontierA

open SimpleGraph
open scoped BigOperators


theorem kwLocalPortRoot_sq_of_matching
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) {p q : KWDartPort G}
    (hmatching : kwDartOfPort G q = (kwDartOfPort G p).symm) :
    data.root q ^ 2 = -(data.root p ^ 2) := by
  have hq : q = kwPortOfDart G (kwDartOfPort G p).symm := by
    apply kwDartOfPort_injective G
    simpa using hmatching
  rw [hq, data.root_sq_symm]
  simp



noncomputable def kwLocalAngularSplitSpinorGauge
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G)
    (d : (kwOrderedDartPortSplitGraph G
      (data.order)).Dart) : Complex :=
  if kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm then 1
  else if kwOrderedPortRank (data.order) d.fst <
      kwOrderedPortRank (data.order) d.snd then
    Complex.I
  else 1

theorem kwLocalAngularSplitSpinorGauge_ne_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G)
    (d : (kwOrderedDartPortSplitGraph G
      (data.order)).Dart) :
    kwLocalAngularSplitSpinorGauge data d ≠ 0 := by
  classical
  unfold kwLocalAngularSplitSpinorGauge
  by_cases hmatching :
      kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm
  · simp [hmatching]
  · by_cases hincreasing :
        kwOrderedPortRank (data.order) d.fst <
          kwOrderedPortRank (data.order) d.snd
    · simp [hmatching, hincreasing]
    · simp [hmatching, hincreasing]



noncomputable def kwLocalAngularSplitSpinorDirection
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G)
    (d : (kwOrderedDartPortSplitGraph G
      (data.order)).Dart) : Complex :=
  if kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm then
    (data.root d.fst) ^ 2
  else if kwOrderedPortRank (data.order) d.fst <
      kwOrderedPortRank (data.order) d.snd then
    -1
  else 1

theorem kwLocalAngularSplitSpinorDirection_symm
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G)
    (d : (kwOrderedDartPortSplitGraph G
      (data.order)).Dart) :
    kwLocalAngularSplitSpinorDirection data d.symm =
      -kwLocalAngularSplitSpinorDirection data d := by
  classical
  have hmatchingRev :
      kwDartOfPort G d.symm.snd =
          (kwDartOfPort G d.symm.fst).symm ↔
        kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm := by
    change kwDartOfPort G d.fst = (kwDartOfPort G d.snd).symm ↔
      kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm
    constructor
    · intro h
      rw [h]
      simp
    · intro h
      rw [h]
      simp
  by_cases hmatching :
      kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm
  · have hmatching' :
        kwDartOfPort G d.symm.snd =
          (kwDartOfPort G d.symm.fst).symm := hmatchingRev.mpr hmatching
    unfold kwLocalAngularSplitSpinorDirection
    rw [if_pos hmatching', if_pos hmatching]
    change data.root d.snd ^ 2 =
      -(data.root d.fst ^ 2)
    exact kwLocalPortRoot_sq_of_matching data hmatching
  · have hmatching' :
        ¬kwDartOfPort G d.symm.snd =
          (kwDartOfPort G d.symm.fst).symm := by
        simpa only [hmatchingRev] using hmatching
    have hadj := d.adj
    rw [kwOrderedDartPortSplitGraph_adj] at hadj
    have hinternal := hadj.resolve_left hmatching
    have hmatchingSwap :
        ¬kwDartOfPort G d.fst = (kwDartOfPort G d.snd).symm := by
      intro h
      apply hmatching
      rw [h]
      simp
    rcases hinternal.2 with hinc | hdec
    · have hlt : kwOrderedPortRank (data.order) d.fst <
          kwOrderedPortRank (data.order) d.snd := by omega
      have hnrev : ¬kwOrderedPortRank (data.order) d.snd <
          kwOrderedPortRank (data.order) d.fst := by omega
      unfold kwLocalAngularSplitSpinorDirection
      change (if kwDartOfPort G d.fst = (kwDartOfPort G d.snd).symm then _
          else if kwOrderedPortRank (data.order) d.snd <
            kwOrderedPortRank (data.order) d.fst then -1 else 1) =
        -(if kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm then _
          else if kwOrderedPortRank (data.order) d.fst <
            kwOrderedPortRank (data.order) d.snd then -1 else 1)
      rw [if_neg hmatchingSwap, if_neg hmatching,
        if_neg hnrev, if_pos hlt]
      norm_num
    · have hnlt : ¬kwOrderedPortRank (data.order) d.fst <
          kwOrderedPortRank (data.order) d.snd := by omega
      have hrev : kwOrderedPortRank (data.order) d.snd <
          kwOrderedPortRank (data.order) d.fst := by omega
      unfold kwLocalAngularSplitSpinorDirection
      change (if kwDartOfPort G d.fst = (kwDartOfPort G d.snd).symm then _
          else if kwOrderedPortRank (data.order) d.snd <
            kwOrderedPortRank (data.order) d.fst then -1 else 1) =
        -(if kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm then _
          else if kwOrderedPortRank (data.order) d.fst <
            kwOrderedPortRank (data.order) d.snd then -1 else 1)
      rw [if_neg hmatchingSwap, if_neg hmatching,
        if_pos hrev, if_neg hnlt]


noncomputable def kwLocalAngularSplitSpinorPhase
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G) :=
  kwPhaseGauge (kwLocalAngularSplitSpinorGauge data)
    (kwLocalAngularSplitPhase data)

theorem kwLocalAngularSplitSpinorDirection_ne_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G)
    (d : (kwOrderedDartPortSplitGraph G
      (data.order)).Dart) :
    kwLocalAngularSplitSpinorDirection data d ≠ 0 := by
  classical
  unfold kwLocalAngularSplitSpinorDirection
  by_cases hmatching :
      kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm
  · rw [if_pos hmatching]
    exact pow_ne_zero 2 (data.root_ne_zero d.fst)
  · rw [if_neg hmatching]
    split <;> norm_num



theorem kwLocalAngularSplitSpinorPhase_sq_mul_direction
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G)
    (d e : (kwOrderedDartPortSplitGraph G
      (data.order)).Dart)
    (hconnect : d.snd = e.fst) (hne : d.edge ≠ e.edge) :
    kwLocalAngularSplitSpinorPhase data d e ^ 2 *
        kwLocalAngularSplitSpinorDirection data d =
      kwLocalAngularSplitSpinorDirection data e := by
  classical
  by_cases hd : kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm
  · by_cases he : kwDartOfPort G e.snd = (kwDartOfPort G e.fst).symm
    · exfalso
      apply hne
      have hsnd : e.snd = d.fst := by
        apply kwDartOfPort_injective G
        rw [he, ← hconnect, hd]
        simp
      have hedart : e = d.symm := by
        apply SimpleGraph.Dart.ext
        apply Prod.ext
        · exact hconnect.symm
        · exact hsnd
      rw [hedart]
      exact d.edge_symm.symm
    · have hmatchRoot : data.root e.fst ^ 2 =
          -(data.root d.fst ^ 2) := by
        apply kwLocalPortRoot_sq_of_matching data
        rw [← hconnect]
        exact hd
      have hr : data.root e.fst ≠ 0 :=
        data.root_ne_zero e.fst
      by_cases hinc : kwOrderedPortRank (data.order) e.fst <
          kwOrderedPortRank (data.order) e.snd
      · simp [kwLocalAngularSplitSpinorPhase, kwPhaseGauge,
          kwLocalAngularSplitSpinorGauge, kwLocalAngularSplitSpinorDirection,
          kwLocalAngularSplitPhase, hd, he, hinc]
        field_simp
        rw [hmatchRoot]
        norm_num [Complex.I_sq]
      · simp [kwLocalAngularSplitSpinorPhase, kwPhaseGauge,
          kwLocalAngularSplitSpinorGauge, kwLocalAngularSplitSpinorDirection,
          kwLocalAngularSplitPhase, hd, he, hinc]
        field_simp
        rw [hmatchRoot]
        norm_num [Complex.I_sq]
  · by_cases he : kwDartOfPort G e.snd = (kwDartOfPort G e.fst).symm
    · by_cases hinc : kwOrderedPortRank (data.order) d.fst <
          kwOrderedPortRank (data.order) d.snd
      · simp [kwLocalAngularSplitSpinorPhase, kwPhaseGauge,
          kwLocalAngularSplitSpinorGauge, kwLocalAngularSplitSpinorDirection,
          kwLocalAngularSplitPhase, hd, he, hinc]
        rw [mul_pow, Complex.I_sq]
        ring
      · simp [kwLocalAngularSplitSpinorPhase, kwPhaseGauge,
          kwLocalAngularSplitSpinorGauge, kwLocalAngularSplitSpinorDirection,
          kwLocalAngularSplitPhase, hd, he, hinc]
    · let di : KWOrderedInternalSplitDart G
          (data.order) := ⟨d, hd⟩
      let ei : KWOrderedInternalSplitDart G
          (data.order) := ⟨e, he⟩
      have hstep : KWOrderedInternalDartStep G
          (data.order) di ei := by
        exact ⟨hconnect, hne⟩
      by_cases hinc : kwOrderedPortRank (data.order) d.fst <
          kwOrderedPortRank (data.order) d.snd
      · have heinc : kwOrderedPortRank (data.order) e.fst <
            kwOrderedPortRank (data.order) e.snd := by
          simpa only [di, ei] using
            (kwOrderedInternalDartStep_rank_lt G
              (data.order) hstep hinc)
        simp [kwLocalAngularSplitSpinorPhase, kwPhaseGauge,
          kwLocalAngularSplitSpinorGauge, kwLocalAngularSplitSpinorDirection,
          kwLocalAngularSplitPhase, hd, he, hinc, heinc]
      · have hddata' := kwOrderedInternalSplitDart_adj_data G
          (data.order) di
        have hddata : d.fst.1 = d.snd.1 ∧
            (kwOrderedPortRank (data.order) d.fst + 1 =
                kwOrderedPortRank (data.order) d.snd ∨
              kwOrderedPortRank (data.order) d.snd + 1 =
                kwOrderedPortRank (data.order) d.fst) := by
          simpa only [di] using hddata'
        have hddec : kwOrderedPortRank (data.order) d.snd <
            kwOrderedPortRank (data.order) d.fst := by
          rcases hddata.2 with h | h <;> omega
        have hedec : kwOrderedPortRank (data.order) e.snd <
            kwOrderedPortRank (data.order) e.fst := by
          simpa only [di, ei] using
            (kwOrderedInternalDartStep_rank_gt G
              (data.order) hstep hddec)
        have heinc : ¬kwOrderedPortRank (data.order) e.fst <
            kwOrderedPortRank (data.order) e.snd := by omega
        simp [kwLocalAngularSplitSpinorPhase, kwPhaseGauge,
          kwLocalAngularSplitSpinorGauge, kwLocalAngularSplitSpinorDirection,
          kwLocalAngularSplitPhase, hd, he, hinc, heinc]


theorem kwLocalAngularSplitSpinorPath_sq_mul_direction
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G)
    {N : Nat}
    (path : Fin (N + 1) →
      (kwOrderedDartPortSplitGraph G
        (data.order)).Dart)
    (hvalid : ∀ j : Fin N,
      (path j.castSucc).snd = (path j.succ).fst ∧
        (path j.castSucc).edge ≠ (path j.succ).edge) :
    (∏ j : Fin N, kwLocalAngularSplitSpinorPhase data
        (path j.castSucc) (path j.succ)) ^ 2 *
        kwLocalAngularSplitSpinorDirection data (path 0) =
      kwLocalAngularSplitSpinorDirection data (path (Fin.last N)) := by
  classical
  let phase : Fin N → Complex := fun j ↦
    kwLocalAngularSplitSpinorPhase data (path j.castSucc) (path j.succ)
  let direction : Fin (N + 1) → Complex := fun j ↦
    kwLocalAngularSplitSpinorDirection data (path j)
  let prefixProd : Complex := ∏ j : Fin N, direction j.castSucc
  let suffixProd : Complex := ∏ j : Fin N, direction j.succ
  have hprod : (∏ j : Fin N, phase j) ^ 2 * prefixProd = suffixProd := by
    calc
      (∏ j : Fin N, phase j) ^ 2 * prefixProd =
          (∏ j : Fin N, phase j ^ 2) *
            ∏ j : Fin N, direction j.castSucc := by
              rw [Finset.prod_pow]
      _ = ∏ j : Fin N, phase j ^ 2 * direction j.castSucc := by
        rw [Finset.prod_mul_distrib]
      _ = ∏ j : Fin N, direction j.succ := by
        apply Finset.prod_congr rfl
        intro j _
        exact kwLocalAngularSplitSpinorPhase_sq_mul_direction data _ _
          (hvalid j).1 (hvalid j).2
  have hprefix_ne : prefixProd ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact kwLocalAngularSplitSpinorDirection_ne_zero data _
  have hsuffix_eq : suffixProd =
      prefixProd * kwLocalAngularSplitSpinorDirection data (path (Fin.last N)) /
        kwLocalAngularSplitSpinorDirection data (path 0) := by
    have hfullCast := Fin.prod_univ_castSucc direction
    have hfullSucc := Fin.prod_univ_succ direction
    have hzero := kwLocalAngularSplitSpinorDirection_ne_zero data (path 0)
    apply (mul_left_cancel₀ hzero)
    field_simp
    rw [← hfullSucc, ← hfullCast]
  change (∏ j : Fin N, phase j) ^ 2 * direction 0 =
    direction (Fin.last N)
  have hzero : direction 0 ≠ 0 :=
    kwLocalAngularSplitSpinorDirection_ne_zero data (path 0)
  apply (mul_left_cancel₀ hprefix_ne)
  calc
    prefixProd * ((∏ j : Fin N, phase j) ^ 2 * direction 0) =
        ((∏ j : Fin N, phase j) ^ 2 * prefixProd) * direction 0 := by
          ring
    _ = suffixProd * direction 0 := by rw [hprod]
    _ = (prefixProd * direction (Fin.last N) / direction 0) *
        direction 0 := by rw [hsuffix_eq]
    _ = prefixProd * direction (Fin.last N) := by field_simp



theorem kwLocalAngularSplitSpinorPath_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G)
    {N : Nat}
    (path : Fin (N + 1) →
      (kwOrderedDartPortSplitGraph G
        (data.order)).Dart)
    (hend : path (Fin.last N) = (path 0).symm)
    (hvalid : ∀ j : Fin N,
      (path j.castSucc).snd = (path j.succ).fst ∧
        (path j.castSucc).edge ≠ (path j.succ).edge) :
    (∏ j : Fin N, kwLocalAngularSplitSpinorPhase data
      (path j.castSucc) (path j.succ)) ^ 2 = -1 := by
  have htel := kwLocalAngularSplitSpinorPath_sq_mul_direction data path hvalid
  rw [hend, kwLocalAngularSplitSpinorDirection_symm] at htel
  have hne := kwLocalAngularSplitSpinorDirection_ne_zero data (path 0)
  apply (mul_right_cancel₀ hne)
  simpa only [neg_mul, one_mul] using htel


theorem kwLocalAngularSplitSpinorPhase_reverse
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G)
    (d e : (kwOrderedDartPortSplitGraph G
      (data.order)).Dart)
    (hconnect : d.snd = e.fst) (hne : d.edge ≠ e.edge) :
    kwLocalAngularSplitSpinorPhase data e.symm d.symm =
      (kwLocalAngularSplitSpinorPhase data d e)⁻¹ := by
  classical
  have hdrev :
      kwDartOfPort G d.fst = (kwDartOfPort G d.snd).symm ↔
        kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm := by
    constructor <;> intro h <;> rw [h] <;> simp
  have herev :
      kwDartOfPort G e.fst = (kwDartOfPort G e.snd).symm ↔
        kwDartOfPort G e.snd = (kwDartOfPort G e.fst).symm := by
    constructor <;> intro h <;> rw [h] <;> simp
  by_cases hd : kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm
  · by_cases he : kwDartOfPort G e.snd = (kwDartOfPort G e.fst).symm
    · exfalso
      apply hne
      have hsnd : e.snd = d.fst := by
        apply kwDartOfPort_injective G
        rw [he, ← hconnect, hd]
        simp
      have hedart : e = d.symm := by
        apply SimpleGraph.Dart.ext
        apply Prod.ext
        · exact hconnect.symm
        · exact hsnd
      rw [hedart]
      exact d.edge_symm.symm
    · by_cases hinc : kwOrderedPortRank (data.order) e.fst <
          kwOrderedPortRank (data.order) e.snd
      · have hnback : ¬kwOrderedPortRank (data.order) e.snd <
            kwOrderedPortRank (data.order) e.fst := by omega
        simp [kwLocalAngularSplitSpinorPhase, kwPhaseGauge,
          kwLocalAngularSplitSpinorGauge, kwLocalAngularSplitPhase,
          herev, hd, he, hinc, hnback]
        rw [hconnect]
        field_simp
        norm_num [Complex.I_sq]
      · have eadj := e.adj
        rw [kwOrderedDartPortSplitGraph_adj] at eadj
        have eranks := (eadj.resolve_left he).2
        have hback : kwOrderedPortRank (data.order) e.snd <
            kwOrderedPortRank (data.order) e.fst := by
          rcases eranks with h | h <;> omega
        simp [kwLocalAngularSplitSpinorPhase, kwPhaseGauge,
          kwLocalAngularSplitSpinorGauge, kwLocalAngularSplitPhase,
          herev, hd, he, hinc, hback]
        rw [hconnect]
        field_simp
  · by_cases he : kwDartOfPort G e.snd = (kwDartOfPort G e.fst).symm
    · by_cases hinc : kwOrderedPortRank (data.order) d.fst <
          kwOrderedPortRank (data.order) d.snd
      · have hnback : ¬kwOrderedPortRank (data.order) e.fst <
            kwOrderedPortRank (data.order) d.fst := by
          rw [← hconnect]
          omega
        simp [kwLocalAngularSplitSpinorPhase, kwPhaseGauge,
          kwLocalAngularSplitSpinorGauge, kwLocalAngularSplitPhase,
          hdrev, hd, he, hinc]
        rw [hconnect]
        simp [hnback]
        ring
      · have dadj := d.adj
        rw [kwOrderedDartPortSplitGraph_adj] at dadj
        have dranks := (dadj.resolve_left hd).2
        have dback : kwOrderedPortRank (data.order) d.snd <
            kwOrderedPortRank (data.order) d.fst := by
          rcases dranks with h | h <;> omega
        have hback : kwOrderedPortRank (data.order) e.fst <
            kwOrderedPortRank (data.order) d.fst := by
          rw [← hconnect]
          exact dback
        simp [kwLocalAngularSplitSpinorPhase, kwPhaseGauge,
          kwLocalAngularSplitSpinorGauge, kwLocalAngularSplitPhase,
          hdrev, hd, he, hinc, dback]
        rw [hconnect]
        calc
          -(Complex.I * (data.root e.fst)⁻¹ * Complex.I) =
              -(Complex.I ^ 2 * (data.root e.fst)⁻¹) := by ring
          _ = (data.root e.fst)⁻¹ := by
            rw [Complex.I_sq]
            ring
    · let di : KWOrderedInternalSplitDart G
          (data.order) := ⟨d, hd⟩
      let ei : KWOrderedInternalSplitDart G
          (data.order) := ⟨e, he⟩
      have hstep : KWOrderedInternalDartStep G
          (data.order) di ei := ⟨hconnect, hne⟩
      by_cases hinc : kwOrderedPortRank (data.order) d.fst <
          kwOrderedPortRank (data.order) d.snd
      · have heinc : kwOrderedPortRank (data.order) e.fst <
            kwOrderedPortRank (data.order) e.snd := by
          simpa only [di, ei] using
            (kwOrderedInternalDartStep_rank_lt G
              (data.order) hstep hinc)
        have hdback : ¬kwOrderedPortRank (data.order) d.snd <
            kwOrderedPortRank (data.order) d.fst := by omega
        have heback : ¬kwOrderedPortRank (data.order) e.snd <
            kwOrderedPortRank (data.order) e.fst := by omega
        simp [kwLocalAngularSplitSpinorPhase, kwPhaseGauge,
          kwLocalAngularSplitSpinorGauge, kwLocalAngularSplitPhase,
          hdrev, herev, hd, he, hinc, heinc, hdback, heback]
      · have hddata' := kwOrderedInternalSplitDart_adj_data G
          (data.order) di
        have hddata : d.fst.1 = d.snd.1 ∧
            (kwOrderedPortRank (data.order) d.fst + 1 =
                kwOrderedPortRank (data.order) d.snd ∨
              kwOrderedPortRank (data.order) d.snd + 1 =
                kwOrderedPortRank (data.order) d.fst) := by
          simpa only [di] using hddata'
        have hddec : kwOrderedPortRank (data.order) d.snd <
            kwOrderedPortRank (data.order) d.fst := by
          rcases hddata.2 with h | h <;> omega
        have hedec : kwOrderedPortRank (data.order) e.snd <
            kwOrderedPortRank (data.order) e.fst := by
          simpa only [di, ei] using
            (kwOrderedInternalDartStep_rank_gt G
              (data.order) hstep hddec)
        have heinc : ¬kwOrderedPortRank (data.order) e.fst <
            kwOrderedPortRank (data.order) e.snd := by omega
        simp [kwLocalAngularSplitSpinorPhase, kwPhaseGauge,
          kwLocalAngularSplitSpinorGauge, kwLocalAngularSplitPhase,
          hdrev, herev, hd, he, hinc, heinc, hddec, hedec]


theorem kwLocalAngularSplitSpinorLoop_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G)
    {n : Nat} [NeZero n]
    (loop : Fin n → (kwOrderedDartPortSplitGraph G
      (data.order)).Dart)
    (hvalid : ∀ k : Fin n,
      (loop k).snd = (loop (k + 1)).fst ∧
        (loop k).edge ≠ (loop (k + 1)).edge) :
    (∏ k : Fin n, kwLocalAngularSplitSpinorPhase data
      (loop k) (loop (k + 1))) ^ 2 = 1 := by
  classical
  let phase : Fin n → Complex := fun k ↦
    kwLocalAngularSplitSpinorPhase data (loop k) (loop (k + 1))
  let direction : Fin n → Complex := fun k ↦
    kwLocalAngularSplitSpinorDirection data (loop k)
  have hprod : (∏ k : Fin n, phase k) ^ 2 * (∏ k : Fin n, direction k) =
      ∏ k : Fin n, direction (k + 1) := by
    calc
      (∏ k : Fin n, phase k) ^ 2 * (∏ k : Fin n, direction k) =
          (∏ k : Fin n, phase k ^ 2) * ∏ k : Fin n, direction k := by
            rw [Finset.prod_pow]
      _ = ∏ k : Fin n, phase k ^ 2 * direction k := by
        rw [Finset.prod_mul_distrib]
      _ = ∏ k : Fin n, direction (k + 1) := by
        apply Finset.prod_congr rfl
        intro k _
        exact kwLocalAngularSplitSpinorPhase_sq_mul_direction data _ _
          (hvalid k).1 (hvalid k).2
  have hreindex : (∏ k : Fin n, direction (k + 1)) =
      ∏ k : Fin n, direction k := by
    exact Equiv.prod_comp (Equiv.addRight (1 : Fin n)) direction
  rw [hreindex] at hprod
  have hdirection : (∏ k : Fin n, direction k) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k _
    exact kwLocalAngularSplitSpinorDirection_ne_zero data _
  change (∏ k : Fin n, phase k) ^ 2 = 1
  apply mul_right_cancel₀ hdirection
  simpa only [one_mul] using hprod



theorem kwLocalAngularSplitGraphLoopWeight_surgery_sign
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G)
    {n : Nat} [NeZero n]
    (weight : Sym2 (KWDartPort G) → Complex)
    (selected : (kwOrderedDartPortSplitGraph G
      (data.order)).Dart)
    (loop : Fin n → (kwOrderedDartPortSplitGraph G
      (data.order)).Dart)
    (hboth : (∃ i, loop i = selected) ∧ ∃ j, loop j = selected.symm) :
    StatMech.Onsager.ons_loopWeight
        (kwGraphTransition (kwOrderedDartPortSplitGraph G
          (data.order)) weight
          (kwLocalAngularSplitSpinorPhase data))
        (StatMech.Onsager.ons_surgery selected SimpleGraph.Dart.symm loop) =
      -StatMech.Onsager.ons_loopWeight
        (kwGraphTransition (kwOrderedDartPortSplitGraph G
          (data.order)) weight
          (kwLocalAngularSplitSpinorPhase data)) loop := by
  convert kwGraphLoopWeight_surgery_sign
    (kwOrderedDartPortSplitGraph G (data.order))
    weight (kwLocalAngularSplitSpinorPhase data)
    (kwLocalAngularSplitSpinorPath_sq data)
    (fun d e hconnect hne ↦
      kwLocalAngularSplitSpinorPhase_reverse data d e hconnect hne)
    selected loop hboth using 3


theorem kwLocalAngularSplitSpinor_formalRoot_coeff_eq_zero_of_repeated
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G)
    (selected : (kwOrderedDartPortSplitGraph G
      (data.order)).Dart)
    (m : Sym2 (KWDartPort G) →₀ Nat)
    (hrepeated : 2 ≤ m selected.edge) :
    MvPowerSeries.coeff m
      (kwGraphFormalRoot
        (kwOrderedDartPortSplitGraph G (data.order))
        (kwLocalAngularSplitSpinorPhase data)) = 0 := by
  apply kw_spinorGraph_formalRoot_coeff_eq_zero_of_repeated
    (kwOrderedDartPortSplitGraph G (data.order))
    (kwLocalAngularSplitSpinorPhase data)
    (kwLocalAngularSplitSpinorPath_sq data)
    (fun d e hconnect hne ↦
      kwLocalAngularSplitSpinorPhase_reverse data d e hconnect hne)
    (kwLocalAngularSplitSpinorLoop_sq data)
    selected m hrepeated



theorem kwLocalAngularSplit_formalRoot_coeff_eq_zero_of_repeated
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G)
    (selected : (kwOrderedDartPortSplitGraph G
      (data.order)).Dart)
    (m : Sym2 (KWDartPort G) →₀ Nat)
    (hrepeated : 2 ≤ m selected.edge) :
    MvPowerSeries.coeff m
      (kwGraphFormalRoot
        (kwOrderedDartPortSplitGraph G (data.order))
        (kwLocalAngularSplitPhase data)) = 0 := by
  have hgauge := kwGraphFormalRoot_phaseGauge
    (kwOrderedDartPortSplitGraph G (data.order))
    (kwLocalAngularSplitPhase data)
    (kwLocalAngularSplitSpinorGauge data)
    (kwLocalAngularSplitSpinorGauge_ne_zero data)
  rw [← hgauge]
  exact kwLocalAngularSplitSpinor_formalRoot_coeff_eq_zero_of_repeated
    data selected m hrepeated



theorem kwLocalAngularSplit_formalRoot_coeff_eq_zero_of_not_squarefree
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G)
    (m : Sym2 (KWDartPort G) →₀ Nat)
    (hm : ¬StatMech.Onsager.ons_IsSquarefreeExponent m) :
    MvPowerSeries.coeff m
      (kwGraphFormalRoot
        (kwOrderedDartPortSplitGraph G (data.order))
        (kwLocalAngularSplitPhase data)) = 0 := by
  classical
  obtain ⟨edge, hedge⟩ :=
    (StatMech.Onsager.ons_not_isSquarefreeExponent_iff m).mp hm
  by_cases hmem : edge ∈
      (kwOrderedDartPortSplitGraph G
        (data.order)).edgeFinset
  · induction edge using Sym2.inductionOn with
    | _ a b =>
      rw [SimpleGraph.mem_edgeFinset] at hmem
      let selected : (kwOrderedDartPortSplitGraph G
          (data.order)).Dart := ⟨(a, b), hmem⟩
      apply kwLocalAngularSplit_formalRoot_coeff_eq_zero_of_repeated
        data selected m
      simpa [selected, SimpleGraph.Dart.edge] using hedge
  · apply kwGraphFormalRoot_coeff_eq_zero_of_offGraph
      (kwOrderedDartPortSplitGraph G (data.order))
      (kwLocalAngularSplitPhase data) m edge hmem
    omega

end StatMech.FrontierA
