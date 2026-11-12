/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardArbitraryValenceReduction
import Code.FrontierA.KacWardPrincipalAngleMultiaffine










namespace StatMech.FrontierA

open SimpleGraph
open scoped BigOperators


noncomputable def kwAngularSplitSpinorGauge
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (d : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart) : Complex :=
  if kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm then 1
  else if kwOrderedPortRank (kwAngularPortOrder embedding) d.fst <
      kwOrderedPortRank (kwAngularPortOrder embedding) d.snd then
    Complex.I
  else 1

theorem kwAngularSplitSpinorGauge_ne_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (d : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart) :
    kwAngularSplitSpinorGauge embedding d ≠ 0 := by
  classical
  unfold kwAngularSplitSpinorGauge
  by_cases hmatching :
      kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm
  · simp [hmatching]
  · by_cases hincreasing :
        kwOrderedPortRank (kwAngularPortOrder embedding) d.fst <
          kwOrderedPortRank (kwAngularPortOrder embedding) d.snd
    · simp [hmatching, hincreasing]
    · simp [hmatching, hincreasing]



noncomputable def kwAngularSplitSpinorDirection
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (d : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart) : Complex :=
  if kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm then
    (kwPortAngleRoot embedding d.fst) ^ 2
  else if kwOrderedPortRank (kwAngularPortOrder embedding) d.fst <
      kwOrderedPortRank (kwAngularPortOrder embedding) d.snd then
    -1
  else 1

theorem kwPortAngleRoot_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (p : KWDartPort G) :
    kwPortAngleRoot embedding p ^ 2 =
      Complex.exp ((((embedding.dartAngle (kwDartOfPort G p)).toReal : Real) :
        Complex) * Complex.I) := by
  unfold kwPortAngleRoot
  rw [pow_two, ← Complex.exp_add]
  congr 1
  ring

theorem kwPortAngleRoot_sq_symm
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (d : G.Dart) :
    kwPortAngleRoot embedding (kwPortOfDart G d.symm) ^ 2 =
      -(kwPortAngleRoot embedding (kwPortOfDart G d) ^ 2) := by
  rw [kwPortAngleRoot_sq, kwPortAngleRoot_sq]
  simp only [kwDartOfPort_portOfDart]
  unfold KWStraightLineEmbedding.dartAngle
  rw [Complex.arg_coe_angle_toReal_eq_arg,
    Complex.arg_coe_angle_toReal_eq_arg]
  let z := embedding.vertex d.snd - embedding.vertex d.fst
  have hz : z ≠ 0 := by
    simpa only [z] using embedding.dartVector_ne_zero d
  have hsymm : embedding.vertex d.fst - embedding.vertex d.snd = -z := by
    dsimp only [z]
    ring
  change Complex.exp
      ((Complex.arg (embedding.vertex d.fst - embedding.vertex d.snd) :
        Complex) * Complex.I) =
    -Complex.exp ((Complex.arg z : Complex) * Complex.I)
  rw [hsymm]
  have hzNorm : (norm z : Complex) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hz)
  have hneg := Complex.norm_mul_exp_arg_mul_I (-z)
  have hpos := Complex.norm_mul_exp_arg_mul_I z
  rw [norm_neg] at hneg
  apply (mul_left_cancel₀ hzNorm)
  calc
    (norm z : Complex) *
          Complex.exp ((Complex.arg (-z) : Complex) * Complex.I) =
        -z := hneg
    _ = -((norm z : Complex) *
          Complex.exp ((Complex.arg z : Complex) * Complex.I)) := by rw [hpos]
    _ = (norm z : Complex) *
          (-Complex.exp ((Complex.arg z : Complex) * Complex.I)) := by ring

theorem kwPortAngleRoot_sq_of_matching
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) {p q : KWDartPort G}
    (hmatching : kwDartOfPort G q = (kwDartOfPort G p).symm) :
    kwPortAngleRoot embedding q ^ 2 =
      -(kwPortAngleRoot embedding p ^ 2) := by
  have hq : q = kwPortOfDart G (kwDartOfPort G p).symm := by
    apply kwDartOfPort_injective G
    simpa using hmatching
  rw [hq, kwPortAngleRoot_sq_symm]
  simp


theorem kwAngularSplitSpinorDirection_symm
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (d : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart) :
    kwAngularSplitSpinorDirection embedding d.symm =
      -kwAngularSplitSpinorDirection embedding d := by
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
    unfold kwAngularSplitSpinorDirection
    rw [if_pos hmatching', if_pos hmatching]
    change kwPortAngleRoot embedding d.snd ^ 2 =
      -(kwPortAngleRoot embedding d.fst ^ 2)
    exact kwPortAngleRoot_sq_of_matching embedding hmatching
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
    · have hlt : kwOrderedPortRank (kwAngularPortOrder embedding) d.fst <
          kwOrderedPortRank (kwAngularPortOrder embedding) d.snd := by omega
      have hnrev : ¬kwOrderedPortRank (kwAngularPortOrder embedding) d.snd <
          kwOrderedPortRank (kwAngularPortOrder embedding) d.fst := by omega
      unfold kwAngularSplitSpinorDirection
      change (if kwDartOfPort G d.fst = (kwDartOfPort G d.snd).symm then _
          else if kwOrderedPortRank (kwAngularPortOrder embedding) d.snd <
            kwOrderedPortRank (kwAngularPortOrder embedding) d.fst then -1 else 1) =
        -(if kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm then _
          else if kwOrderedPortRank (kwAngularPortOrder embedding) d.fst <
            kwOrderedPortRank (kwAngularPortOrder embedding) d.snd then -1 else 1)
      rw [if_neg hmatchingSwap, if_neg hmatching,
        if_neg hnrev, if_pos hlt]
      norm_num
    · have hnlt : ¬kwOrderedPortRank (kwAngularPortOrder embedding) d.fst <
          kwOrderedPortRank (kwAngularPortOrder embedding) d.snd := by omega
      have hrev : kwOrderedPortRank (kwAngularPortOrder embedding) d.snd <
          kwOrderedPortRank (kwAngularPortOrder embedding) d.fst := by omega
      unfold kwAngularSplitSpinorDirection
      change (if kwDartOfPort G d.fst = (kwDartOfPort G d.snd).symm then _
          else if kwOrderedPortRank (kwAngularPortOrder embedding) d.snd <
            kwOrderedPortRank (kwAngularPortOrder embedding) d.fst then -1 else 1) =
        -(if kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm then _
          else if kwOrderedPortRank (kwAngularPortOrder embedding) d.fst <
            kwOrderedPortRank (kwAngularPortOrder embedding) d.snd then -1 else 1)
      rw [if_neg hmatchingSwap, if_neg hmatching,
        if_pos hrev, if_neg hnlt]


noncomputable def kwAngularSplitSpinorPhase
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :=
  kwPhaseGauge (kwAngularSplitSpinorGauge embedding)
    (kwAngularSplitPhase embedding)

theorem kwAngularSplitSpinorDirection_ne_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (d : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart) :
    kwAngularSplitSpinorDirection embedding d ≠ 0 := by
  classical
  unfold kwAngularSplitSpinorDirection
  by_cases hmatching :
      kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm
  · rw [if_pos hmatching]
    exact pow_ne_zero 2 (kwPortAngleRoot_ne_zero embedding d.fst)
  · rw [if_neg hmatching]
    split <;> norm_num



theorem kwAngularSplitSpinorPhase_sq_mul_direction
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (d e : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart)
    (hconnect : d.snd = e.fst) (hne : d.edge ≠ e.edge) :
    kwAngularSplitSpinorPhase embedding d e ^ 2 *
        kwAngularSplitSpinorDirection embedding d =
      kwAngularSplitSpinorDirection embedding e := by
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
    · have hmatchRoot : kwPortAngleRoot embedding e.fst ^ 2 =
          -(kwPortAngleRoot embedding d.fst ^ 2) := by
        apply kwPortAngleRoot_sq_of_matching embedding
        rw [← hconnect]
        exact hd
      have hr : kwPortAngleRoot embedding e.fst ≠ 0 :=
        kwPortAngleRoot_ne_zero embedding e.fst
      by_cases hinc : kwOrderedPortRank (kwAngularPortOrder embedding) e.fst <
          kwOrderedPortRank (kwAngularPortOrder embedding) e.snd
      · simp [kwAngularSplitSpinorPhase, kwPhaseGauge,
          kwAngularSplitSpinorGauge, kwAngularSplitSpinorDirection,
          kwAngularSplitPhase, hd, he, hinc]
        field_simp
        rw [hmatchRoot]
        norm_num [Complex.I_sq]
      · simp [kwAngularSplitSpinorPhase, kwPhaseGauge,
          kwAngularSplitSpinorGauge, kwAngularSplitSpinorDirection,
          kwAngularSplitPhase, hd, he, hinc]
        field_simp
        rw [hmatchRoot]
        norm_num [Complex.I_sq]
  · by_cases he : kwDartOfPort G e.snd = (kwDartOfPort G e.fst).symm
    · by_cases hinc : kwOrderedPortRank (kwAngularPortOrder embedding) d.fst <
          kwOrderedPortRank (kwAngularPortOrder embedding) d.snd
      · simp [kwAngularSplitSpinorPhase, kwPhaseGauge,
          kwAngularSplitSpinorGauge, kwAngularSplitSpinorDirection,
          kwAngularSplitPhase, hd, he, hinc]
        rw [mul_pow, Complex.I_sq]
        ring
      · simp [kwAngularSplitSpinorPhase, kwPhaseGauge,
          kwAngularSplitSpinorGauge, kwAngularSplitSpinorDirection,
          kwAngularSplitPhase, hd, he, hinc]
    · let di : KWOrderedInternalSplitDart G
          (kwAngularPortOrder embedding) := ⟨d, hd⟩
      let ei : KWOrderedInternalSplitDart G
          (kwAngularPortOrder embedding) := ⟨e, he⟩
      have hstep : KWOrderedInternalDartStep G
          (kwAngularPortOrder embedding) di ei := by
        exact ⟨hconnect, hne⟩
      by_cases hinc : kwOrderedPortRank (kwAngularPortOrder embedding) d.fst <
          kwOrderedPortRank (kwAngularPortOrder embedding) d.snd
      · have heinc : kwOrderedPortRank (kwAngularPortOrder embedding) e.fst <
            kwOrderedPortRank (kwAngularPortOrder embedding) e.snd := by
          simpa only [di, ei] using
            (kwOrderedInternalDartStep_rank_lt G
              (kwAngularPortOrder embedding) hstep hinc)
        simp [kwAngularSplitSpinorPhase, kwPhaseGauge,
          kwAngularSplitSpinorGauge, kwAngularSplitSpinorDirection,
          kwAngularSplitPhase, hd, he, hinc, heinc]
      · have hddata' := kwOrderedInternalSplitDart_adj_data G
          (kwAngularPortOrder embedding) di
        have hddata : d.fst.1 = d.snd.1 ∧
            (kwOrderedPortRank (kwAngularPortOrder embedding) d.fst + 1 =
                kwOrderedPortRank (kwAngularPortOrder embedding) d.snd ∨
              kwOrderedPortRank (kwAngularPortOrder embedding) d.snd + 1 =
                kwOrderedPortRank (kwAngularPortOrder embedding) d.fst) := by
          simpa only [di] using hddata'
        have hddec : kwOrderedPortRank (kwAngularPortOrder embedding) d.snd <
            kwOrderedPortRank (kwAngularPortOrder embedding) d.fst := by
          rcases hddata.2 with h | h <;> omega
        have hedec : kwOrderedPortRank (kwAngularPortOrder embedding) e.snd <
            kwOrderedPortRank (kwAngularPortOrder embedding) e.fst := by
          simpa only [di, ei] using
            (kwOrderedInternalDartStep_rank_gt G
              (kwAngularPortOrder embedding) hstep hddec)
        have heinc : ¬kwOrderedPortRank (kwAngularPortOrder embedding) e.fst <
            kwOrderedPortRank (kwAngularPortOrder embedding) e.snd := by omega
        simp [kwAngularSplitSpinorPhase, kwPhaseGauge,
          kwAngularSplitSpinorGauge, kwAngularSplitSpinorDirection,
          kwAngularSplitPhase, hd, he, hinc, heinc]


theorem kwAngularSplitSpinorPath_sq_mul_direction
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    {N : Nat}
    (path : Fin (N + 1) →
      (kwOrderedDartPortSplitGraph G
        (kwAngularPortOrder embedding)).Dart)
    (hvalid : ∀ j : Fin N,
      (path j.castSucc).snd = (path j.succ).fst ∧
        (path j.castSucc).edge ≠ (path j.succ).edge) :
    (∏ j : Fin N, kwAngularSplitSpinorPhase embedding
        (path j.castSucc) (path j.succ)) ^ 2 *
        kwAngularSplitSpinorDirection embedding (path 0) =
      kwAngularSplitSpinorDirection embedding (path (Fin.last N)) := by
  classical
  let phase : Fin N → Complex := fun j ↦
    kwAngularSplitSpinorPhase embedding (path j.castSucc) (path j.succ)
  let direction : Fin (N + 1) → Complex := fun j ↦
    kwAngularSplitSpinorDirection embedding (path j)
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
        exact kwAngularSplitSpinorPhase_sq_mul_direction embedding _ _
          (hvalid j).1 (hvalid j).2
  have hprefix_ne : prefixProd ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact kwAngularSplitSpinorDirection_ne_zero embedding _
  have hsuffix_eq : suffixProd =
      prefixProd * kwAngularSplitSpinorDirection embedding (path (Fin.last N)) /
        kwAngularSplitSpinorDirection embedding (path 0) := by
    have hfullCast := Fin.prod_univ_castSucc direction
    have hfullSucc := Fin.prod_univ_succ direction
    have hzero := kwAngularSplitSpinorDirection_ne_zero embedding (path 0)
    apply (mul_left_cancel₀ hzero)
    field_simp
    rw [← hfullSucc, ← hfullCast]
  change (∏ j : Fin N, phase j) ^ 2 * direction 0 =
    direction (Fin.last N)
  have hzero : direction 0 ≠ 0 :=
    kwAngularSplitSpinorDirection_ne_zero embedding (path 0)
  apply (mul_left_cancel₀ hprefix_ne)
  calc
    prefixProd * ((∏ j : Fin N, phase j) ^ 2 * direction 0) =
        ((∏ j : Fin N, phase j) ^ 2 * prefixProd) * direction 0 := by
          ring
    _ = suffixProd * direction 0 := by rw [hprod]
    _ = (prefixProd * direction (Fin.last N) / direction 0) *
        direction 0 := by rw [hsuffix_eq]
    _ = prefixProd * direction (Fin.last N) := by field_simp



theorem kwAngularSplitSpinorPath_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    {N : Nat}
    (path : Fin (N + 1) →
      (kwOrderedDartPortSplitGraph G
        (kwAngularPortOrder embedding)).Dart)
    (hend : path (Fin.last N) = (path 0).symm)
    (hvalid : ∀ j : Fin N,
      (path j.castSucc).snd = (path j.succ).fst ∧
        (path j.castSucc).edge ≠ (path j.succ).edge) :
    (∏ j : Fin N, kwAngularSplitSpinorPhase embedding
      (path j.castSucc) (path j.succ)) ^ 2 = -1 := by
  have htel := kwAngularSplitSpinorPath_sq_mul_direction embedding path hvalid
  rw [hend, kwAngularSplitSpinorDirection_symm] at htel
  have hne := kwAngularSplitSpinorDirection_ne_zero embedding (path 0)
  apply (mul_right_cancel₀ hne)
  simpa only [neg_mul, one_mul] using htel


theorem kwAngularSplitSpinorPhase_reverse
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (d e : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart)
    (hconnect : d.snd = e.fst) (hne : d.edge ≠ e.edge) :
    kwAngularSplitSpinorPhase embedding e.symm d.symm =
      (kwAngularSplitSpinorPhase embedding d e)⁻¹ := by
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
    · by_cases hinc : kwOrderedPortRank (kwAngularPortOrder embedding) e.fst <
          kwOrderedPortRank (kwAngularPortOrder embedding) e.snd
      · have hnback : ¬kwOrderedPortRank (kwAngularPortOrder embedding) e.snd <
            kwOrderedPortRank (kwAngularPortOrder embedding) e.fst := by omega
        simp [kwAngularSplitSpinorPhase, kwPhaseGauge,
          kwAngularSplitSpinorGauge, kwAngularSplitPhase,
          herev, hd, he, hinc, hnback]
        rw [hconnect]
        field_simp
        norm_num [Complex.I_sq]
      · have eadj := e.adj
        rw [kwOrderedDartPortSplitGraph_adj] at eadj
        have eranks := (eadj.resolve_left he).2
        have hback : kwOrderedPortRank (kwAngularPortOrder embedding) e.snd <
            kwOrderedPortRank (kwAngularPortOrder embedding) e.fst := by
          rcases eranks with h | h <;> omega
        simp [kwAngularSplitSpinorPhase, kwPhaseGauge,
          kwAngularSplitSpinorGauge, kwAngularSplitPhase,
          herev, hd, he, hinc, hback]
        rw [hconnect]
        field_simp
  · by_cases he : kwDartOfPort G e.snd = (kwDartOfPort G e.fst).symm
    · by_cases hinc : kwOrderedPortRank (kwAngularPortOrder embedding) d.fst <
          kwOrderedPortRank (kwAngularPortOrder embedding) d.snd
      · have hnback : ¬kwOrderedPortRank (kwAngularPortOrder embedding) e.fst <
            kwOrderedPortRank (kwAngularPortOrder embedding) d.fst := by
          rw [← hconnect]
          omega
        simp [kwAngularSplitSpinorPhase, kwPhaseGauge,
          kwAngularSplitSpinorGauge, kwAngularSplitPhase,
          hdrev, hd, he, hinc]
        rw [hconnect]
        simp [hnback]
        ring
      · have dadj := d.adj
        rw [kwOrderedDartPortSplitGraph_adj] at dadj
        have dranks := (dadj.resolve_left hd).2
        have dback : kwOrderedPortRank (kwAngularPortOrder embedding) d.snd <
            kwOrderedPortRank (kwAngularPortOrder embedding) d.fst := by
          rcases dranks with h | h <;> omega
        have hback : kwOrderedPortRank (kwAngularPortOrder embedding) e.fst <
            kwOrderedPortRank (kwAngularPortOrder embedding) d.fst := by
          rw [← hconnect]
          exact dback
        simp [kwAngularSplitSpinorPhase, kwPhaseGauge,
          kwAngularSplitSpinorGauge, kwAngularSplitPhase,
          hdrev, hd, he, hinc, dback]
        rw [hconnect]
        calc
          -(Complex.I * (kwPortAngleRoot embedding e.fst)⁻¹ * Complex.I) =
              -(Complex.I ^ 2 * (kwPortAngleRoot embedding e.fst)⁻¹) := by ring
          _ = (kwPortAngleRoot embedding e.fst)⁻¹ := by
            rw [Complex.I_sq]
            ring
    · let di : KWOrderedInternalSplitDart G
          (kwAngularPortOrder embedding) := ⟨d, hd⟩
      let ei : KWOrderedInternalSplitDart G
          (kwAngularPortOrder embedding) := ⟨e, he⟩
      have hstep : KWOrderedInternalDartStep G
          (kwAngularPortOrder embedding) di ei := ⟨hconnect, hne⟩
      by_cases hinc : kwOrderedPortRank (kwAngularPortOrder embedding) d.fst <
          kwOrderedPortRank (kwAngularPortOrder embedding) d.snd
      · have heinc : kwOrderedPortRank (kwAngularPortOrder embedding) e.fst <
            kwOrderedPortRank (kwAngularPortOrder embedding) e.snd := by
          simpa only [di, ei] using
            (kwOrderedInternalDartStep_rank_lt G
              (kwAngularPortOrder embedding) hstep hinc)
        have hdback : ¬kwOrderedPortRank (kwAngularPortOrder embedding) d.snd <
            kwOrderedPortRank (kwAngularPortOrder embedding) d.fst := by omega
        have heback : ¬kwOrderedPortRank (kwAngularPortOrder embedding) e.snd <
            kwOrderedPortRank (kwAngularPortOrder embedding) e.fst := by omega
        simp [kwAngularSplitSpinorPhase, kwPhaseGauge,
          kwAngularSplitSpinorGauge, kwAngularSplitPhase,
          hdrev, herev, hd, he, hinc, heinc, hdback, heback]
      · have hddata' := kwOrderedInternalSplitDart_adj_data G
          (kwAngularPortOrder embedding) di
        have hddata : d.fst.1 = d.snd.1 ∧
            (kwOrderedPortRank (kwAngularPortOrder embedding) d.fst + 1 =
                kwOrderedPortRank (kwAngularPortOrder embedding) d.snd ∨
              kwOrderedPortRank (kwAngularPortOrder embedding) d.snd + 1 =
                kwOrderedPortRank (kwAngularPortOrder embedding) d.fst) := by
          simpa only [di] using hddata'
        have hddec : kwOrderedPortRank (kwAngularPortOrder embedding) d.snd <
            kwOrderedPortRank (kwAngularPortOrder embedding) d.fst := by
          rcases hddata.2 with h | h <;> omega
        have hedec : kwOrderedPortRank (kwAngularPortOrder embedding) e.snd <
            kwOrderedPortRank (kwAngularPortOrder embedding) e.fst := by
          simpa only [di, ei] using
            (kwOrderedInternalDartStep_rank_gt G
              (kwAngularPortOrder embedding) hstep hddec)
        have heinc : ¬kwOrderedPortRank (kwAngularPortOrder embedding) e.fst <
            kwOrderedPortRank (kwAngularPortOrder embedding) e.snd := by omega
        simp [kwAngularSplitSpinorPhase, kwPhaseGauge,
          kwAngularSplitSpinorGauge, kwAngularSplitPhase,
          hdrev, herev, hd, he, hinc, heinc, hddec, hedec]


theorem kwAngularSplitSpinorLoop_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    {n : Nat} [NeZero n]
    (loop : Fin n → (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart)
    (hvalid : ∀ k : Fin n,
      (loop k).snd = (loop (k + 1)).fst ∧
        (loop k).edge ≠ (loop (k + 1)).edge) :
    (∏ k : Fin n, kwAngularSplitSpinorPhase embedding
      (loop k) (loop (k + 1))) ^ 2 = 1 := by
  classical
  let phase : Fin n → Complex := fun k ↦
    kwAngularSplitSpinorPhase embedding (loop k) (loop (k + 1))
  let direction : Fin n → Complex := fun k ↦
    kwAngularSplitSpinorDirection embedding (loop k)
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
        exact kwAngularSplitSpinorPhase_sq_mul_direction embedding _ _
          (hvalid k).1 (hvalid k).2
  have hreindex : (∏ k : Fin n, direction (k + 1)) =
      ∏ k : Fin n, direction k := by
    exact Equiv.prod_comp (Equiv.addRight (1 : Fin n)) direction
  rw [hreindex] at hprod
  have hdirection : (∏ k : Fin n, direction k) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k _
    exact kwAngularSplitSpinorDirection_ne_zero embedding _
  change (∏ k : Fin n, phase k) ^ 2 = 1
  apply mul_right_cancel₀ hdirection
  simpa only [one_mul] using hprod



theorem kwAngularSplitGraphLoopWeight_surgery_sign
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    {n : Nat} [NeZero n]
    (weight : Sym2 (KWDartPort G) → Complex)
    (selected : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart)
    (loop : Fin n → (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart)
    (hboth : (∃ i, loop i = selected) ∧ ∃ j, loop j = selected.symm) :
    StatMech.Onsager.ons_loopWeight
        (kwGraphTransition (kwOrderedDartPortSplitGraph G
          (kwAngularPortOrder embedding)) weight
          (kwAngularSplitSpinorPhase embedding))
        (StatMech.Onsager.ons_surgery selected SimpleGraph.Dart.symm loop) =
      -StatMech.Onsager.ons_loopWeight
        (kwGraphTransition (kwOrderedDartPortSplitGraph G
          (kwAngularPortOrder embedding)) weight
          (kwAngularSplitSpinorPhase embedding)) loop := by
  convert kwGraphLoopWeight_surgery_sign
    (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
    weight (kwAngularSplitSpinorPhase embedding)
    (kwAngularSplitSpinorPath_sq embedding)
    (fun d e hconnect hne ↦
      kwAngularSplitSpinorPhase_reverse embedding d e hconnect hne)
    selected loop hboth using 3


theorem kwAngularSplitSpinor_formalRoot_coeff_eq_zero_of_repeated
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (selected : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart)
    (m : Sym2 (KWDartPort G) →₀ Nat)
    (hrepeated : 2 ≤ m selected.edge) :
    MvPowerSeries.coeff m
      (kwGraphFormalRoot
        (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
        (kwAngularSplitSpinorPhase embedding)) = 0 := by
  apply kw_spinorGraph_formalRoot_coeff_eq_zero_of_repeated
    (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
    (kwAngularSplitSpinorPhase embedding)
    (kwAngularSplitSpinorPath_sq embedding)
    (fun d e hconnect hne ↦
      kwAngularSplitSpinorPhase_reverse embedding d e hconnect hne)
    (kwAngularSplitSpinorLoop_sq embedding)
    selected m hrepeated



theorem kwAngularSplit_formalRoot_coeff_eq_zero_of_repeated
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (selected : (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).Dart)
    (m : Sym2 (KWDartPort G) →₀ Nat)
    (hrepeated : 2 ≤ m selected.edge) :
    MvPowerSeries.coeff m
      (kwGraphFormalRoot
        (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
        (kwAngularSplitPhase embedding)) = 0 := by
  have hgauge := kwGraphFormalRoot_phaseGauge
    (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
    (kwAngularSplitPhase embedding)
    (kwAngularSplitSpinorGauge embedding)
    (kwAngularSplitSpinorGauge_ne_zero embedding)
  rw [← hgauge]
  exact kwAngularSplitSpinor_formalRoot_coeff_eq_zero_of_repeated
    embedding selected m hrepeated



theorem kwAngularSplit_formalRoot_coeff_eq_zero_of_not_squarefree
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (m : Sym2 (KWDartPort G) →₀ Nat)
    (hm : ¬StatMech.Onsager.ons_IsSquarefreeExponent m) :
    MvPowerSeries.coeff m
      (kwGraphFormalRoot
        (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
        (kwAngularSplitPhase embedding)) = 0 := by
  classical
  obtain ⟨edge, hedge⟩ :=
    (StatMech.Onsager.ons_not_isSquarefreeExponent_iff m).mp hm
  by_cases hmem : edge ∈
      (kwOrderedDartPortSplitGraph G
        (kwAngularPortOrder embedding)).edgeFinset
  · induction edge using Sym2.inductionOn with
    | _ a b =>
      rw [SimpleGraph.mem_edgeFinset] at hmem
      let selected : (kwOrderedDartPortSplitGraph G
          (kwAngularPortOrder embedding)).Dart := ⟨(a, b), hmem⟩
      apply kwAngularSplit_formalRoot_coeff_eq_zero_of_repeated
        embedding selected m
      simpa [selected, SimpleGraph.Dart.edge] using hedge
  · apply kwGraphFormalRoot_coeff_eq_zero_of_offGraph
      (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
      (kwAngularSplitPhase embedding) m edge hmem
    omega



theorem kacWard_original_of_angularSplit_unitCycleLog_closed
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V → Complex)
    (hunit : KWGraphUnitCycleLog
      (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
      (kwAngularSplitPhase embedding)) :
    (1 - kwGraphTransition G weight embedding.turnPhase).det =
      (kwEvenPolynomial G weight) ^ 2 := by
  exact kacWard_original_of_angularSplit_unitCycleLog embedding weight hunit
    (kwAngularSplit_formalRoot_coeff_eq_zero_of_not_squarefree embedding)

end StatMech.FrontierA
