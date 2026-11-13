/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartInjective
import Code.Lattice.DartOrbit
import Code.Lattice.TurningNumber
import Code.Lattice.CornerBalance

open SimpleGraph Function

namespace StatMech

namespace Lattice







open Classical in


noncomputable def straightStepCount (K : Set (Site 2)) (e : Dart) (p : ℕ) : ℤ :=
  ((Finset.range p).filter (fun i => turnZ K ((dartNext K)^[i] e) = 0)).card









theorem orbitStep_partition (K : Set (Site 2)) (e : Dart) (p : ℕ) :
    rightCornerCount K e p + straightStepCount K e p + leftCornerCount K e p = (p : ℤ) := by
  classical
  unfold rightCornerCount straightStepCount leftCornerCount
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter]
  push_cast
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [show ((p : ℤ)) = ∑ _i ∈ Finset.range p, (1 : ℤ) by simp]
  apply Finset.sum_congr rfl
  intro i _
  rcases turnZ_mem K ((dartNext K)^[i] e) with h | h | h <;> rw [h] <;> norm_num














theorem totalTurnZ_eq_rl (K : Set (Site 2)) (e : Dart) (p : ℕ) {r l : ℤ}
    (hr : rightCornerCount K e p = r) (hl : leftCornerCount K e p = l) :
    totalTurnZ K e p = r - l := by
  rw [totalTurnZ_eq_cornerBalance, hr, hl]


















theorem totalTurnZ_neg_four_of_convex (K : Set (Site 2)) (e : Dart) (p : ℕ)
    (hr : rightCornerCount K e p = 0) (hl : leftCornerCount K e p = 4) :
    totalTurnZ K e p = -4 := by
  rw [totalTurnZ_eq_rl K e p hr hl]; ring



theorem totalTurnZ_four_of_reflexFree (K : Set (Site 2)) (e : Dart) (p : ℕ)
    (hr : rightCornerCount K e p = 4) (hl : leftCornerCount K e p = 0) :
    totalTurnZ K e p = 4 := by
  rw [totalTurnZ_eq_rl K e p hr hl]; ring









theorem turningIsFullRevolution_of_corner_diff_four (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (h : rightCornerCount K a.1 (dartOrbitPeriod K a) -
          leftCornerCount K a.1 (dartOrbitPeriod K a) = 4 ∨
        rightCornerCount K a.1 (dartOrbitPeriod K a) -
          leftCornerCount K a.1 (dartOrbitPeriod K a) = -4) :
    TurningIsFullRevolution K a :=
  turningIsFullRevolution_of_cornerBalance K a h



theorem turningIsFullRevolution_of_canonical_convex (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hr : rightCornerCount K a.1 (dartOrbitPeriod K a) = 0)
    (hl : leftCornerCount K a.1 (dartOrbitPeriod K a) = 4) :
    TurningIsFullRevolution K a := by
  apply turningIsFullRevolution_of_corner_diff_four
  right; rw [hr, hl]; ring



theorem turningIsFullRevolution_of_canonical_reflexFree (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hr : rightCornerCount K a.1 (dartOrbitPeriod K a) = 4)
    (hl : leftCornerCount K a.1 (dartOrbitPeriod K a) = 0) :
    TurningIsFullRevolution K a := by
  apply turningIsFullRevolution_of_corner_diff_four
  left; rw [hr, hl]; ring



















theorem earTurnReplacement (K K' : Set (Site 2)) (e e' : Dart) (p p' : ℕ)
    {r l r' l' : ℤ}
    (hr : rightCornerCount K e p = r) (hl : leftCornerCount K e p = l)
    (hr' : rightCornerCount K' e' p' = r') (hl' : leftCornerCount K' e' p' = l')
    (hbal : r - l = r' - l') :
    totalTurnZ K e p = totalTurnZ K' e' p' := by
  rw [totalTurnZ_eq_rl K e p hr hl, totalTurnZ_eq_rl K' e' p' hr' hl', hbal]







theorem turningIsFullRevolution_of_balance_eq_base (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hbase : rightCornerCount K a.1 (dartOrbitPeriod K a) -
        leftCornerCount K a.1 (dartOrbitPeriod K a) =
      rightCornerCount unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) -
        leftCornerCount unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase)) :
    TurningIsFullRevolution K a := by
  apply turningIsFullRevolution_of_corner_diff_four
  right
  
  have hbal : rightCornerCount unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) -
      leftCornerCount unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = -4 := by
    have h := unitCell_totalTurnZ_four
    rw [show (ucBase).1 = ucDart0 from rfl] at *
    rw [unitCell_orbitPeriod_eq_four] at hbase ⊢
    rw [← totalTurnZ_eq_cornerBalance]
    exact h
  rw [hbase, hbal]


















def SimplePolygonCornerBalance (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    Prop :=
  rightCornerCount K a.1 (dartOrbitPeriod K a) -
      leftCornerCount K a.1 (dartOrbitPeriod K a) = 4 ∨
    rightCornerCount K a.1 (dartOrbitPeriod K a) -
      leftCornerCount K a.1 (dartOrbitPeriod K a) = -4






theorem turningIsFullRevolution_of_simplePolygon (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (h : SimplePolygonCornerBalance K a) :
    TurningIsFullRevolution K a :=
  turningIsFullRevolution_of_corner_diff_four K a h






theorem simplePolygonCornerBalance_iff (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    SimplePolygonCornerBalance K a ↔ TurningIsFullRevolution K a := by
  unfold SimplePolygonCornerBalance TurningIsFullRevolution
  rw [totalTurnZ_eq_cornerBalance]




theorem unitCell_simplePolygonCornerBalance :
    SimplePolygonCornerBalance unitCell ucBase :=
  (simplePolygonCornerBalance_iff unitCell ucBase).mpr unitCell_turningIsFullRevolution












noncomputable def domino : Set (Site 2) := {![0, 0], ![1, 0]}

theorem domino_eq_insert : domino = insert (![0, 0] : Site 2) {![1, 0]} := rfl

theorem domino_finite : domino.Finite := by
  rw [domino_eq_insert]; exact (Set.finite_singleton _).insert _

theorem mem_domino_iff (v : Site 2) :
    v ∈ domino ↔ v = ![0, 0] ∨ v = ![1, 0] := by
  rw [domino_eq_insert, Set.mem_insert_iff, Set.mem_singleton_iff]

theorem origin_mem_domino : (![0, 0] : Site 2) ∈ domino := by rw [mem_domino_iff]; exact Or.inl rfl
theorem one_mem_domino : (![1, 0] : Site 2) ∈ domino := by rw [mem_domino_iff]; exact Or.inr rfl


theorem mem_domino_coord_iff (v : Site 2) :
    v ∈ domino ↔ (v 0 = 0 ∧ v 1 = 0) ∨ (v 0 = 1 ∧ v 1 = 0) := by
  rw [mem_domino_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl ⟨by rw [h]; simp, by rw [h]; simp⟩
    · exact Or.inr ⟨by rw [h]; simp, by rw [h]; simp⟩
  · rintro (⟨h0, h1⟩ | ⟨h0, h1⟩)
    · left; funext i; fin_cases i <;> simpa
    · right; funext i; fin_cases i <;> simpa


theorem not_mem_domino (v : Site 2)
    (h : ¬ ((v 0 = 0 ∧ v 1 = 0) ∨ (v 0 = 1 ∧ v 1 = 0))) : v ∉ domino := by
  rw [mem_domino_coord_iff]; exact h



noncomputable def dmD0 : Dart := mkDart ![0, 0] ![0, -1] unitWt_my
noncomputable def dmD1 : Dart := mkDart ![0, 0] ![-1, 0] unitWt_mx
noncomputable def dmD2 : Dart := mkDart ![0, 0] ![0, 1] unitWt_py
noncomputable def dmD3 : Dart := mkDart ![1, 0] ![0, 1] unitWt_py
noncomputable def dmD4 : Dart := mkDart ![1, 0] ![1, 0] unitWt_px
noncomputable def dmD5 : Dart := mkDart ![1, 0] ![0, -1] unitWt_my



theorem dmD0_tail : dmD0.tail = ![0, 0] := rfl
theorem dmD1_tail : dmD1.tail = ![0, 0] := rfl
theorem dmD2_tail : dmD2.tail = ![0, 0] := rfl
theorem dmD3_tail : dmD3.tail = ![1, 0] := rfl
theorem dmD4_tail : dmD4.tail = ![1, 0] := rfl
theorem dmD5_tail : dmD5.tail = ![1, 0] := rfl

theorem dmD0_dir : dmD0.dir = ![0, -1] := by rw [dmD0, mkDart_dir]
theorem dmD1_dir : dmD1.dir = ![-1, 0] := by rw [dmD1, mkDart_dir]
theorem dmD2_dir : dmD2.dir = ![0, 1] := by rw [dmD2, mkDart_dir]
theorem dmD3_dir : dmD3.dir = ![0, 1] := by rw [dmD3, mkDart_dir]
theorem dmD4_dir : dmD4.dir = ![1, 0] := by rw [dmD4, mkDart_dir]
theorem dmD5_dir : dmD5.dir = ![0, -1] := by rw [dmD5, mkDart_dir]

theorem dmD0_head : dmD0.head = ![0, -1] := by
  rw [dmD0, mkDart_head]; funext i; fin_cases i <;> simp
theorem dmD1_head : dmD1.head = ![-1, 0] := by
  rw [dmD1, mkDart_head]; funext i; fin_cases i <;> simp
theorem dmD2_head : dmD2.head = ![0, 1] := by
  rw [dmD2, mkDart_head]; funext i; fin_cases i <;> simp
theorem dmD3_head : dmD3.head = ![1, 1] := by
  rw [dmD3, mkDart_head]; funext i; fin_cases i <;> simp
theorem dmD4_head : dmD4.head = ![2, 0] := by
  rw [dmD4, mkDart_head]; funext i; fin_cases i <;> simp
theorem dmD5_head : dmD5.head = ![1, -1] := by
  rw [dmD5, mkDart_head]; funext i; fin_cases i <;> simp



theorem dmD0_boundary : IsBoundaryDart domino dmD0 :=
  ⟨by rw [dmD0_tail]; exact origin_mem_domino,
   by rw [dmD0_head]; exact not_mem_domino _ (by decide)⟩



theorem dmD0_travel : -rot90Fun dmD0.dir = ![-1, 0] := by
  rw [dmD0_dir, rot90Fun_apply]; funext i; fin_cases i <;> simp
theorem dmD1_travel : -rot90Fun dmD1.dir = ![0, 1] := by
  rw [dmD1_dir, rot90Fun_apply]; funext i; fin_cases i <;> simp
theorem dmD2_travel : -rot90Fun dmD2.dir = ![1, 0] := by
  rw [dmD2_dir, rot90Fun_apply]; funext i; fin_cases i <;> simp
theorem dmD3_travel : -rot90Fun dmD3.dir = ![1, 0] := by
  rw [dmD3_dir, rot90Fun_apply]; funext i; fin_cases i <;> simp
theorem dmD4_travel : -rot90Fun dmD4.dir = ![0, -1] := by
  rw [dmD4_dir, rot90Fun_apply]; funext i; fin_cases i <;> simp
theorem dmD5_travel : -rot90Fun dmD5.dir = ![-1, 0] := by
  rw [dmD5_dir, rot90Fun_apply]; funext i; fin_cases i <;> simp




theorem dmD0_front_nmem : dmD0.head + (-rot90Fun dmD0.dir) ∉ domino := by
  rw [dmD0_head, dmD0_travel]; exact not_mem_domino _ (by decide)
theorem dmD0_side_nmem : dmD0.tail + (-rot90Fun dmD0.dir) ∉ domino := by
  rw [dmD0_tail, dmD0_travel]; exact not_mem_domino _ (by decide)


theorem dmD1_front_nmem : dmD1.head + (-rot90Fun dmD1.dir) ∉ domino := by
  rw [dmD1_head, dmD1_travel]; exact not_mem_domino _ (by decide)
theorem dmD1_side_nmem : dmD1.tail + (-rot90Fun dmD1.dir) ∉ domino := by
  rw [dmD1_tail, dmD1_travel]; exact not_mem_domino _ (by decide)


theorem dmD2_front_nmem : dmD2.head + (-rot90Fun dmD2.dir) ∉ domino := by
  rw [dmD2_head, dmD2_travel]; exact not_mem_domino _ (by decide)
theorem dmD2_side_mem : dmD2.tail + (-rot90Fun dmD2.dir) ∈ domino := by
  rw [dmD2_tail, dmD2_travel]
  rw [show (![0,0] : Site 2) + ![1,0] = ![1,0] by funext i; fin_cases i <;> simp]
  exact one_mem_domino


theorem dmD3_front_nmem : dmD3.head + (-rot90Fun dmD3.dir) ∉ domino := by
  rw [dmD3_head, dmD3_travel]; exact not_mem_domino _ (by decide)
theorem dmD3_side_nmem : dmD3.tail + (-rot90Fun dmD3.dir) ∉ domino := by
  rw [dmD3_tail, dmD3_travel]; exact not_mem_domino _ (by decide)


theorem dmD4_front_nmem : dmD4.head + (-rot90Fun dmD4.dir) ∉ domino := by
  rw [dmD4_head, dmD4_travel]; exact not_mem_domino _ (by decide)
theorem dmD4_side_nmem : dmD4.tail + (-rot90Fun dmD4.dir) ∉ domino := by
  rw [dmD4_tail, dmD4_travel]; exact not_mem_domino _ (by decide)


theorem dmD5_front_nmem : dmD5.head + (-rot90Fun dmD5.dir) ∉ domino := by
  rw [dmD5_head, dmD5_travel]; exact not_mem_domino _ (by decide)
theorem dmD5_side_mem : dmD5.tail + (-rot90Fun dmD5.dir) ∈ domino := by
  rw [dmD5_tail, dmD5_travel]
  rw [show (![1,0] : Site 2) + ![-1,0] = ![0,0] by funext i; fin_cases i <;> simp]
  exact origin_mem_domino



theorem dmD0_turnZ : turnZ domino dmD0 = -1 := by
  unfold turnZ; rw [if_neg dmD0_front_nmem, if_neg dmD0_side_nmem]
theorem dmD1_turnZ : turnZ domino dmD1 = -1 := by
  unfold turnZ; rw [if_neg dmD1_front_nmem, if_neg dmD1_side_nmem]
theorem dmD2_turnZ : turnZ domino dmD2 = 0 := by
  unfold turnZ; rw [if_neg dmD2_front_nmem, if_pos dmD2_side_mem]
theorem dmD3_turnZ : turnZ domino dmD3 = -1 := by
  unfold turnZ; rw [if_neg dmD3_front_nmem, if_neg dmD3_side_nmem]
theorem dmD4_turnZ : turnZ domino dmD4 = -1 := by
  unfold turnZ; rw [if_neg dmD4_front_nmem, if_neg dmD4_side_nmem]
theorem dmD5_turnZ : turnZ domino dmD5 = 0 := by
  unfold turnZ; rw [if_neg dmD5_front_nmem, if_pos dmD5_side_mem]

theorem dartNext_dmD0 : dartNext domino dmD0 = dmD1 := by
  apply dart_eq_of_tail_dir
  · rw [dartNext_left_tail domino dmD0 dmD0_front_nmem dmD0_side_nmem, dmD0_tail, dmD1_tail]
  · rw [dartNext_left_dir domino dmD0 dmD0_front_nmem dmD0_side_nmem, dmD0_travel, dmD1_dir]
theorem dartNext_dmD1 : dartNext domino dmD1 = dmD2 := by
  apply dart_eq_of_tail_dir
  · rw [dartNext_left_tail domino dmD1 dmD1_front_nmem dmD1_side_nmem, dmD1_tail, dmD2_tail]
  · rw [dartNext_left_dir domino dmD1 dmD1_front_nmem dmD1_side_nmem, dmD1_travel, dmD2_dir]
theorem dartNext_dmD2 : dartNext domino dmD2 = dmD3 := by
  apply dart_eq_of_tail_dir
  · rw [dartNext_straight_tail domino dmD2 dmD2_front_nmem dmD2_side_mem, dmD2_tail, dmD2_travel,
      dmD3_tail]
    funext i; fin_cases i <;> simp
  · rw [dartNext_straight_dir domino dmD2 dmD2_front_nmem dmD2_side_mem, dmD2_dir, dmD3_dir]
theorem dartNext_dmD3 : dartNext domino dmD3 = dmD4 := by
  apply dart_eq_of_tail_dir
  · rw [dartNext_left_tail domino dmD3 dmD3_front_nmem dmD3_side_nmem, dmD3_tail, dmD4_tail]
  · rw [dartNext_left_dir domino dmD3 dmD3_front_nmem dmD3_side_nmem, dmD3_travel, dmD4_dir]
theorem dartNext_dmD4 : dartNext domino dmD4 = dmD5 := by
  apply dart_eq_of_tail_dir
  · rw [dartNext_left_tail domino dmD4 dmD4_front_nmem dmD4_side_nmem, dmD4_tail, dmD5_tail]
  · rw [dartNext_left_dir domino dmD4 dmD4_front_nmem dmD4_side_nmem, dmD4_travel, dmD5_dir]
theorem dartNext_dmD5 : dartNext domino dmD5 = dmD0 := by
  apply dart_eq_of_tail_dir
  · rw [dartNext_straight_tail domino dmD5 dmD5_front_nmem dmD5_side_mem, dmD5_tail, dmD5_travel,
      dmD0_tail]
    funext i; fin_cases i <;> simp
  · rw [dartNext_straight_dir domino dmD5 dmD5_front_nmem dmD5_side_mem, dmD5_dir, dmD0_dir]



theorem iterate_dmD_1 : (dartNext domino)^[1] dmD0 = dmD1 := by
  rw [Function.iterate_one]; exact dartNext_dmD0
theorem iterate_dmD_2 : (dartNext domino)^[2] dmD0 = dmD2 := by
  rw [Function.iterate_succ_apply', iterate_dmD_1, dartNext_dmD1]
theorem iterate_dmD_3 : (dartNext domino)^[3] dmD0 = dmD3 := by
  rw [Function.iterate_succ_apply', iterate_dmD_2, dartNext_dmD2]
theorem iterate_dmD_4 : (dartNext domino)^[4] dmD0 = dmD4 := by
  rw [Function.iterate_succ_apply', iterate_dmD_3, dartNext_dmD3]
theorem iterate_dmD_5 : (dartNext domino)^[5] dmD0 = dmD5 := by
  rw [Function.iterate_succ_apply', iterate_dmD_4, dartNext_dmD4]
theorem iterate_dmD_6 : (dartNext domino)^[6] dmD0 = dmD0 := by
  rw [Function.iterate_succ_apply', iterate_dmD_5, dartNext_dmD5]






theorem domino_totalTurnZ_six : totalTurnZ domino dmD0 6 = -4 := by
  unfold totalTurnZ
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  rw [Function.iterate_zero_apply, dmD0_turnZ]
  rw [iterate_dmD_1, dmD1_turnZ, iterate_dmD_2, dmD2_turnZ, iterate_dmD_3, dmD3_turnZ,
    iterate_dmD_4, dmD4_turnZ, iterate_dmD_5, dmD5_turnZ]
  ring




noncomputable def dmBase : {e : Dart // IsBoundaryDart domino e} := ⟨dmD0, dmD0_boundary⟩


theorem dmBase_isPeriodicPt : Function.IsPeriodicPt (dartNextSub domino) 6 dmBase := by
  unfold Function.IsPeriodicPt Function.IsFixedPt
  apply Subtype.ext
  rw [dartNextSub_iterate_val]
  exact iterate_dmD_6



theorem dmBase_not_periodic_two :
    ¬ Function.IsPeriodicPt (dartNextSub domino) 2 dmBase := by
  intro h
  have h2 : (dartNext domino)^[2] dmD0 = dmD0 := by
    have := congrArg Subtype.val h; rwa [dartNextSub_iterate_val] at this
  rw [iterate_dmD_2] at h2
  have hd : dmD2.dir = dmD0.dir := congrArg Dart.dir h2
  rw [dmD2_dir, dmD0_dir] at hd
  have := congrFun hd 1; simp at this



theorem dmBase_not_periodic_three :
    ¬ Function.IsPeriodicPt (dartNextSub domino) 3 dmBase := by
  intro h
  have h3 : (dartNext domino)^[3] dmD0 = dmD0 := by
    have := congrArg Subtype.val h; rwa [dartNextSub_iterate_val] at this
  rw [iterate_dmD_3] at h3
  have hd : dmD3.dir = dmD0.dir := congrArg Dart.dir h3
  rw [dmD3_dir, dmD0_dir] at hd
  have := congrFun hd 1; simp at this


theorem dmBase_not_fixedPt : ¬ Function.IsFixedPt (dartNextSub domino) dmBase := by
  intro h
  have h1 : dartNext domino dmD0 = dmD0 := by
    have := congrArg Subtype.val h; rwa [dartNextSub_val] at this
  rw [dartNext_dmD0] at h1
  have hd : dmD1.dir = dmD0.dir := congrArg Dart.dir h1
  rw [dmD1_dir, dmD0_dir] at hd
  have := congrFun hd 0; simp at this




theorem domino_orbitPeriod_eq_six : dartOrbitPeriod domino dmBase = 6 := by
  unfold dartOrbitPeriod
  have hdvd : Function.minimalPeriod (dartNextSub domino) dmBase ∣ 6 :=
    Function.isPeriodicPt_iff_minimalPeriod_dvd.mp dmBase_isPeriodicPt
  have hper : Function.IsPeriodicPt (dartNextSub domino)
      (Function.minimalPeriod (dartNextSub domino) dmBase) dmBase :=
    Function.isPeriodicPt_minimalPeriod _ _
  set m := Function.minimalPeriod (dartNextSub domino) dmBase with hm
  have hmem : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 6 := by
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases m <;> omega
  rcases hmem with h | h | h | h
  · rw [h] at hper
    rw [Function.IsPeriodicPt, Function.iterate_one] at hper
    exact absurd hper dmBase_not_fixedPt
  · rw [h] at hper; exact absurd hper dmBase_not_periodic_two
  · rw [h] at hper; exact absurd hper dmBase_not_periodic_three
  · exact h








theorem domino_turningIsFullRevolution :
    TurningIsFullRevolution domino dmBase := by
  unfold TurningIsFullRevolution
  rw [show (dmBase).1 = dmD0 from rfl, domino_orbitPeriod_eq_six]
  right
  exact domino_totalTurnZ_six




theorem domino_simplePolygonCornerBalance :
    SimplePolygonCornerBalance domino dmBase :=
  (simplePolygonCornerBalance_iff domino dmBase).mpr domino_turningIsFullRevolution

end Lattice

end StatMech
