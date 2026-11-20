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

open SimpleGraph Function

namespace StatMech

namespace Lattice







open Classical in


noncomputable def rightCornerCount (K : Set (Site 2)) (e : Dart) (p : ℕ) : ℤ :=
  ((Finset.range p).filter (fun i => turnZ K ((dartNext K)^[i] e) = 1)).card

open Classical in


noncomputable def leftCornerCount (K : Set (Site 2)) (e : Dart) (p : ℕ) : ℤ :=
  ((Finset.range p).filter (fun i => turnZ K ((dartNext K)^[i] e) = -1)).card












theorem totalTurnZ_eq_cornerBalance (K : Set (Site 2)) (e : Dart) (p : ℕ) :
    totalTurnZ K e p = rightCornerCount K e p - leftCornerCount K e p := by
  classical
  unfold totalTurnZ rightCornerCount leftCornerCount
  rw [Finset.card_filter, Finset.card_filter]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases turnZ_mem K ((dartNext K)^[i] e) with h | h | h <;> rw [h] <;> norm_num






theorem turningIsFullRevolution_of_cornerBalance (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (h : rightCornerCount K a.1 (dartOrbitPeriod K a) -
          leftCornerCount K a.1 (dartOrbitPeriod K a) = 4 ∨
        rightCornerCount K a.1 (dartOrbitPeriod K a) -
          leftCornerCount K a.1 (dartOrbitPeriod K a) = -4) :
    TurningIsFullRevolution K a := by
  unfold TurningIsFullRevolution
  rw [totalTurnZ_eq_cornerBalance]
  exact h









theorem totalTurnZ_four_of_all_left (K : Set (Site 2)) (e : Dart)
    (h0 : turnZ K e = -1)
    (h1 : turnZ K (dartNext K e) = -1)
    (h2 : turnZ K ((dartNext K)^[2] e) = -1)
    (h3 : turnZ K ((dartNext K)^[3] e) = -1) :
    totalTurnZ K e 4 = -4 := by
  unfold totalTurnZ
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one, Function.iterate_zero_apply, Function.iterate_one]
  rw [h0, h1, h2, h3]
  ring









noncomputable def unitCell : Set (Site 2) := {![0, 0]}

theorem unitCell_finite : unitCell.Finite := Set.finite_singleton _


theorem origin_mem_unitCell : (![0, 0] : Site 2) ∈ unitCell := rfl



theorem not_mem_unitCell (v : Site 2) (h : v 0 ≠ 0 ∨ v 1 ≠ 0) : v ∉ unitCell := by
  simp only [unitCell, Set.mem_singleton_iff]
  intro hv
  rcases h with h | h
  · exact h (by rw [hv]; simp)
  · exact h (by rw [hv]; simp)



theorem unitWt_px : unitWt (![1, 0] : Site 2) = 1 := by simp [unitWt, Fin.sum_univ_two]
theorem unitWt_my : unitWt (![0, -1] : Site 2) = 1 := by simp [unitWt, Fin.sum_univ_two]
theorem unitWt_mx : unitWt (![-1, 0] : Site 2) = 1 := by simp [unitWt, Fin.sum_univ_two]
theorem unitWt_py : unitWt (![0, 1] : Site 2) = 1 := by simp [unitWt, Fin.sum_univ_two]



noncomputable def ucDart0 : Dart := mkDart ![0, 0] ![1, 0] unitWt_px
noncomputable def ucDart1 : Dart := mkDart ![0, 0] ![0, -1] unitWt_my
noncomputable def ucDart2 : Dart := mkDart ![0, 0] ![-1, 0] unitWt_mx
noncomputable def ucDart3 : Dart := mkDart ![0, 0] ![0, 1] unitWt_py



theorem ucDart0_tail : ucDart0.tail = ![0, 0] := rfl
theorem ucDart1_tail : ucDart1.tail = ![0, 0] := rfl
theorem ucDart2_tail : ucDart2.tail = ![0, 0] := rfl
theorem ucDart3_tail : ucDart3.tail = ![0, 0] := rfl

theorem ucDart0_dir : ucDart0.dir = ![1, 0] := by rw [ucDart0, mkDart_dir]
theorem ucDart1_dir : ucDart1.dir = ![0, -1] := by rw [ucDart1, mkDart_dir]
theorem ucDart2_dir : ucDart2.dir = ![-1, 0] := by rw [ucDart2, mkDart_dir]
theorem ucDart3_dir : ucDart3.dir = ![0, 1] := by rw [ucDart3, mkDart_dir]

theorem ucDart0_head : ucDart0.head = ![1, 0] := by
  rw [ucDart0, mkDart_head]; funext i; fin_cases i <;> simp
theorem ucDart1_head : ucDart1.head = ![0, -1] := by
  rw [ucDart1, mkDart_head]; funext i; fin_cases i <;> simp
theorem ucDart2_head : ucDart2.head = ![-1, 0] := by
  rw [ucDart2, mkDart_head]; funext i; fin_cases i <;> simp
theorem ucDart3_head : ucDart3.head = ![0, 1] := by
  rw [ucDart3, mkDart_head]; funext i; fin_cases i <;> simp



theorem ucDart0_boundary : IsBoundaryDart unitCell ucDart0 :=
  ⟨by rw [ucDart0_tail]; exact origin_mem_unitCell,
   by rw [ucDart0_head]; exact not_mem_unitCell _ (Or.inl (by simp))⟩
theorem ucDart1_boundary : IsBoundaryDart unitCell ucDart1 :=
  ⟨by rw [ucDart1_tail]; exact origin_mem_unitCell,
   by rw [ucDart1_head]; exact not_mem_unitCell _ (Or.inr (by simp))⟩
theorem ucDart2_boundary : IsBoundaryDart unitCell ucDart2 :=
  ⟨by rw [ucDart2_tail]; exact origin_mem_unitCell,
   by rw [ucDart2_head]; exact not_mem_unitCell _ (Or.inl (by simp))⟩
theorem ucDart3_boundary : IsBoundaryDart unitCell ucDart3 :=
  ⟨by rw [ucDart3_tail]; exact origin_mem_unitCell,
   by rw [ucDart3_head]; exact not_mem_unitCell _ (Or.inr (by simp))⟩




theorem ucDart0_travel : -rot90Fun ucDart0.dir = ![0, -1] := by
  rw [ucDart0_dir, rot90Fun_apply]; funext i; fin_cases i <;> simp
theorem ucDart1_travel : -rot90Fun ucDart1.dir = ![-1, 0] := by
  rw [ucDart1_dir, rot90Fun_apply]; funext i; fin_cases i <;> simp
theorem ucDart2_travel : -rot90Fun ucDart2.dir = ![0, 1] := by
  rw [ucDart2_dir, rot90Fun_apply]; funext i; fin_cases i <;> simp
theorem ucDart3_travel : -rot90Fun ucDart3.dir = ![1, 0] := by
  rw [ucDart3_dir, rot90Fun_apply]; funext i; fin_cases i <;> simp





theorem ucDart0_front_nmem : ucDart0.head + (-rot90Fun ucDart0.dir) ∉ unitCell := by
  rw [ucDart0_head, ucDart0_travel]; exact not_mem_unitCell _ (Or.inl (by simp))
theorem ucDart0_side_nmem : ucDart0.tail + (-rot90Fun ucDart0.dir) ∉ unitCell := by
  rw [ucDart0_tail, ucDart0_travel]; exact not_mem_unitCell _ (Or.inr (by simp))

theorem ucDart1_front_nmem : ucDart1.head + (-rot90Fun ucDart1.dir) ∉ unitCell := by
  rw [ucDart1_head, ucDart1_travel]; exact not_mem_unitCell _ (Or.inl (by simp))
theorem ucDart1_side_nmem : ucDart1.tail + (-rot90Fun ucDart1.dir) ∉ unitCell := by
  rw [ucDart1_tail, ucDart1_travel]; exact not_mem_unitCell _ (Or.inl (by simp))

theorem ucDart2_front_nmem : ucDart2.head + (-rot90Fun ucDart2.dir) ∉ unitCell := by
  rw [ucDart2_head, ucDart2_travel]; exact not_mem_unitCell _ (Or.inl (by simp))
theorem ucDart2_side_nmem : ucDart2.tail + (-rot90Fun ucDart2.dir) ∉ unitCell := by
  rw [ucDart2_tail, ucDart2_travel]; exact not_mem_unitCell _ (Or.inr (by simp))

theorem ucDart3_front_nmem : ucDart3.head + (-rot90Fun ucDart3.dir) ∉ unitCell := by
  rw [ucDart3_head, ucDart3_travel]; exact not_mem_unitCell _ (Or.inl (by simp))
theorem ucDart3_side_nmem : ucDart3.tail + (-rot90Fun ucDart3.dir) ∉ unitCell := by
  rw [ucDart3_tail, ucDart3_travel]; exact not_mem_unitCell _ (Or.inl (by simp))



theorem ucDart0_turnZ : turnZ unitCell ucDart0 = -1 := by
  unfold turnZ; rw [if_neg ucDart0_front_nmem, if_neg ucDart0_side_nmem]
theorem ucDart1_turnZ : turnZ unitCell ucDart1 = -1 := by
  unfold turnZ; rw [if_neg ucDart1_front_nmem, if_neg ucDart1_side_nmem]
theorem ucDart2_turnZ : turnZ unitCell ucDart2 = -1 := by
  unfold turnZ; rw [if_neg ucDart2_front_nmem, if_neg ucDart2_side_nmem]
theorem ucDart3_turnZ : turnZ unitCell ucDart3 = -1 := by
  unfold turnZ; rw [if_neg ucDart3_front_nmem, if_neg ucDart3_side_nmem]

theorem dartNext_ucDart0 : dartNext unitCell ucDart0 = ucDart1 := by
  apply dart_eq_of_tail_dir
  · rw [dartNext_left_tail unitCell ucDart0 ucDart0_front_nmem ucDart0_side_nmem,
      ucDart0_tail, ucDart1_tail]
  · rw [dartNext_left_dir unitCell ucDart0 ucDart0_front_nmem ucDart0_side_nmem,
      ucDart0_travel, ucDart1_dir]
theorem dartNext_ucDart1 : dartNext unitCell ucDart1 = ucDart2 := by
  apply dart_eq_of_tail_dir
  · rw [dartNext_left_tail unitCell ucDart1 ucDart1_front_nmem ucDart1_side_nmem,
      ucDart1_tail, ucDart2_tail]
  · rw [dartNext_left_dir unitCell ucDart1 ucDart1_front_nmem ucDart1_side_nmem,
      ucDart1_travel, ucDart2_dir]
theorem dartNext_ucDart2 : dartNext unitCell ucDart2 = ucDart3 := by
  apply dart_eq_of_tail_dir
  · rw [dartNext_left_tail unitCell ucDart2 ucDart2_front_nmem ucDart2_side_nmem,
      ucDart2_tail, ucDart3_tail]
  · rw [dartNext_left_dir unitCell ucDart2 ucDart2_front_nmem ucDart2_side_nmem,
      ucDart2_travel, ucDart3_dir]
theorem dartNext_ucDart3 : dartNext unitCell ucDart3 = ucDart0 := by
  apply dart_eq_of_tail_dir
  · rw [dartNext_left_tail unitCell ucDart3 ucDart3_front_nmem ucDart3_side_nmem,
      ucDart3_tail, ucDart0_tail]
  · rw [dartNext_left_dir unitCell ucDart3 ucDart3_front_nmem ucDart3_side_nmem,
      ucDart3_travel, ucDart0_dir]




theorem iterate_ucDart_1 : (dartNext unitCell)^[1] ucDart0 = ucDart1 := by
  rw [Function.iterate_one]; exact dartNext_ucDart0

theorem iterate_ucDart_2 : (dartNext unitCell)^[2] ucDart0 = ucDart2 := by
  rw [Function.iterate_succ_apply', iterate_ucDart_1, dartNext_ucDart1]

theorem iterate_ucDart_3 : (dartNext unitCell)^[3] ucDart0 = ucDart3 := by
  rw [Function.iterate_succ_apply', iterate_ucDart_2, dartNext_ucDart2]

theorem iterate_ucDart_4 : (dartNext unitCell)^[4] ucDart0 = ucDart0 := by
  rw [Function.iterate_succ_apply', iterate_ucDart_3, dartNext_ucDart3]






theorem unitCell_totalTurnZ_four : totalTurnZ unitCell ucDart0 4 = -4 := by
  apply totalTurnZ_four_of_all_left
  · exact ucDart0_turnZ
  · rw [dartNext_ucDart0]; exact ucDart1_turnZ
  · rw [iterate_ucDart_2]; exact ucDart2_turnZ
  · rw [iterate_ucDart_3]; exact ucDart3_turnZ








noncomputable def ucBase : {e : Dart // IsBoundaryDart unitCell e} :=
  ⟨ucDart0, ucDart0_boundary⟩


theorem ucBase_isPeriodicPt : Function.IsPeriodicPt (dartNextSub unitCell) 4 ucBase := by
  unfold Function.IsPeriodicPt Function.IsFixedPt
  apply Subtype.ext
  rw [dartNextSub_iterate_val]
  exact iterate_ucDart_4


theorem ucBase_not_fixedPt : ¬ Function.IsFixedPt (dartNextSub unitCell) ucBase := by
  intro h
  have h2 : dartNext unitCell ucDart0 = ucDart0 := by
    have := congrArg Subtype.val h
    rwa [dartNextSub_val] at this
  rw [dartNext_ucDart0] at h2
  have hd : ucDart1.dir = ucDart0.dir := congrArg Dart.dir h2
  rw [ucDart1_dir, ucDart0_dir] at hd
  have := congrFun hd 0
  simp at this


theorem ucBase_not_periodic_two :
    ¬ Function.IsPeriodicPt (dartNextSub unitCell) 2 ucBase := by
  intro h
  have h2 : (dartNext unitCell)^[2] ucDart0 = ucDart0 := by
    have := congrArg Subtype.val h
    rwa [dartNextSub_iterate_val] at this
  rw [iterate_ucDart_2] at h2
  have hd : ucDart2.dir = ucDart0.dir := congrArg Dart.dir h2
  rw [ucDart2_dir, ucDart0_dir] at hd
  have := congrFun hd 0
  simp at this




theorem unitCell_orbitPeriod_eq_four : dartOrbitPeriod unitCell ucBase = 4 := by
  unfold dartOrbitPeriod
  have hdvd : Function.minimalPeriod (dartNextSub unitCell) ucBase ∣ 4 :=
    Function.isPeriodicPt_iff_minimalPeriod_dvd.mp ucBase_isPeriodicPt
  have hper : Function.IsPeriodicPt (dartNextSub unitCell)
      (Function.minimalPeriod (dartNextSub unitCell) ucBase) ucBase :=
    Function.isPeriodicPt_minimalPeriod _ _
  set m := Function.minimalPeriod (dartNextSub unitCell) ucBase with hm
  have hmem : m = 1 ∨ m = 2 ∨ m = 4 := by
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases m <;> omega
  rcases hmem with h | h | h
  · rw [h] at hper
    rw [Function.IsPeriodicPt, Function.iterate_one] at hper
    exact absurd hper ucBase_not_fixedPt
  · rw [h] at hper; exact absurd hper ucBase_not_periodic_two
  · exact h












theorem unitCell_turningIsFullRevolution :
    TurningIsFullRevolution unitCell ucBase := by
  unfold TurningIsFullRevolution
  rw [show (ucBase).1 = ucDart0 from rfl, unitCell_orbitPeriod_eq_four]
  right
  exact unitCell_totalTurnZ_four





theorem unitCell_orbitPeriod_ge_four : 4 ≤ dartOrbitPeriod unitCell ucBase :=
  orbitPeriod_ge_four_of_fullRevolution unitCell ucBase unitCell_turningIsFullRevolution

end Lattice

end StatMech
