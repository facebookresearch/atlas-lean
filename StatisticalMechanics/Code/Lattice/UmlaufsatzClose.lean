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
import Code.Lattice.EarRemoval
import Code.Lattice.EarExistence
import Code.Lattice.GaussBonnet
import Code.Lattice.EarContraction
import Code.Lattice.UmlaufsatzBaseCases
import Code.Lattice.UmlaufsatzEar
import Code.Lattice.GaussBonnetEar
import Code.Lattice.BalancePreservingContraction

open SimpleGraph Function Set

namespace StatMech

namespace Lattice












def uc_WindsAtMostOnce (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  |totalTurnZ K a.1 (dartOrbitPeriod K a)| ≤ 4




def uc_WindsAtLeastOnce (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  totalTurnZ K a.1 (dartOrbitPeriod K a) ≠ 0







theorem uc_totalTurn_eq_four_of_winds (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hmax : uc_WindsAtMostOnce K a) (hmin : uc_WindsAtLeastOnce K a) :
    totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 ∨
      totalTurnZ K a.1 (dartOrbitPeriod K a) = -4 := by
  have hdvd := four_dvd_orbit_totalTurnZ K a
  unfold uc_WindsAtMostOnce at hmax
  unfold uc_WindsAtLeastOnce at hmin
  obtain ⟨k, hk⟩ := hdvd
  rw [hk] at hmax hmin ⊢
  rw [abs_le] at hmax
  have hk1 : k = 1 ∨ k = -1 := by
    rcases lt_trichotomy k 0 with h | h | h
    · right; omega
    · exact absurd (by rw [h]; ring) hmin
    · left; omega
  rcases hk1 with h | h
  · left; rw [h]; ring
  · right; rw [h]; ring



theorem uc_winds_of_totalTurn_eq_four (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (h : totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 ∨
      totalTurnZ K a.1 (dartOrbitPeriod K a) = -4) :
    uc_WindsAtMostOnce K a ∧ uc_WindsAtLeastOnce K a := by
  unfold uc_WindsAtMostOnce uc_WindsAtLeastOnce
  rcases h with h | h <;> rw [h] <;> exact ⟨by decide, by decide⟩





theorem uc_winds_iff (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (uc_WindsAtMostOnce K a ∧ uc_WindsAtLeastOnce K a) ↔
      (totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 ∨
        totalTurnZ K a.1 (dartOrbitPeriod K a) = -4) := by
  constructor
  · rintro ⟨hmax, hmin⟩; exact uc_totalTurn_eq_four_of_winds K a hmax hmin
  · exact uc_winds_of_totalTurn_eq_four K a



theorem uc_turningIsFullRevolution_of_winds (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hmax : uc_WindsAtMostOnce K a) (hmin : uc_WindsAtLeastOnce K a) :
    TurningIsFullRevolution K a :=
  uc_totalTurn_eq_four_of_winds K a hmax hmin













theorem uc_base_totalTurn_eq_four (v : Site 2)
    (a : {e : Dart // IsBoundaryDart ({v} : Set (Site 2)) e}) :
    totalTurnZ ({v} : Set (Site 2)) a.1 (dartOrbitPeriod ({v} : Set (Site 2)) a) = 4 ∨
      totalTurnZ ({v} : Set (Site 2)) a.1 (dartOrbitPeriod ({v} : Set (Site 2)) a) = -4 :=
  gbe_singleton_totalTurn_eq_four v a









theorem uc_step_preserves_turn (K K' : Set (Site 2)) (e e' : Dart) (m m' n : ℕ)
    (hmatch : ∀ i, i < n →
      turnZ K ((dartNext K)^[m + i] e) = turnZ K' ((dartNext K')^[m' + i] e'))
    (hbal : umEar_windowTurn K' e' 0 m' = umEar_windowTurn K e 0 m) :
    totalTurnZ K' e' (m' + n) = totalTurnZ K e (m + n) :=
  gbe_ear_step_preserves_turn K K' e e' m m' n hmatch hbal























theorem uc_turningIsFullRevolution (hsat : bpc_BalanceSaturatingContraction)
    (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty)
    (a : {e : Dart // IsBoundaryDart K e}) :
    TurningIsFullRevolution K a :=
  turningIsFullRevolution_of_contraction
    (bpc_balancePreservingContraction_of_saturating hsat) K hK hne a




theorem uc_totalTurn_eq_four (hsat : bpc_BalanceSaturatingContraction)
    (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty)
    (a : {e : Dart // IsBoundaryDart K e}) :
    totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 ∨
      totalTurnZ K a.1 (dartOrbitPeriod K a) = -4 :=
  uc_turningIsFullRevolution hsat K hK hne a










open Real in




theorem uc_totalTurnAngle_eq_two_pi_iff (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    (totalTurnAngle K a.1 (dartOrbitPeriod K a) = 2 * Real.pi ∨
        totalTurnAngle K a.1 (dartOrbitPeriod K a) = -(2 * Real.pi)) ↔
      (totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 ∨
        totalTurnZ K a.1 (dartOrbitPeriod K a) = -4) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [umBase_totalTurnAngle_eq]
  constructor
  · rintro (h | h)
    · left
      have : (totalTurnZ K a.1 (dartOrbitPeriod K a) : ℝ) = 4 := by
        have hh : (totalTurnZ K a.1 (dartOrbitPeriod K a) : ℝ) * (Real.pi / 2)
            = 4 * (Real.pi / 2) := by rw [h]; ring
        exact mul_right_cancel₀ (by positivity) hh
      exact_mod_cast this
    · right
      have : (totalTurnZ K a.1 (dartOrbitPeriod K a) : ℝ) = -4 := by
        have hh : (totalTurnZ K a.1 (dartOrbitPeriod K a) : ℝ) * (Real.pi / 2)
            = (-4) * (Real.pi / 2) := by rw [h]; ring
        exact mul_right_cancel₀ (by positivity) hh
      exact_mod_cast this
  · rintro (h | h)
    · left; rw [h]; push_cast; ring
    · right; rw [h]; push_cast; ring

open Real in





theorem uc_totalTurnAngle_eq_two_pi (hsat : bpc_BalanceSaturatingContraction)
    (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty)
    (a : {e : Dart // IsBoundaryDart K e}) :
    totalTurnAngle K a.1 (dartOrbitPeriod K a) = 2 * Real.pi ∨
      totalTurnAngle K a.1 (dartOrbitPeriod K a) = -(2 * Real.pi) :=
  (uc_totalTurnAngle_eq_two_pi_iff K a).mpr (uc_totalTurn_eq_four hsat K hK hne a)











theorem uc_unitCell_totalTurn_eq_four :
    totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = 4 ∨
      totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = -4 :=
  unitCell_turningIsFullRevolution

open Real in


theorem uc_unitCell_totalTurnAngle_eq_two_pi :
    totalTurnAngle unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = 2 * Real.pi ∨
      totalTurnAngle unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = -(2 * Real.pi) :=
  Or.inr umBase_square_turning_period



theorem uc_unitCell_winds :
    uc_WindsAtMostOnce unitCell ucBase ∧ uc_WindsAtLeastOnce unitCell ucBase :=
  uc_winds_of_totalTurn_eq_four unitCell ucBase uc_unitCell_totalTurn_eq_four



theorem uc_domino_totalTurn_eq_four :
    totalTurnZ domino dmBase.1 (dartOrbitPeriod domino dmBase) = 4 ∨
      totalTurnZ domino dmBase.1 (dartOrbitPeriod domino dmBase) = -4 :=
  domino_turningIsFullRevolution

open Real in



theorem uc_domino_totalTurnAngle_eq_two_pi :
    totalTurnAngle domino dmBase.1 (dartOrbitPeriod domino dmBase) = 2 * Real.pi ∨
      totalTurnAngle domino dmBase.1 (dartOrbitPeriod domino dmBase) = -(2 * Real.pi) := by
  right
  rw [show (dmBase).1 = dmD0 from rfl, domino_orbitPeriod_eq_six]
  exact umBase_domino_turning


theorem uc_domino_winds :
    uc_WindsAtMostOnce domino dmBase ∧ uc_WindsAtLeastOnce domino dmBase :=
  uc_winds_of_totalTurn_eq_four domino dmBase uc_domino_totalTurn_eq_four







theorem uc_domino_saturating_witness :
    ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty)
      (a' : {e : Dart // IsBoundaryDart K' e}),
      K'.ncard < domino.ncard ∧ cornerBalance K' a' = cornerBalance domino dmBase :=
  bpc_domino_balanceSaturatingContraction_witness












theorem uc_winds_iff_turningIsFullRevolution (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    (uc_WindsAtMostOnce K a ∧ uc_WindsAtLeastOnce K a) ↔ TurningIsFullRevolution K a := by
  rw [uc_winds_iff]; rfl





















theorem uc_rot90Fun_add (x y : Site 2) : rot90Fun (x + y) = rot90Fun x + rot90Fun y := by
  funext i
  fin_cases i
  · show -(x + y) 1 = -x 1 + -y 1
    rw [Pi.add_apply]; ring
  · show (x + y) 0 = x 0 + y 0
    rw [Pi.add_apply]



noncomputable def uc_rotSet (K : Set (Site 2)) : Set (Site 2) := rot90Fun '' K



theorem uc_rotSet_mem_iff (K : Set (Site 2)) (z : Site 2) :
    rot90Fun z ∈ uc_rotSet K ↔ z ∈ K := by
  unfold uc_rotSet
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hyz : y = z := rot90Fun_injective hxy
    rwa [hyz] at hy
  · intro h; exact ⟨z, h, rfl⟩



noncomputable def uc_rotDart (e : Dart) : Dart :=
  mkDart (rot90Fun e.tail) (rot90Fun e.dir) (unitWt_rot90Fun_dir e)

@[simp] theorem uc_rotDart_tail (e : Dart) : (uc_rotDart e).tail = rot90Fun e.tail := rfl
@[simp] theorem uc_rotDart_dir (e : Dart) : (uc_rotDart e).dir = rot90Fun e.dir := by
  rw [uc_rotDart, mkDart_dir]
@[simp] theorem uc_rotDart_head (e : Dart) : (uc_rotDart e).head = rot90Fun e.head := by
  rw [uc_rotDart, mkDart_head, Dart.dir_def, sub_eq_add_neg, uc_rot90Fun_add, rot90Fun_neg]; abel


theorem uc_rotDart_injective : Function.Injective uc_rotDart := by
  intro a b h
  apply dart_eq_of_tail_dir
  · exact rot90Fun_injective (by have := congrArg Dart.tail h; simpa only [uc_rotDart_tail] using this)
  · exact rot90Fun_injective (by have := congrArg Dart.dir h; simpa only [uc_rotDart_dir] using this)




theorem uc_turnZ_rot (K : Set (Site 2)) (e : Dart) :
    turnZ (uc_rotSet K) (uc_rotDart e) = turnZ K e := by
  classical
  unfold turnZ
  rw [uc_rotDart_head, uc_rotDart_dir, uc_rotDart_tail]
  have m1 : (rot90Fun e.head + -rot90Fun (rot90Fun e.dir) ∈ uc_rotSet K) ↔
            (e.head + -rot90Fun e.dir ∈ K) := by
    rw [show rot90Fun e.head + -rot90Fun (rot90Fun e.dir)
        = rot90Fun (e.head + -rot90Fun e.dir) by rw [uc_rot90Fun_add, rot90Fun_neg]]
    exact uc_rotSet_mem_iff K _
  have m2 : (rot90Fun e.tail + -rot90Fun (rot90Fun e.dir) ∈ uc_rotSet K) ↔
            (e.tail + -rot90Fun e.dir ∈ K) := by
    rw [show rot90Fun e.tail + -rot90Fun (rot90Fun e.dir)
        = rot90Fun (e.tail + -rot90Fun e.dir) by rw [uc_rot90Fun_add, rot90Fun_neg]]
    exact uc_rotSet_mem_iff K _
  by_cases h1 : e.head + -rot90Fun e.dir ∈ K
  · rw [if_pos (m1.mpr h1), if_pos h1]
  · rw [if_neg (fun hh => h1 (m1.mp hh)), if_neg h1]
    by_cases h2 : e.tail + -rot90Fun e.dir ∈ K
    · rw [if_pos (m2.mpr h2), if_pos h2]
    · rw [if_neg (fun hh => h2 (m2.mp hh)), if_neg h2]




theorem uc_dartNext_rot (K : Set (Site 2)) (e : Dart) :
    dartNext (uc_rotSet K) (uc_rotDart e) = uc_rotDart (dartNext K e) := by
  classical
  have m1 : ((uc_rotDart e).head + -rot90Fun (uc_rotDart e).dir ∈ uc_rotSet K) ↔
            (e.head + -rot90Fun e.dir ∈ K) := by
    rw [uc_rotDart_head, uc_rotDart_dir,
        show rot90Fun e.head + -rot90Fun (rot90Fun e.dir)
        = rot90Fun (e.head + -rot90Fun e.dir) by rw [uc_rot90Fun_add, rot90Fun_neg]]
    exact uc_rotSet_mem_iff K _
  have m2 : ((uc_rotDart e).tail + -rot90Fun (uc_rotDart e).dir ∈ uc_rotSet K) ↔
            (e.tail + -rot90Fun e.dir ∈ K) := by
    rw [uc_rotDart_tail, uc_rotDart_dir,
        show rot90Fun e.tail + -rot90Fun (rot90Fun e.dir)
        = rot90Fun (e.tail + -rot90Fun e.dir) by rw [uc_rot90Fun_add, rot90Fun_neg]]
    exact uc_rotSet_mem_iff K _
  by_cases h1 : e.head + -rot90Fun e.dir ∈ K
  · rw [dartNext_of_front_mem (uc_rotSet K) (uc_rotDart e) (m1.mpr h1),
        dartNext_of_front_mem K e h1]
    apply dart_eq_of_tail_dir
    · simp only [mkDart_tail, uc_rotDart_head, uc_rotDart_dir, uc_rotDart_tail]
      rw [uc_rot90Fun_add, rot90Fun_neg]
    · simp only [mkDart_dir, uc_rotDart_dir]
  · by_cases h2 : e.tail + -rot90Fun e.dir ∈ K
    · rw [dartNext_of_side_mem (uc_rotSet K) (uc_rotDart e) (fun hh => h1 (m1.mp hh)) (m2.mpr h2),
          dartNext_of_side_mem K e h1 h2]
      apply dart_eq_of_tail_dir
      · simp only [mkDart_tail, uc_rotDart_tail, uc_rotDart_dir]
        rw [uc_rot90Fun_add, rot90Fun_neg]
      · simp only [mkDart_dir, uc_rotDart_dir]
    · rw [dartNext_of_corner (uc_rotSet K) (uc_rotDart e) (fun hh => h1 (m1.mp hh))
            (fun hh => h2 (m2.mp hh)),
          dartNext_of_corner K e h1 h2]
      apply dart_eq_of_tail_dir
      · simp only [mkDart_tail, uc_rotDart_tail]
      · simp only [mkDart_dir, uc_rotDart_dir]; rw [rot90Fun_neg]


theorem uc_iterate_dartNext_rot (K : Set (Site 2)) (e : Dart) (k : ℕ) :
    (dartNext (uc_rotSet K))^[k] (uc_rotDart e) = uc_rotDart ((dartNext K)^[k] e) := by
  induction k generalizing e with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, uc_dartNext_rot, ih]


theorem uc_rotDart_boundary (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e) :
    IsBoundaryDart (uc_rotSet K) (uc_rotDart e) := by
  refine ⟨?_, ?_⟩
  · rw [uc_rotDart_tail, uc_rotSet_mem_iff]; exact he.1
  · rw [uc_rotDart_head, uc_rotSet_mem_iff]; exact he.2


theorem uc_rightCornerCount_rot (K : Set (Site 2)) (e : Dart) (p : ℕ) :
    rightCornerCount (uc_rotSet K) (uc_rotDart e) p = rightCornerCount K e p := by
  classical
  unfold rightCornerCount
  congr 2
  apply Finset.filter_congr
  intro i _
  rw [uc_iterate_dartNext_rot, uc_turnZ_rot]


theorem uc_leftCornerCount_rot (K : Set (Site 2)) (e : Dart) (p : ℕ) :
    leftCornerCount (uc_rotSet K) (uc_rotDart e) p = leftCornerCount K e p := by
  classical
  unfold leftCornerCount
  congr 2
  apply Finset.filter_congr
  intro i _
  rw [uc_iterate_dartNext_rot, uc_turnZ_rot]


noncomputable def uc_rotSub (K : Set (Site 2)) :
    {e : Dart // IsBoundaryDart K e} → {e : Dart // IsBoundaryDart (uc_rotSet K) e} :=
  fun a => ⟨uc_rotDart a.1, uc_rotDart_boundary K a.1 a.2⟩

@[simp] theorem uc_rotSub_val (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (uc_rotSub K a).1 = uc_rotDart a.1 := rfl


theorem uc_isPeriodicPt_rot (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) (n : ℕ) :
    Function.IsPeriodicPt (dartNextSub (uc_rotSet K)) n (uc_rotSub K a) ↔
      Function.IsPeriodicPt (dartNextSub K) n a := by
  unfold Function.IsPeriodicPt Function.IsFixedPt
  constructor
  · intro h
    apply Subtype.ext
    have hv := congrArg Subtype.val h
    rw [dartNextSub_iterate_val] at hv
    show ((dartNextSub K)^[n] a).1 = a.1
    rw [dartNextSub_iterate_val]
    have hstep : (dartNext (uc_rotSet K))^[n] (uc_rotSub K a).1
        = uc_rotDart ((dartNext K)^[n] a.1) := by
      show (dartNext (uc_rotSet K))^[n] (uc_rotDart a.1) = _
      rw [uc_iterate_dartNext_rot]
    rw [hstep] at hv
    exact uc_rotDart_injective hv
  · intro h
    apply Subtype.ext
    rw [dartNextSub_iterate_val]
    show (dartNext (uc_rotSet K))^[n] (uc_rotDart a.1) = uc_rotDart a.1
    rw [uc_iterate_dartNext_rot]
    have hv := congrArg Subtype.val h
    rw [dartNextSub_iterate_val] at hv
    rw [hv]


theorem uc_dartOrbitPeriod_rot (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    dartOrbitPeriod (uc_rotSet K) (uc_rotSub K a) = dartOrbitPeriod K a := by
  unfold dartOrbitPeriod
  apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
  intro n
  exact uc_isPeriodicPt_rot K a n




theorem uc_cornerBalance_rot (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    cornerBalance (uc_rotSet K) (uc_rotSub K a) = cornerBalance K a := by
  unfold cornerBalance
  rw [uc_rotSub_val, uc_dartOrbitPeriod_rot, uc_rightCornerCount_rot, uc_leftCornerCount_rot]




theorem uc_totalTurnZ_rot (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    totalTurnZ (uc_rotSet K) (uc_rotSub K a).1 (dartOrbitPeriod (uc_rotSet K) (uc_rotSub K a))
      = totalTurnZ K a.1 (dartOrbitPeriod K a) := by
  rw [← cornerBalance_eq_totalTurnZ, ← cornerBalance_eq_totalTurnZ, uc_cornerBalance_rot]




theorem uc_turningIsFullRevolution_rot (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (h : TurningIsFullRevolution K a) :
    TurningIsFullRevolution (uc_rotSet K) (uc_rotSub K a) := by
  unfold TurningIsFullRevolution at h ⊢
  rw [uc_totalTurnZ_rot]
  exact h




theorem uc_rotSet_domino : uc_rotSet domino = {![0, 0], ![0, 1]} := by
  unfold uc_rotSet domino
  rw [Set.image_insert_eq, Set.image_singleton,
      show rot90Fun (![0, 0] : Site 2) = ![0, 0] by
        rw [rot90Fun_apply]; funext i; fin_cases i <;> simp,
      show rot90Fun (![1, 0] : Site 2) = ![0, 1] by
        rw [rot90Fun_apply]; funext i; fin_cases i <;> simp]







theorem uc_verticalDomino_totalTurn_eq_four :
    totalTurnZ (uc_rotSet domino) (uc_rotSub domino dmBase).1
        (dartOrbitPeriod (uc_rotSet domino) (uc_rotSub domino dmBase)) = 4 ∨
      totalTurnZ (uc_rotSet domino) (uc_rotSub domino dmBase).1
        (dartOrbitPeriod (uc_rotSet domino) (uc_rotSub domino dmBase)) = -4 := by
  rw [uc_totalTurnZ_rot]
  exact domino_turningIsFullRevolution

open Real in



theorem uc_verticalDomino_totalTurnAngle_eq_two_pi :
    totalTurnAngle (uc_rotSet domino) (uc_rotSub domino dmBase).1
        (dartOrbitPeriod (uc_rotSet domino) (uc_rotSub domino dmBase)) = 2 * Real.pi ∨
      totalTurnAngle (uc_rotSet domino) (uc_rotSub domino dmBase).1
        (dartOrbitPeriod (uc_rotSet domino) (uc_rotSub domino dmBase)) = -(2 * Real.pi) := by
  rw [umBase_totalTurnAngle_eq]
  rcases uc_verticalDomino_totalTurn_eq_four with h | h
  · left; rw [h]; push_cast; ring
  · right; rw [h]; push_cast; ring












def uc_GeneralFullRevolution : Prop :=
  ∀ (K : Set (Site 2)), K.Finite → K.Nonempty →
    ∀ (a : {e : Dart // IsBoundaryDart K e}), TurningIsFullRevolution K a



def uc_GeneralEulerCharOne : Prop :=
  ∀ (K : Set (Site 2)), K.Finite → K.Nonempty →
    ∀ (a : {e : Dart // IsBoundaryDart K e}), EulerCharOne K a



theorem uc_generalFullRevolution_of_saturating (hsat : bpc_BalanceSaturatingContraction) :
    uc_GeneralFullRevolution :=
  fun K hK hne a => uc_turningIsFullRevolution hsat K hK hne a







theorem uc_generalEulerCharOne_of_saturating (hsat : bpc_BalanceSaturatingContraction) :
    uc_GeneralEulerCharOne := by
  intro K hK hne a
  have hrev : TurningIsFullRevolution K a := uc_turningIsFullRevolution hsat K hK hne a
  have hp : 3 ≤ dartOrbitPeriod K a := by
    have := orbitPeriod_ge_four_of_fullRevolution K a hrev; omega
  exact (eulerCharOne_iff_turningIsFullRevolution K a hp).mpr hrev









theorem uc_fullRevolution_of_eulerCharOne_period (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (hp : 3 ≤ dartOrbitPeriod K a)
    (h : EulerCharOne K a) : TurningIsFullRevolution K a :=
  turningIsFullRevolution_of_eulerCharOne K a hp h





theorem uc_verticalDomino_eulerCharOne :
    EulerCharOne (uc_rotSet domino) (uc_rotSub domino dmBase) := by
  have hrev : TurningIsFullRevolution (uc_rotSet domino) (uc_rotSub domino dmBase) :=
    uc_verticalDomino_totalTurn_eq_four
  have hp : 3 ≤ dartOrbitPeriod (uc_rotSet domino) (uc_rotSub domino dmBase) := by
    have := orbitPeriod_ge_four_of_fullRevolution (uc_rotSet domino) (uc_rotSub domino dmBase) hrev
    omega
  exact (eulerCharOne_iff_turningIsFullRevolution (uc_rotSet domino) (uc_rotSub domino dmBase) hp).mpr
    hrev


































































end Lattice

end StatMech
