/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FK.TriHexFKExternalWeight










open Finset
open scoped BigOperators

namespace StatMech.FK.PeriodicPlanar

open Universality


def triangleFKLocalConnectivity : LocalConfig → ThreeTerminalConnectivity
  | (false, false, false) => .separate
  | (true, false, false) => .pair12
  | (false, true, false) => .pair20
  | (false, false, true) => .pair01
  | _ => .together


def starFKLocalConnectivity : LocalConfig → ThreeTerminalConnectivity
  | (false, false, false) => .separate
  | (true, false, false) => .separate
  | (false, true, false) => .separate
  | (false, false, true) => .separate
  | (true, true, false) => .pair01
  | (false, true, true) => .pair12
  | (true, false, true) => .pair20
  | (true, true, true) => .together




def triangleFKLocalOddsWeight (y0 y1 y2 : Real) : LocalConfig → Real
  | (b0, b1, b2) =>
      (if b0 then y0 else 1) * (if b1 then y1 else 1) *
        (if b2 then y2 else 1)



def starFKLocalOddsWeight (q y0 y1 y2 : Real) : LocalConfig → Real
  | (false, false, false) => q
  | (b0, b1, b2) =>
      (if b0 then y0 else 1) * (if b1 then y1 else 1) *
        (if b2 then y2 else 1)



theorem triangleFKLocalOddsWeight_fiber
    (y0 y1 y2 : Real) (connectivity : ThreeTerminalConnectivity) :
    (∑ omega : LocalConfig,
      if triangleFKLocalConnectivity omega = connectivity then
        triangleFKLocalOddsWeight y0 y1 y2 omega else 0) =
      triangleFKTerminalWeight y0 y1 y2 connectivity := by
  fin_cases connectivity <;>
    simp [triangleFKLocalConnectivity, triangleFKLocalOddsWeight,
      triangleFKTerminalWeight, Fintype.sum_prod_type] <;> ring



theorem starFKLocalOddsWeight_fiber
    (q y0 y1 y2 : Real) (connectivity : ThreeTerminalConnectivity) :
    (∑ omega : LocalConfig,
      if starFKLocalConnectivity omega = connectivity then
        starFKLocalOddsWeight q y0 y1 y2 omega else 0) =
      starFKTerminalWeight q y0 y1 y2 connectivity := by
  fin_cases connectivity <;>
    simp [starFKLocalConnectivity, starFKLocalOddsWeight,
      starFKTerminalWeight, Fintype.sum_prod_type] <;> ring




theorem finiteLocalConfig_fiber_sum_eq_prod
    {ι Ω C : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [Fintype C] [DecidableEq C]
    (classify : Ω → C) (weight : Ω → Real) (sector : ι → C) :
    (∑ config : ι → Ω,
      if (fun i => classify (config i)) = sector then
        ∏ i, weight (config i) else 0) =
      ∏ i, ∑ omega : Ω,
        if classify omega = sector i then weight omega else 0 := by
  classical
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro config _
  by_cases hsector : (fun i => classify (config i)) = sector
  · subst sector
    simp
  · simp only [hsector, if_false]
    obtain ⟨i, hi⟩ : ∃ i, classify (config i) ≠ sector i := by
      by_contra h
      push_neg at h
      exact hsector (funext h)
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]



def triangleFKGlobalSweepSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y0 y1 y2 : Real)
    (external : (ι → ThreeTerminalConnectivity) → Real) : Real :=
  ∑ sector : ι → ThreeTerminalConnectivity,
    external sector * ∏ i, triangleFKTerminalWeight y0 y1 y2 (sector i)



def starFKGlobalSweepSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q y0 y1 y2 : Real)
    (external : (ι → ThreeTerminalConnectivity) → Real) : Real :=
  ∑ sector : ι → ThreeTerminalConnectivity,
    external sector * ∏ i, starFKTerminalWeight q y0 y1 y2 (sector i)


def triangleFKGlobalConfigSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y0 y1 y2 : Real)
    (external : (ι → ThreeTerminalConnectivity) → Real) : Real :=
  ∑ config : ι → LocalConfig,
    external (fun i => triangleFKLocalConnectivity (config i)) *
      ∏ i, triangleFKLocalOddsWeight y0 y1 y2 (config i)


def starFKGlobalConfigSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q y0 y1 y2 : Real)
    (external : (ι → ThreeTerminalConnectivity) → Real) : Real :=
  ∑ config : ι → LocalConfig,
    external (fun i => starFKLocalConnectivity (config i)) *
      ∏ i, starFKLocalOddsWeight q y0 y1 y2 (config i)



theorem triangleFKGlobalConfigSum_eq_sweepSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y0 y1 y2 : Real)
    (external : (ι → ThreeTerminalConnectivity) → Real) :
    triangleFKGlobalConfigSum y0 y1 y2 external =
      triangleFKGlobalSweepSum y0 y1 y2 external := by
  classical
  unfold triangleFKGlobalConfigSum triangleFKGlobalSweepSum
  let classify : (ι → LocalConfig) →
      (ι → ThreeTerminalConnectivity) := fun config i =>
    triangleFKLocalConnectivity (config i)
  calc
    (∑ config : ι → LocalConfig,
        external (classify config) *
          ∏ i, triangleFKLocalOddsWeight y0 y1 y2 (config i)) =
      ∑ sector : ι → ThreeTerminalConnectivity,
        ∑ config : ι → LocalConfig,
          if classify config = sector then
            external (classify config) *
              ∏ i, triangleFKLocalOddsWeight y0 y1 y2 (config i)
          else 0 := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro config _
            simp
    _ = ∑ sector : ι → ThreeTerminalConnectivity,
        external sector *
          ∏ i, ∑ omega : LocalConfig,
            if triangleFKLocalConnectivity omega = sector i then
              triangleFKLocalOddsWeight y0 y1 y2 omega else 0 := by
      apply Finset.sum_congr rfl
      intro sector _
      rw [← finiteLocalConfig_fiber_sum_eq_prod]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro config _
      by_cases h : classify config = sector <;> simp [h, classify]
    _ = ∑ sector : ι → ThreeTerminalConnectivity,
        external sector *
          ∏ i, triangleFKTerminalWeight y0 y1 y2 (sector i) := by
      apply Finset.sum_congr rfl
      intro sector _
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      exact triangleFKLocalOddsWeight_fiber y0 y1 y2 (sector i)



theorem starFKGlobalConfigSum_eq_sweepSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q y0 y1 y2 : Real)
    (external : (ι → ThreeTerminalConnectivity) → Real) :
    starFKGlobalConfigSum q y0 y1 y2 external =
      starFKGlobalSweepSum q y0 y1 y2 external := by
  classical
  unfold starFKGlobalConfigSum starFKGlobalSweepSum
  let classify : (ι → LocalConfig) →
      (ι → ThreeTerminalConnectivity) := fun config i =>
    starFKLocalConnectivity (config i)
  calc
    (∑ config : ι → LocalConfig,
        external (classify config) *
          ∏ i, starFKLocalOddsWeight q y0 y1 y2 (config i)) =
      ∑ sector : ι → ThreeTerminalConnectivity,
        ∑ config : ι → LocalConfig,
          if classify config = sector then
            external (classify config) *
              ∏ i, starFKLocalOddsWeight q y0 y1 y2 (config i)
          else 0 := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro config _
            simp
    _ = ∑ sector : ι → ThreeTerminalConnectivity,
        external sector *
          ∏ i, ∑ omega : LocalConfig,
            if starFKLocalConnectivity omega = sector i then
              starFKLocalOddsWeight q y0 y1 y2 omega else 0 := by
      apply Finset.sum_congr rfl
      intro sector _
      rw [← finiteLocalConfig_fiber_sum_eq_prod]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro config _
      by_cases h : classify config = sector <;> simp [h, classify]
    _ = ∑ sector : ι → ThreeTerminalConnectivity,
        external sector *
          ∏ i, starFKTerminalWeight q y0 y1 y2 (sector i) := by
      apply Finset.sum_congr rfl
      intro sector _
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      exact starFKLocalOddsWeight_fiber q y0 y1 y2 (sector i)



noncomputable def triangleFKGlobalSweepRatio
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y0 y1 y2 : Real)
    (external observable : (ι → ThreeTerminalConnectivity) → Real) : Real :=
  triangleFKGlobalSweepSum y0 y1 y2
      (fun sector => external sector * observable sector) /
    triangleFKGlobalSweepSum y0 y1 y2 external


noncomputable def starFKGlobalSweepRatio
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q y0 y1 y2 : Real)
    (external observable : (ι → ThreeTerminalConnectivity) → Real) : Real :=
  starFKGlobalSweepSum q y0 y1 y2
      (fun sector => external sector * observable sector) /
    starFKGlobalSweepSum q y0 y1 y2 external



theorem triHexFK_globalSweep_sector_identity
    {ι : Type*} [Fintype ι]
    {q y0 y1 y2 y0Star y1Star y2Star : Real}
    (h0 : y0 * y0Star = q) (h1 : y1 * y1Star = q)
    (h2 : y2 * y2Star = q)
    (hsurface : FrontierA.triangularFKCriticalSurface q y0 y1 y2 = 0)
    (sector : ι → ThreeTerminalConnectivity) :
    (y0 * y1 * y2) ^ Fintype.card ι *
        (∏ i, starFKTerminalWeight q y0Star y1Star y2Star (sector i)) =
      (q ^ 2) ^ Fintype.card ι *
        ∏ i, triangleFKTerminalWeight y0 y1 y2 (sector i) := by
  classical
  have hprod := Finset.prod_congr rfl fun i (_hi : i ∈ (univ : Finset ι)) =>
    triHexFK_terminalWeight_identity h0 h1 h2 hsurface (sector i)
  simpa [Finset.prod_mul_distrib] using hprod





theorem triHexFK_globalSweepSum_identity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q y0 y1 y2 y0Star y1Star y2Star : Real}
    (h0 : y0 * y0Star = q) (h1 : y1 * y1Star = q)
    (h2 : y2 * y2Star = q)
    (hsurface : FrontierA.triangularFKCriticalSurface q y0 y1 y2 = 0)
    (external : (ι → ThreeTerminalConnectivity) → Real) :
    (y0 * y1 * y2) ^ Fintype.card ι *
        starFKGlobalSweepSum q y0Star y1Star y2Star external =
      (q ^ 2) ^ Fintype.card ι *
        triangleFKGlobalSweepSum y0 y1 y2 external := by
  unfold starFKGlobalSweepSum triangleFKGlobalSweepSum
  rw [mul_sum, mul_sum]
  apply Finset.sum_congr rfl
  intro sector _
  calc
    (y0 * y1 * y2) ^ Fintype.card ι *
        (external sector *
          ∏ i, starFKTerminalWeight q y0Star y1Star y2Star (sector i)) =
      external sector *
        ((y0 * y1 * y2) ^ Fintype.card ι *
          ∏ i, starFKTerminalWeight q y0Star y1Star y2Star (sector i)) := by
        ring
    _ = external sector *
        ((q ^ 2) ^ Fintype.card ι *
          ∏ i, triangleFKTerminalWeight y0 y1 y2 (sector i)) := by
        rw [triHexFK_globalSweep_sector_identity h0 h1 h2 hsurface sector]
    _ = (q ^ 2) ^ Fintype.card ι *
        (external sector *
          ∏ i, triangleFKTerminalWeight y0 y1 y2 (sector i)) := by
        ring



theorem triHexFK_globalSweepRatio_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q y0 y1 y2 y0Star y1Star y2Star : Real}
    (hq : q ≠ 0) (hyprod : y0 * y1 * y2 ≠ 0)
    (h0 : y0 * y0Star = q) (h1 : y1 * y1Star = q)
    (h2 : y2 * y2Star = q)
    (hsurface : FrontierA.triangularFKCriticalSurface q y0 y1 y2 = 0)
    (external observable : (ι → ThreeTerminalConnectivity) → Real) :
    starFKGlobalSweepRatio q y0Star y1Star y2Star external observable =
      triangleFKGlobalSweepRatio y0 y1 y2 external observable := by
  have hscale :
      (q ^ 2) ^ Fintype.card ι /
          (y0 * y1 * y2) ^ Fintype.card ι ≠ 0 :=
    div_ne_zero (pow_ne_zero _ (pow_ne_zero 2 hq))
      (pow_ne_zero _ hyprod)
  have scale (coeff : (ι → ThreeTerminalConnectivity) → Real) :
      starFKGlobalSweepSum q y0Star y1Star y2Star coeff =
        ((q ^ 2) ^ Fintype.card ι /
          (y0 * y1 * y2) ^ Fintype.card ι) *
            triangleFKGlobalSweepSum y0 y1 y2 coeff := by
    have hid := triHexFK_globalSweepSum_identity
      (ι := ι) h0 h1 h2 hsurface coeff
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff (pow_ne_zero _ hyprod)).2
    calc
      starFKGlobalSweepSum q y0Star y1Star y2Star coeff *
          (y0 * y1 * y2) ^ Fintype.card ι =
        (y0 * y1 * y2) ^ Fintype.card ι *
          starFKGlobalSweepSum q y0Star y1Star y2Star coeff := by ring
      _ = (q ^ 2) ^ Fintype.card ι *
          triangleFKGlobalSweepSum y0 y1 y2 coeff := hid
  unfold starFKGlobalSweepRatio triangleFKGlobalSweepRatio
  rw [scale (fun sector => external sector * observable sector), scale external]
  exact mul_div_mul_left _ _ hscale



def ThreeTerminalConnectivity.Connects
    (connectivity : ThreeTerminalConnectivity) (i j : Fin 3) : Prop :=
  i = j ∨ match connectivity with
    | .separate => False
    | .pair01 => (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)
    | .pair12 => (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)
    | .pair20 => (i = 2 ∧ j = 0) ∨ (i = 0 ∧ j = 2)
    | .together => True

theorem ThreeTerminalConnectivity.connects_symm
    (connectivity : ThreeTerminalConnectivity) (i j : Fin 3) :
    connectivity.Connects i j ↔ connectivity.Connects j i := by
  fin_cases connectivity <;> fin_cases i <;> fin_cases j <;>
    simp [ThreeTerminalConnectivity.Connects]



def triHexFKTerminalSectorGraph
    {ι V : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq V]
    (terminal : ι → Fin 3 → V)
    (sector : ι → ThreeTerminalConnectivity) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {edge | ∃ cell i j,
    (sector cell).Connects i j ∧ edge = s(terminal cell i, terminal cell j)}



noncomputable def triHexFKTerminalTwoPointObservable
    {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]
    (terminal : ι → Fin 3 → V) (x y : V)
    (sector : ι → ThreeTerminalConnectivity) : Real :=
  by
    classical
    exact if (triHexFKTerminalSectorGraph terminal sector).Reachable x y then 1 else 0





theorem triHexFK_globalSweep_twoPointRatio_eq
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V]
    {q y0 y1 y2 y0Star y1Star y2Star : Real}
    (hq : q ≠ 0) (hyprod : y0 * y1 * y2 ≠ 0)
    (h0 : y0 * y0Star = q) (h1 : y1 * y1Star = q)
    (h2 : y2 * y2Star = q)
    (hsurface : FrontierA.triangularFKCriticalSurface q y0 y1 y2 = 0)
    (terminal : ι → Fin 3 → V)
    (external : (ι → ThreeTerminalConnectivity) → Real)
    (x y : V) :
    starFKGlobalSweepRatio q y0Star y1Star y2Star external
        (triHexFKTerminalTwoPointObservable terminal x y) =
      triangleFKGlobalSweepRatio y0 y1 y2 external
        (triHexFKTerminalTwoPointObservable terminal x y) :=
  triHexFK_globalSweepRatio_eq hq hyprod h0 h1 h2 hsurface
    external (triHexFKTerminalTwoPointObservable terminal x y)

end StatMech.FK.PeriodicPlanar
