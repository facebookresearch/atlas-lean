/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Probability.Reliability.SystemLifetime

/-!
# Tests for measurable lifetime of a monotone Boolean system

C5: concrete API instantiations for
`Reliability.systemLifetime` and its event identity.

* Series, parallel and 2-of-3 on three components with ties (`1`, `1`)
  and an infinite component (`⊤`); observation time exactly equal to a
  component lifetime (`t = 1`) is down by the strict up convention.
* Empty component type: series is always up (`⊤`), parallel never up (`0`).
* Never-up (`∅`) and always-up (`univ`) boundary events.
* Non-monotone XOR negative example: up times need not form an initial
  segment (`false`, `true` at `t = 0`, `1`).
* Nonstrict (`≤`) up convention fails the event identity at a tie
  (`T = 0`, `t = 0`).

Each test combines independently reduced pins (direct `rfl`, lattice
bounds, `lt_irrefl`, `ENNReal.coe_lt_top`) with applications of the
exported theorems. No copied production implementation.
-/

namespace ReliabilityTest

open Reliability StatMech

/-- Three-component lifetimes with ties and an infinite component:
`none ↦ 1`, `some false ↦ 1`, `some true ↦ ⊤`. Finite values are
`NNReal` coercions so strict comparisons reduce via `coe` lemmas. -/
noncomputable def T3 : Option Bool → ENNReal
  | none => ((1 : NNReal) : ENNReal)
  | some false => ((1 : NNReal) : ENNReal)
  | some true => ⊤

/-- Two-component lifetimes for XOR: `false ↦ 1`, `true ↦ ⊤`. -/
noncomputable def T2 : Bool → ENNReal
  | false => ((1 : NNReal) : ENNReal)
  | true => ⊤

/-- Single-component zero lifetime for tie tests. -/
noncomputable def T1 : Unit → ENNReal
  | () => ((0 : NNReal) : ENNReal)

/-- Empty-type lifetimes (value irrelevant, no components). -/
noncomputable def T0 : Empty → ENNReal := fun _ => ((0 : NNReal) : ENNReal)

/-- 2-of-3 event on `Option Bool`: at least two coordinates `true`. -/
def twoOfThree : Set (ConfigSpace (Option Bool)) :=
  {x |
    (x none = true ∧ x (some false) = true) ∨
    (x none = true ∧ x (some true) = true) ∨
    (x (some false) = true ∧ x (some true) = true)}

/-- XOR event on `Bool`: exactly one coordinate `true`. Stated with
`¬(· = true)` so `upConfig` reasoning uses only `upConfig_apply_eq_true`. -/
def xorEvent : Set (ConfigSpace Bool) :=
  {x |
    (x false = true ∧ ¬(x true = true)) ∨
    (¬(x false = true) ∧ x true = true)}

/-- Nonstrict up-configuration (`≤` instead of `<`) for the tie
counterexample. Mirrors `upConfig` with `Classical.propDecidable`. -/
noncomputable def nonstrictUpConfig (E : Type*) (T : E → ENNReal) (t : NNReal) :
    ConfigSpace E :=
  fun e => @decide ((t : ENNReal) ≤ T e) (Classical.propDecidable ((t : ENNReal) ≤ T e))

/-- Characterization of `nonstrictUpConfig`, mirroring
`upConfig_apply_eq_true` with `≤`. -/
theorem nonstrictUpConfig_apply_eq_true (E : Type*) (T : E → ENNReal) (t : NNReal)
    (e : E) :
    (nonstrictUpConfig E T t e = true ↔ (t : ENNReal) ≤ T e) :=
  ⟨@of_decide_eq_true _ (Classical.propDecidable _),
    @decide_eq_true _ (Classical.propDecidable _)⟩

/-- `0 < 1` in `NNReal`. -/
theorem zero_lt_one_nnreal : (0 : NNReal) < 1 :=
  zero_lt_one

/-- `0 ≤ 1` in `NNReal` from the strict fact. -/
theorem zero_le_one_nnreal : (0 : NNReal) ≤ 1 :=
  le_of_lt zero_lt_one_nnreal

/-- Finite-finite `0 < 1` in `ENNReal` via `NNReal` coercions. -/
theorem zero_lt_one_ennreal_coe :
    (((0 : NNReal) : ENNReal) < ((1 : NNReal) : ENNReal)) :=
  ENNReal.coe_lt_coe.mpr zero_lt_one_nnreal

/-- Tie is down: `¬(1 < 1)` in `ENNReal`. -/
theorem not_lt_self_one_ennreal_coe :
    ¬((((1 : NNReal) : ENNReal) < ((1 : NNReal) : ENNReal))) :=
  lt_irrefl _

/-- Tie is down: `¬(0 < 0)` in `ENNReal`. -/
theorem not_lt_self_zero_ennreal_coe :
    ¬((((0 : NNReal) : ENNReal) < ((0 : NNReal) : ENNReal))) :=
  lt_irrefl _

/-- Finite below top at `0`. -/
theorem coe_zero_lt_top_ennreal : (((0 : NNReal) : ENNReal) < (⊤ : ENNReal)) :=
  ENNReal.coe_lt_top

/-- Finite below top at `1`. -/
theorem coe_one_lt_top_ennreal : (((1 : NNReal) : ENNReal) < (⊤ : ENNReal)) :=
  ENNReal.coe_lt_top

/-- Series is increasing: application of the public
`Reliability.isIncreasing_seriesEvent`. -/
theorem isIncreasing_seriesEvent (E : Type*) :
    IsIncreasing (seriesEvent E) :=
  Reliability.isIncreasing_seriesEvent E

/-- Parallel is increasing: application of the public
`Reliability.isIncreasing_parallelEvent`. -/
theorem isIncreasing_parallelEvent (E : Type*) :
    IsIncreasing (parallelEvent E) :=
  Reliability.isIncreasing_parallelEvent E

/-- Empty event is increasing (vacuous, via `Set.notMem_empty`). -/
theorem isIncreasing_emptyEvent (E : Type*) :
    IsIncreasing (∅ : Set (ConfigSpace E)) := by
  intro x y _ hmem
  exact False.elim (Set.notMem_empty x hmem)

/-- Universal event is increasing (via `Set.mem_univ`). -/
theorem isIncreasing_univEvent (E : Type*) :
    IsIncreasing (Set.univ : Set (ConfigSpace E)) := by
  intro _ _ _ _
  exact Set.mem_univ _

/-- 2-of-3 is increasing. -/
theorem isIncreasing_twoOfThree : IsIncreasing twoOfThree := by
  intro x y hle hmem
  simp only [twoOfThree, Set.mem_ofPred_eq] at hmem ⊢
  rcases hmem with ⟨h0, h1⟩ | ⟨h0, h2⟩ | ⟨h1, h2⟩
  · left
    exact ⟨(Bool.le_iff_imp.mp (hle none)) h0,
      (Bool.le_iff_imp.mp (hle (some false))) h1⟩
  · right; left
    exact ⟨(Bool.le_iff_imp.mp (hle none)) h0,
      (Bool.le_iff_imp.mp (hle (some true))) h2⟩
  · right; right
    exact ⟨(Bool.le_iff_imp.mp (hle (some false))) h1,
      (Bool.le_iff_imp.mp (hle (some true))) h2⟩

/-- `upConfig` is `true` for strictly-up finite component at `t = 0`.
Application of `upConfig_apply_eq_true` plus independent `0 < 1`. -/
theorem upConfig_T3_zero_none_true :
    (upConfig (Option Bool) T3 0 none = true) := by
  rw [upConfig_apply_eq_true]
  show (((0 : NNReal) : ENNReal) < T3 none)
  have hT : T3 none = ((1 : NNReal) : ENNReal) := rfl
  rw [hT]
  exact zero_lt_one_ennreal_coe

/-- `upConfig` is `true` for infinite component at `t = 1`.
Application plus independent `coe_lt_top`. -/
theorem upConfig_T3_one_top_true :
    (upConfig (Option Bool) T3 1 (some true) = true) := by
  rw [upConfig_apply_eq_true]
  show (((1 : NNReal) : ENNReal) < T3 (some true))
  have hT : T3 (some true) = (⊤ : ENNReal) := rfl
  rw [hT]
  exact coe_one_lt_top_ennreal

/-- Tie is down: `upConfig` is not `true` at `t = 1` for `T = 1`.
Uses `upConfig_apply_eq_true` (application) and `lt_irrefl` (pin). -/
theorem upConfig_T3_one_none_not_true :
    ¬(upConfig (Option Bool) T3 1 none = true) := by
  rw [upConfig_apply_eq_true]
  show ¬((((1 : NNReal) : ENNReal) < T3 none))
  have hT : T3 none = ((1 : NNReal) : ENNReal) := rfl
  rw [hT]
  exact not_lt_self_one_ennreal_coe

/-- Zero tie is down: `T = 0`, `t = 0` gives `¬(upConfig = true)`. -/
theorem upConfig_T1_zero_not_true :
    ¬(upConfig Unit T1 0 () = true) := by
  rw [upConfig_apply_eq_true]
  show ¬((((0 : NNReal) : ENNReal) < T1 ()))
  have hT : T1 () = ((0 : NNReal) : ENNReal) := rfl
  rw [hT]
  exact not_lt_self_zero_ennreal_coe

/-- `configLifetime` of all-down is `⊤`: application of
`configLifetime_allFalse`. -/
theorem configLifetime_allFalse_Bool_pin :
    configLifetime Bool (fun _ => false) T2 = ⊤ :=
  configLifetime_allFalse Bool T2

/-- Independent pin for the all-down filter: selects nothing. -/
theorem configLifetime_allFalse_filter_Bool :
    (Finset.univ.filter (fun e : Bool => (fun _ => false) e = true)) = ∅ := by
  apply Finset.filter_false_of_mem
  intro e _
  simp

/-- `lt_configLifetime_iff` at a tie: all-true config with `T = [1, ⊤]`,
`t = 1`. Left `¬(1 < min)` and right `¬∀` pins plus the iff application. -/
theorem lt_configLifetime_iff_tie_Bool :
    (¬((((1 : NNReal) : ENNReal) < configLifetime Bool (fun _ => true) T2)) ∧
    ¬(∀ e : Bool, (fun _ => true) e = true → ((1 : NNReal) : ENNReal) < T2 e) ∧
    ((((1 : NNReal) : ENNReal) < configLifetime Bool (fun _ => true) T2) ↔
      ∀ e : Bool, (fun _ => true) e = true → ((1 : NNReal) : ENNReal) < T2 e)) := by
  have hT_false : T2 false = ((1 : NNReal) : ENNReal) := rfl
  have h_not_lt : ¬((((1 : NNReal) : ENNReal) < T2 false)) := by
    rw [hT_false]
    exact not_lt_self_one_ennreal_coe
  have h_right_false : ¬(∀ e : Bool, (fun _ => true) e = true →
      ((1 : NNReal) : ENNReal) < T2 e) := by
    intro h
    exact h_not_lt (h false rfl)
  have h_iff := lt_configLifetime_iff Bool (fun _ => true) T2 1
  have h_left_false : ¬((((1 : NNReal) : ENNReal) <
      configLifetime Bool (fun _ => true) T2)) := by
    rw [h_iff]
    exact h_right_false
  exact ⟨h_left_false, h_right_false, h_iff⟩

/-- `mem_seriesEvent` / `mem_parallelEvent` pins on `Bool`. -/
theorem mem_series_parallel_Bool_pins :
    ((fun _ : Bool => true) ∈ seriesEvent Bool) ∧
    ((fun _ : Bool => false) ∉ seriesEvent Bool) ∧
    ((fun _ : Bool => true) ∈ parallelEvent Bool) ∧
    ((fun _ : Bool => false) ∉ parallelEvent Bool) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mem_seriesEvent]
    intro _
    rfl
  · rw [mem_seriesEvent]
    intro h
    have hfalse : (fun _ : Bool => false) false = true := h false
    simp at hfalse
  · rw [mem_parallelEvent]
    exact ⟨false, rfl⟩
  · rw [mem_parallelEvent]
    rintro ⟨e, he⟩
    simp at he

/-- Independent pin: `inf T3 = 1` on `Option Bool` (ties + top). -/
theorem inf_T3_eq_one : Finset.univ.inf T3 = ((1 : NNReal) : ENNReal) := by
  apply le_antisymm
  · have h_le : Finset.univ.inf T3 ≤ T3 none :=
      Finset.inf_le (Finset.mem_univ none)
    have hT : T3 none = ((1 : NNReal) : ENNReal) := rfl
    rw [hT] at h_le
    exact h_le
  · apply Finset.le_inf
    intro i _
    cases i with
    | none => exact le_refl _
    | some b =>
      cases b with
      | false => exact le_refl _
      | true => exact le_top

/-- Independent pin: `sup T3 = ⊤` on `Option Bool`. -/
theorem sup_T3_eq_top : Finset.univ.sup T3 = (⊤ : ENNReal) := by
  apply le_antisymm le_top
  have h_ge : T3 (some true) ≤ Finset.univ.sup T3 :=
    Finset.le_sup (Finset.mem_univ (some true))
  have hT : T3 (some true) = (⊤ : ENNReal) := rfl
  rw [hT] at h_ge
  exact h_ge

/-- Series lifetime is `1` for `T3`: `systemLifetime_series` (application)
plus `inf_T3_eq_one` (independent pin). -/
theorem systemLifetime_series_T3_eq_one :
    systemLifetime (Option Bool) (seriesEvent (Option Bool)) T3 =
      ((1 : NNReal) : ENNReal) := by
  rw [systemLifetime_series]
  exact inf_T3_eq_one

/-- Parallel lifetime is `⊤` for `T3`: `systemLifetime_parallel`
(application) plus `sup_T3_eq_top` (independent pin). -/
theorem systemLifetime_parallel_T3_eq_top :
    systemLifetime (Option Bool) (parallelEvent (Option Bool)) T3 = ⊤ := by
  rw [systemLifetime_parallel]
  exact sup_T3_eq_top

/-- Series event identity at `t = 0` (all up): both sides true.
`t < 1` pin, membership pin, and `lt_systemLifetime_iff` application. -/
theorem lt_systemLifetime_series_T3_zero :
    (((0 : NNReal) : ENNReal) <
      systemLifetime (Option Bool) (seriesEvent (Option Bool)) T3) ∧
    (upConfig (Option Bool) T3 0 ∈ seriesEvent (Option Bool)) ∧
    (((((0 : NNReal) : ENNReal) <
      systemLifetime (Option Bool) (seriesEvent (Option Bool)) T3) ↔
      upConfig (Option Bool) T3 0 ∈ seriesEvent (Option Bool)) ) := by
  have h_series := systemLifetime_series_T3_eq_one
  have h_lt : (((0 : NNReal) : ENNReal) <
      systemLifetime (Option Bool) (seriesEvent (Option Bool)) T3) := by
    rw [h_series]
    exact zero_lt_one_ennreal_coe
  have h_mem : upConfig (Option Bool) T3 0 ∈ seriesEvent (Option Bool) := by
    rw [mem_seriesEvent]
    intro i
    cases i with
    | none =>
      rw [upConfig_apply_eq_true]
      show (((0 : NNReal) : ENNReal) < T3 none)
      have hT : T3 none = ((1 : NNReal) : ENNReal) := rfl
      rw [hT]
      exact zero_lt_one_ennreal_coe
    | some b =>
      cases b with
      | false =>
        rw [upConfig_apply_eq_true]
        show (((0 : NNReal) : ENNReal) < T3 (some false))
        have hT : T3 (some false) = ((1 : NNReal) : ENNReal) := rfl
        rw [hT]
        exact zero_lt_one_ennreal_coe
      | true =>
        rw [upConfig_apply_eq_true]
        show (((0 : NNReal) : ENNReal) < T3 (some true))
        have hT : T3 (some true) = (⊤ : ENNReal) := rfl
        rw [hT]
        exact coe_zero_lt_top_ennreal
  have h_iff := lt_systemLifetime_iff (Option Bool) (seriesEvent (Option Bool)) T3 0
    (isIncreasing_seriesEvent (Option Bool))
  exact ⟨h_lt, h_mem, h_iff⟩

/-- Series event identity at tie `t = 1`: both sides false. -/
theorem lt_systemLifetime_series_T3_one_tie :
    (¬((((1 : NNReal) : ENNReal) <
      systemLifetime (Option Bool) (seriesEvent (Option Bool)) T3)) ∧
    (upConfig (Option Bool) T3 1 ∉ seriesEvent (Option Bool)) ∧
    (((((1 : NNReal) : ENNReal) <
      systemLifetime (Option Bool) (seriesEvent (Option Bool)) T3) ↔
      upConfig (Option Bool) T3 1 ∈ seriesEvent (Option Bool))) ) := by
  have h_series := systemLifetime_series_T3_eq_one
  have h_not_lt : ¬((((1 : NNReal) : ENNReal) <
      systemLifetime (Option Bool) (seriesEvent (Option Bool)) T3)) := by
    rw [h_series]
    exact not_lt_self_one_ennreal_coe
  have h_not_mem : upConfig (Option Bool) T3 1 ∉ seriesEvent (Option Bool) := by
    rw [mem_seriesEvent]
    intro h
    have h_none : upConfig (Option Bool) T3 1 none = true := h none
    rw [upConfig_apply_eq_true] at h_none
    have hT : T3 none = ((1 : NNReal) : ENNReal) := rfl
    rw [hT] at h_none
    exact not_lt_self_one_ennreal_coe h_none
  have h_iff := lt_systemLifetime_iff (Option Bool) (seriesEvent (Option Bool)) T3 1
    (isIncreasing_seriesEvent (Option Bool))
  exact ⟨h_not_lt, h_not_mem, h_iff⟩

/-- Parallel event identity at tie `t = 1`: both sides true via the
infinite component. -/
theorem lt_systemLifetime_parallel_T3_one_tie :
    (((1 : NNReal) : ENNReal) <
      systemLifetime (Option Bool) (parallelEvent (Option Bool)) T3) ∧
    (upConfig (Option Bool) T3 1 ∈ parallelEvent (Option Bool)) ∧
    (((((1 : NNReal) : ENNReal) <
      systemLifetime (Option Bool) (parallelEvent (Option Bool)) T3) ↔
      upConfig (Option Bool) T3 1 ∈ parallelEvent (Option Bool)) ) := by
  have h_par := systemLifetime_parallel_T3_eq_top
  have h_lt : (((1 : NNReal) : ENNReal) <
      systemLifetime (Option Bool) (parallelEvent (Option Bool)) T3) := by
    rw [h_par]
    exact coe_one_lt_top_ennreal
  have h_mem : upConfig (Option Bool) T3 1 ∈ parallelEvent (Option Bool) := by
    rw [mem_parallelEvent]
    exact ⟨some true, upConfig_T3_one_top_true⟩
  have h_iff := lt_systemLifetime_iff (Option Bool) (parallelEvent (Option Bool)) T3 1
    (isIncreasing_parallelEvent (Option Bool))
  exact ⟨h_lt, h_mem, h_iff⟩

/-- 2-of-3 at `t = 0`: all three up, so in event. Membership pin plus
iff application (lifetime side via the same `T3` pins). -/
theorem lt_systemLifetime_twoOfThree_T3_zero :
    ((upConfig (Option Bool) T3 0 ∈ twoOfThree) ∧
    (((((0 : NNReal) : ENNReal) <
      systemLifetime (Option Bool) twoOfThree T3) ↔
      upConfig (Option Bool) T3 0 ∈ twoOfThree)) ) := by
  have h0 : upConfig (Option Bool) T3 0 none = true := upConfig_T3_zero_none_true
  have h1 : upConfig (Option Bool) T3 0 (some false) = true := by
    rw [upConfig_apply_eq_true]
    show (((0 : NNReal) : ENNReal) < T3 (some false))
    have hT : T3 (some false) = ((1 : NNReal) : ENNReal) := rfl
    rw [hT]
    exact zero_lt_one_ennreal_coe
  have h_mem : upConfig (Option Bool) T3 0 ∈ twoOfThree := by
    simp only [twoOfThree, Set.mem_ofPred_eq]
    left
    exact ⟨h0, h1⟩
  have h_iff := lt_systemLifetime_iff (Option Bool) twoOfThree T3 0
    isIncreasing_twoOfThree
  exact ⟨h_mem, h_iff⟩

/-- 2-of-3 at tie `t = 1`: only the infinite component up, so not in
event (needs two). Uses tie-down pins plus iff application. -/
theorem lt_systemLifetime_twoOfThree_T3_one_tie :
    ((upConfig (Option Bool) T3 1 ∉ twoOfThree) ∧
    (((((1 : NNReal) : ENNReal) <
      systemLifetime (Option Bool) twoOfThree T3) ↔
      upConfig (Option Bool) T3 1 ∈ twoOfThree)) ) := by
  have h_not0 : ¬(upConfig (Option Bool) T3 1 none = true) :=
    upConfig_T3_one_none_not_true
  have h_not1 : ¬(upConfig (Option Bool) T3 1 (some false) = true) := by
    rw [upConfig_apply_eq_true]
    show ¬((((1 : NNReal) : ENNReal) < T3 (some false)))
    have hT : T3 (some false) = ((1 : NNReal) : ENNReal) := rfl
    rw [hT]
    exact not_lt_self_one_ennreal_coe
  have h_not_mem : upConfig (Option Bool) T3 1 ∉ twoOfThree := by
    simp only [twoOfThree, Set.mem_ofPred_eq]
    rintro (⟨h0, _⟩ | ⟨h0, _⟩ | ⟨h1, _⟩)
    · exact h_not0 h0
    · exact h_not0 h0
    · exact h_not1 h1
  have h_iff := lt_systemLifetime_iff (Option Bool) twoOfThree T3 1
    isIncreasing_twoOfThree
  exact ⟨h_not_mem, h_iff⟩

/-- Empty components: series event is `univ` (application of
`seriesEvent_empty`). -/
theorem seriesEvent_empty_pin : seriesEvent Empty = Set.univ :=
  seriesEvent_empty Empty

/-- Empty components: parallel event is `∅` (application of
`parallelEvent_empty`). -/
theorem parallelEvent_empty_pin : parallelEvent Empty = ∅ :=
  parallelEvent_empty Empty

/-- Independent pins for empty `Finset.univ`: `inf = ⊤`, `sup = 0`. -/
theorem empty_univ_inf_sup_pins :
    (Finset.univ.inf T0 = (⊤ : ENNReal)) ∧
    (Finset.univ.sup T0 = (0 : ENNReal)) := by
  have h_univ : (Finset.univ : Finset Empty) = ∅ := Finset.univ_eq_empty
  constructor
  · rw [h_univ, Finset.inf_empty]
  · rw [h_univ, Finset.sup_empty]
    exact ENNReal.bot_eq_zero

/-- Empty components: series lifetime `⊤` via `systemLifetime_series_empty`
(application) and via `systemLifetime_series` + independent `inf` pin. -/
theorem systemLifetime_series_empty_pins :
    (systemLifetime Empty (seriesEvent Empty) T0 = (⊤ : ENNReal)) ∧
    (systemLifetime Empty (seriesEvent Empty) T0 = Finset.univ.inf T0) := by
  exact ⟨systemLifetime_series_empty Empty T0, systemLifetime_series Empty T0⟩

/-- Empty components: parallel lifetime `0` via `systemLifetime_parallel_empty`
(application) and via `systemLifetime_parallel` + independent `sup` pin. -/
theorem systemLifetime_parallel_empty_pins :
    (systemLifetime Empty (parallelEvent Empty) T0 = (0 : ENNReal)) ∧
    (systemLifetime Empty (parallelEvent Empty) T0 = Finset.univ.sup T0) := by
  exact ⟨systemLifetime_parallel_empty Empty T0, systemLifetime_parallel Empty T0⟩

/-- Never-up boundary: `systemLifetime ∅ = 0` (application of
`systemLifetime_empty`). -/
theorem systemLifetime_empty_pin_Bool :
    systemLifetime Bool ∅ T2 = (0 : ENNReal) := by
  exact systemLifetime_empty Bool T2

/-- Always-up boundary: `systemLifetime univ = ⊤` (application of
`systemLifetime_univ`). -/
theorem systemLifetime_univ_pin_Bool :
    systemLifetime Bool Set.univ T2 = (⊤ : ENNReal) := by
  exact systemLifetime_univ Bool T2

/-- Never-up event identity at `t = 0`: both sides false.
Independent `¬(0 < 0)` and `∉ ∅` pins plus `lt_systemLifetime_iff`. -/
theorem lt_systemLifetime_empty_Bool_zero :
    (¬((((0 : NNReal) : ENNReal) < systemLifetime Bool ∅ T2)) ∧
    (upConfig Bool T2 0 ∉ (∅ : Set (ConfigSpace Bool))) ∧
    (((((0 : NNReal) : ENNReal) < systemLifetime Bool ∅ T2) ↔
      upConfig Bool T2 0 ∈ (∅ : Set (ConfigSpace Bool)))) ) := by
  have h_empty := systemLifetime_empty_pin_Bool
  have h_not_lt : ¬((((0 : NNReal) : ENNReal) < systemLifetime Bool ∅ T2)) := by
    rw [h_empty]
    exact not_lt_self_zero_ennreal_coe
  have h_not_mem : upConfig Bool T2 0 ∉ (∅ : Set (ConfigSpace Bool)) :=
    Set.notMem_empty _
  have h_iff := lt_systemLifetime_iff Bool ∅ T2 0 (isIncreasing_emptyEvent Bool)
  exact ⟨h_not_lt, h_not_mem, h_iff⟩

/-- Always-up event identity at `t = 0`: both sides true.
Independent `0 < ⊤` and `∈ univ` pins plus `lt_systemLifetime_iff`. -/
theorem lt_systemLifetime_univ_Bool_zero :
    ((((0 : NNReal) : ENNReal) < systemLifetime Bool Set.univ T2) ∧
    (upConfig Bool T2 0 ∈ (Set.univ : Set (ConfigSpace Bool))) ∧
    (((((0 : NNReal) : ENNReal) < systemLifetime Bool Set.univ T2) ↔
      upConfig Bool T2 0 ∈ (Set.univ : Set (ConfigSpace Bool)))) ) := by
  have h_univ := systemLifetime_univ_pin_Bool
  have h_lt : (((0 : NNReal) : ENNReal) < systemLifetime Bool Set.univ T2) := by
    rw [h_univ]
    exact coe_zero_lt_top_ennreal
  have h_mem : upConfig Bool T2 0 ∈ (Set.univ : Set (ConfigSpace Bool)) :=
    Set.mem_univ _
  have h_iff := lt_systemLifetime_iff Bool Set.univ T2 0 (isIncreasing_univEvent Bool)
  exact ⟨h_lt, h_mem, h_iff⟩

/-- Measurable constant lifetimes on `Unit`: each `T e` measurable via
`measurable_const` (independent pin). -/
noncomputable def T_meas : Option Bool → Unit → ENNReal := fun e _ => T3 e

theorem measurable_T_meas (e : Option Bool) : Measurable (T_meas e) :=
  measurable_const

/-- System lifetime measurability: application of
`measurable_systemLifetime` to constant (hence measurable) components. -/
theorem measurable_systemLifetime_T_meas :
    Measurable (fun ω : Unit => systemLifetime (Option Bool) twoOfThree
      (fun e => T_meas e ω)) := by
  exact measurable_systemLifetime (Option Bool) twoOfThree Unit T_meas
    measurable_T_meas

/-- XOR is not increasing: `[false, true]` in event, below `[true, true]`
not in event. Negative example, no `IsIncreasing` hypothesis. -/
theorem xorEvent_not_increasing : ¬IsIncreasing xorEvent := by
  intro h
  let x : ConfigSpace Bool := fun b => b
  let y : ConfigSpace Bool := fun _ => true
  have hx_false : x false = false := rfl
  have hx_true : x true = true := rfl
  have hy_false : y false = true := rfl
  have hy_true : y true = true := rfl
  have h_not_false_true : ¬(x false = true) := by
    rw [hx_false]
    simp
  have h_mem : x ∈ xorEvent := by
    simp only [xorEvent, Set.mem_ofPred_eq]
    right
    exact ⟨h_not_false_true, hx_true⟩
  have hle : x ≤ y := fun b => Bool.le_iff_imp.mpr (fun _ => rfl)
  have hy : y ∈ xorEvent := h hle h_mem
  simp only [xorEvent, Set.mem_ofPred_eq] at hy
  rcases hy with ⟨h0, h_not1⟩ | ⟨h_not0, h1⟩
  · exact h_not1 hy_true
  · exact h_not0 hy_false

/-- XOR up times are not an initial segment: at `t = 0` both up
(`[true, true]`, not XOR), at `t = 1` exactly one up (`[false, true]`,
XOR), with `0 ≤ 1`. Holds later but fails earlier. -/
theorem xorEvent_not_initial_segment :
    (upConfig Bool T2 0 ∉ xorEvent) ∧
    (upConfig Bool T2 1 ∈ xorEvent) ∧
    ((0 : NNReal) ≤ 1) := by
  have hT_false : T2 false = ((1 : NNReal) : ENNReal) := rfl
  have hT_true : T2 true = (⊤ : ENNReal) := rfl
  have h0_false : upConfig Bool T2 0 false = true := by
    rw [upConfig_apply_eq_true]
    show (((0 : NNReal) : ENNReal) < T2 false)
    rw [hT_false]
    exact zero_lt_one_ennreal_coe
  have h0_true : upConfig Bool T2 0 true = true := by
    rw [upConfig_apply_eq_true]
    show (((0 : NNReal) : ENNReal) < T2 true)
    rw [hT_true]
    exact coe_zero_lt_top_ennreal
  have h_not_mem0 : upConfig Bool T2 0 ∉ xorEvent := by
    simp only [xorEvent, Set.mem_ofPred_eq]
    rintro (⟨_, h_not⟩ | ⟨h_not, _⟩)
    · exact h_not h0_true
    · exact h_not h0_false
  have h_not1_false : ¬(upConfig Bool T2 1 false = true) := by
    rw [upConfig_apply_eq_true]
    show ¬((((1 : NNReal) : ENNReal) < T2 false))
    rw [hT_false]
    exact not_lt_self_one_ennreal_coe
  have h1_true : upConfig Bool T2 1 true = true := by
    rw [upConfig_apply_eq_true]
    show (((1 : NNReal) : ENNReal) < T2 true)
    rw [hT_true]
    exact coe_one_lt_top_ennreal
  have h_mem1 : upConfig Bool T2 1 ∈ xorEvent := by
    simp only [xorEvent, Set.mem_ofPred_eq]
    right
    exact ⟨h_not1_false, h1_true⟩
  exact ⟨h_not_mem0, h_mem1, zero_le_one_nnreal⟩

/-- Strict tie pins for `T1 = 0`, `t = 0` on `Unit`: `¬(0 < 0)` (pin),
`upConfig ∉ series` (via `upConfig_apply_eq_true` + `mem_seriesEvent`),
and `¬(t < lifetime)` via `lt_systemLifetime_iff`. Valid control for the
nonstrict counterexample below. -/
theorem strict_tie_T1_series_false :
    (¬((((0 : NNReal) : ENNReal) < T1 ())) ∧
    (upConfig Unit T1 0 ∉ seriesEvent Unit) ∧
    (¬((((0 : NNReal) : ENNReal) <
      systemLifetime Unit (seriesEvent Unit) T1))) ∧
    (((((0 : NNReal) : ENNReal) <
      systemLifetime Unit (seriesEvent Unit) T1) ↔
      upConfig Unit T1 0 ∈ seriesEvent Unit)) ) := by
  have hT : T1 () = ((0 : NNReal) : ENNReal) := rfl
  have h_not_lt_T : ¬((((0 : NNReal) : ENNReal) < T1 ())) := by
    rw [hT]
    exact not_lt_self_zero_ennreal_coe
  have h_not_true : ¬(upConfig Unit T1 0 () = true) := upConfig_T1_zero_not_true
  have h_not_mem : upConfig Unit T1 0 ∉ seriesEvent Unit := by
    rw [mem_seriesEvent]
    intro h
    exact h_not_true (h ())
  have h_iff := lt_systemLifetime_iff Unit (seriesEvent Unit) T1 0
    (isIncreasing_seriesEvent Unit)
  have h_not_lt_sys : ¬((((0 : NNReal) : ENNReal) <
      systemLifetime Unit (seriesEvent Unit) T1)) := by
    rw [h_iff]
    exact h_not_mem
  exact ⟨h_not_lt_T, h_not_mem, h_not_lt_sys, h_iff⟩

/-- Nonstrict (`≤`) fails at the tie: `0 ≤ 0` holds so nonstrict up is
`true` and in series, while strict `t < lifetime` is false. The
advertised `↔` with `≤` is false. Uses `nonstrictUpConfig_apply_eq_true`
(pin) and the strict control above (non-vacuous: strict holds). -/
theorem nonstrict_tie_counterexample :
    ((nonstrictUpConfig Unit T1 0 () = true) ∧
    (nonstrictUpConfig Unit T1 0 ∈ seriesEvent Unit) ∧
    (¬((((0 : NNReal) : ENNReal) <
      systemLifetime Unit (seriesEvent Unit) T1) ↔
      nonstrictUpConfig Unit T1 0 ∈ seriesEvent Unit)) ) := by
  have h_le : (((0 : NNReal) : ENNReal) ≤ T1 ()) := le_refl _
  have h_true : nonstrictUpConfig Unit T1 0 () = true := by
    rw [nonstrictUpConfig_apply_eq_true]
    exact h_le
  have h_mem : nonstrictUpConfig Unit T1 0 ∈ seriesEvent Unit := by
    rw [mem_seriesEvent]
    intro u
    cases u with
    | unit => exact h_true
  have h_strict := strict_tie_T1_series_false
  obtain ⟨_, _, h_not_lt_sys, _⟩ := h_strict
  have h_not_iff : ¬((((0 : NNReal) : ENNReal) <
      systemLifetime Unit (seriesEvent Unit) T1) ↔
      nonstrictUpConfig Unit T1 0 ∈ seriesEvent Unit) :=
    fun h => h_not_lt_sys (h.mpr h_mem)
  exact ⟨h_true, h_mem, h_not_iff⟩

/-- Importing-client check: the survival identity states and applies for an
abstract finite component type and an arbitrary event, with no
decision-instance binders. -/
theorem lt_systemLifetime_iff_abstractClient (E : Type*) [Fintype E]
    (A : Set (ConfigSpace E)) (T : E → ENNReal) (t : NNReal)
    (hA : IsIncreasing A) :
    ((t : ENNReal) < systemLifetime E A T ↔ upConfig E T t ∈ A) :=
  lt_systemLifetime_iff E A T t hA

/-- Importing-client check: measurability states and applies for an abstract
finite component type and an arbitrary event, with no decision-instance
binders. -/
theorem measurable_systemLifetime_abstractClient (E : Type*) [Fintype E]
    (A : Set (ConfigSpace E)) (Ω : Type*) [MeasurableSpace Ω]
    (T : E → Ω → ENNReal) (hT : ∀ e, Measurable (T e)) :
    Measurable (fun ω => systemLifetime E A (fun e => T e ω)) :=
  measurable_systemLifetime E A Ω T hT

/-- Importing-client check: the public series monotonicity lemma applies to
the generic survival identity for an abstract finite component type, with no
copied monotonicity proof. -/
theorem lt_systemLifetime_series_abstractClient (E : Type*) [Fintype E]
    (T : E → ENNReal) (t : NNReal) :
    ((t : ENNReal) < systemLifetime E (seriesEvent E) T ↔
      upConfig E T t ∈ seriesEvent E) :=
  lt_systemLifetime_iff E (seriesEvent E) T t
    (Reliability.isIncreasing_seriesEvent E)

/-- Importing-client check: the public parallel monotonicity lemma applies to
the generic survival identity for an abstract finite component type, with no
copied monotonicity proof. -/
theorem lt_systemLifetime_parallel_abstractClient (E : Type*) [Fintype E]
    (T : E → ENNReal) (t : NNReal) :
    ((t : ENNReal) < systemLifetime E (parallelEvent E) T ↔
      upConfig E T t ∈ parallelEvent E) :=
  lt_systemLifetime_iff E (parallelEvent E) T t
    (Reliability.isIncreasing_parallelEvent E)

/-- Importing-client check: series identity with the public monotonicity
lemma on empty components. -/
theorem lt_systemLifetime_series_emptyClient :
    (((0 : NNReal) : ENNReal) < systemLifetime Empty (seriesEvent Empty) T0 ↔
      upConfig Empty T0 0 ∈ seriesEvent Empty) :=
  lt_systemLifetime_iff Empty (seriesEvent Empty) T0 0
    (Reliability.isIncreasing_seriesEvent Empty)

/-- Importing-client check: parallel identity with the public monotonicity
lemma on empty components. -/
theorem lt_systemLifetime_parallel_emptyClient :
    (((0 : NNReal) : ENNReal) <
      systemLifetime Empty (parallelEvent Empty) T0 ↔
      upConfig Empty T0 0 ∈ parallelEvent Empty) :=
  lt_systemLifetime_iff Empty (parallelEvent Empty) T0 0
    (Reliability.isIncreasing_parallelEvent Empty)

end ReliabilityTest
