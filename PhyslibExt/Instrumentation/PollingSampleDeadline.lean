/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Foundations.Semantics.Peripheral.ProducerInterruptSimulation
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Polling deadline for an overwrite-newest sample register

## i. Overview

A driver polls a single-slot sample register whose newest publication
overwrites the previous one. The closed system is the one of
`Cslib.Semantics.Peripheral.ProducerInterruptSimulation`: the polling
driver, other publishers and readers of the register, and a producer
interrupt that satisfies the rely condition `Rely`, interleaved as
sequentially consistent atomic steps. A costed polling trace is a run of
that system in which every step carries its clock-cycle charge as a
`Cslib.Algorithms.Lean.TimeM ℕ` value: `ret` is the step and `time` the
cycles since the previous step completed. Step `i` completes at the sum
of the charges of steps `0, …, i`, and at that cycle count divided by
the clock frequency `fclk` in seconds. The charges are trusted inputs of
the cost model, not derived worst-case execution times.

The premises hold at every publication, by the environment or by the
interrupt, not only at a loop entry:

- any two publications are at least `Tmin` seconds apart
  (`PublicationGap`);
- after a publication, a driver Ready check completes within `Cpoll`
  cycles, and if it observes Ready a driver read completes within
  `Cread` further cycles; interrupt cycles charged in the window are
  added and bounded by `Cirq`, and bus allowances are added and bounded
  by `Cbus` (`RespondsWithin`);
- `0 < fclk`, `0 < Tmin` and `(Cpoll + Cread + Cirq + Cbus) / fclk < Tmin`.

Then no publication is lost: each is read before the next one, within
the response budget, and each successful read returns the latest
publication.

The driver-side clause carries one extra hypothesis, `NoOtherReader`:
the driver is the only reader of the register. The system model permits
other readers, and a read by another reader also empties the slot. Without
this hypothesis the driver-side clause is false: if another reader takes
a publication before the driver's Ready check, every timing premise
holds, the publication is read, yet the driver returns no ID while one
sample was published. The reader-agnostic clauses need no such
hypothesis.

`Cbus` is an allowance only: the system has no bus event, so the bus
delays are existential slack bounded by `Cbus`, while `Cirq` is checked
against the charges of actual interrupt steps. Acquisition timestamps
are supplied, not modelled, so no acquisition-to-read age is claimed
beyond the publication-to-read latency.

## ii. Key results

- `exists_read_before_next_publication`: every publication of `(n, v)`
  is read as `some (n, v)` within `Cpoll + Cread + Cirq + Cbus` cycles
  and before any later publication.
- `exists_fresh_publication_of_read`: every successful read returns the
  latest earlier publication, with no publication in between, within
  the same cycle budget.
- `exists_driver_read_before_next_publication`: with a sole reader,
  every publication is returned by a driver read before the next one.
- `driverReadIds_eq_publicationIds`: with a sole reader, the IDs
  returned by the driver are the publication IDs, in order.
- `pollingSampleDeadline_correct`: the three clauses in physical time,
  with the IDs composed with supplied acquisition timestamps.
- `worstPhase_valid`, `budget_not_strict_loses`,
  `delayedInterrupt_loses`: a worst-phase run that meets every premise
  and loses nothing, and runs showing that a budget equal to or above
  the gap, or an interrupt stall beyond `Cirq`, loses a publication.

## iii. Table of contents

- A. Costed polling traces
- B. Timing premises
- C. Slot and cycle infrastructure
- D. The polling deadline
- E. Validation

## iv. References

- M. Joseph and P. Pandya, "Finding response times in a real-time
  system", *The Computer Journal* 29(5), 390–395, 1986: response time
  as computation plus interference, here the polling and read costs
  plus interrupt and bus delays.
- G. C. Buttazzo, *Hard Real-Time Computing Systems: Predictable
  Scheduling Algorithms and Applications*, 3rd ed., Springer, 2011:
  deadlines for periodic sampling and interrupt handling.
-/

@[expose] public section

universe u v

namespace PhyslibExt.Instrumentation.PollingSampleDeadline

open Cslib.Algorithms.Lean
open Cslib.Semantics.Peripheral.OverwriteSampleRegister
open Cslib.Semantics.Peripheral.SampleReadyProtocol
open Cslib.Semantics.Peripheral.PollDriverSimulation
open Cslib.Semantics.Peripheral.ProducerInterruptSimulation

/-! ## A. Costed polling traces -/

/-- A costed polling trace: the steps of a run of the closed driver/interrupt/register system,
each paired, as a `TimeM ℕ` value, with the clock cycles it is charged in the explicit cost model.
`ret` is the step label and `time` the cycles elapsed since the previous step completed. The
charges are trusted cost-model inputs, not extracted worst-case execution times. -/
abbrev CostedTrace (α : Type u) : Type u :=
  List (TimeM ℕ (SystemLabel α))

/-- The step labels of a costed trace, in order. -/
def labels {α : Type u} (tr : CostedTrace α) : List (SystemLabel α) :=
  tr.map TimeM.ret

/-- The clock cycle at which step `i` completes: the cycles charged to steps `0, …, i`. -/
def cycleAt {α : Type u} (tr : CostedTrace α) (i : ℕ) : ℕ :=
  ((tr.take (i + 1)).map TimeM.time).sum

/-- The physical completion time, in seconds, of step `i` at clock frequency `fclk` (in Hz). -/
noncomputable def timeAt {α : Type u} (fclk : ℝ) (tr : CostedTrace α) (i : ℕ) : ℝ :=
  (cycleAt tr i : ℝ) / fclk

/-- Whether a system step is a step of the producer interrupt. -/
def isInterruptStep {α : Type u} : SystemLabel α → Bool
  | .interrupt _ => true
  | .driver _ => false

/-- The cycles charged to producer-interrupt steps whose index lies in the window `(a, b]`. -/
def interruptCycles {α : Type u} (tr : CostedTrace α) (a b : ℕ) : ℕ :=
  ((((tr.drop (a + 1)).take (b - a)).filter fun c => isInterruptStep c.ret).map
    TimeM.time).sum

/-- The sample published by step `i` (by the environment or by the interrupt), if any. -/
def publicationAt {α : Type u} (tr : CostedTrace α) (i : ℕ) : Option (ℕ × α) :=
  ((labels tr)[i]?).bind publication?

/-- The result of a register read performed by a system step, by the driver or by another
reader, if the step is a read. -/
def readResult? {α : Type u} : SystemLabel α → Option (Option (ℕ × α))
  | .driver (.visible (.read r)) => some r
  | .driver (.visible (.env (.read r))) => some r
  | _ => none

/-- The driver is the only reader of the register: no other reader's read occurs. -/
def NoOtherReader {α : Type u} (ms : List (SystemLabel α)) : Prop :=
  ∀ (k : ℕ) (r : Option (ℕ × α)), ms[k]? ≠ some (.driver (.visible (.env (.read r))))

/-- The IDs returned by the driver's successful reads, in order. -/
def driverReadIds {α : Type u} (ms : List (SystemLabel α)) : List ℕ :=
  ms.filterMap fun
    | .driver (.visible (.read (some (n, _)))) => some n
    | _ => none

/-- The IDs of all publications (by the environment or by the interrupt), in order. -/
def publicationIds {α : Type u} (ms : List (SystemLabel α)) : List ℕ :=
  ms.filterMap fun m => (publication? m).map Prod.fst

/-- Composition of sample IDs with their supplied acquisition timestamps `acq`. -/
def stampSamples (acq : ℕ → ℝ) (ids : List ℕ) : List (ℕ × ℝ) :=
  ids.map fun n => (n, acq n)

/-! ## B. Timing premises -/

/-- **Inter-publication gap.** Any two publications of the trace are at least `Tmin` seconds
apart at clock frequency `fclk`. -/
def PublicationGap {α : Type u} (fclk Tmin : ℝ) (tr : CostedTrace α) : Prop :=
  ∀ i j : ℕ, i < j → (publicationAt tr i).isSome → (publicationAt tr j).isSome →
    Tmin ≤ timeAt fclk tr j - timeAt fclk tr i

/-- **Costed polling response at step `i`.** A driver Ready check `p > i` completes within
`Cpoll` cycles of step `i`, plus the interrupt cycles charged in `(i, p]`, plus a bus allowance
`bus₁`; if it observes Ready, a driver read `r > p` completes within `Cread` further cycles, plus
the interrupt cycles in `(p, r]`, plus a bus allowance `bus₂`. The interrupt cycles over the
response window are at most `Cirq` and the bus allowances total at most `Cbus`. -/
def RespondsWithin {α : Type u} (Cpoll Cread Cirq Cbus : ℕ) (tr : CostedTrace α) (i : ℕ) :
    Prop :=
  ∃ p, i < p ∧ (∃ b, (labels tr)[p]? = some (.driver (.visible (.poll b)))) ∧
    ∃ bus₁ bus₂ : ℕ, bus₁ + bus₂ ≤ Cbus ∧
      cycleAt tr p ≤ cycleAt tr i + Cpoll + interruptCycles tr i p + bus₁ ∧
      interruptCycles tr i p ≤ Cirq ∧
      ((labels tr)[p]? = some (.driver (.visible (.poll true))) →
        ∃ r, p < r ∧ (∃ res, (labels tr)[r]? = some (.driver (.visible (.read res)))) ∧
          cycleAt tr r ≤ cycleAt tr p + Cread + interruptCycles tr p r + bus₂ ∧
          interruptCycles tr i r ≤ Cirq)

/-! ## C. Slot and cycle infrastructure -/

/-- Effect of one system step on the register slot: a publication stores its sample, a read
clears the slot, every other step leaves it unchanged. -/
private def stepSlot {α : Type u} (s : Slot α) (m : SystemLabel α) : Slot α :=
  match publication? m with
  | some p => some p
  | none =>
    match readResult? m with
    | some _ => none
    | none => s

/-- The register slot before step `k` of a run from the empty slot. -/
private def slotAt {α : Type u} (ms : List (SystemLabel α)) (k : ℕ) : Slot α :=
  (ms.take k).foldl stepSlot none

/-- Step `k` neither publishes nor reads. -/
private def Quiet {α : Type u} (ms : List (SystemLabel α)) (k : ℕ) : Prop :=
  (ms[k]?).bind publication? = none ∧ (ms[k]?).bind readResult? = none

private theorem stepSlot_of_pub {α : Type u} {s : Slot α} {m : SystemLabel α} {p : ℕ × α}
    (h : publication? m = some p) : stepSlot s m = some p := by
  simp [stepSlot, h]

private theorem stepSlot_of_read {α : Type u} {s : Slot α} {m : SystemLabel α}
    {r : Option (ℕ × α)} (hp : publication? m = none) (h : readResult? m = some r) :
    stepSlot s m = none := by
  simp [stepSlot, hp, h]

private theorem stepSlot_of_quiet {α : Type u} {s : Slot α} {m : SystemLabel α}
    (hp : publication? m = none) (h : readResult? m = none) : stepSlot s m = s := by
  simp [stepSlot, hp, h]

private theorem readResult_eq_none_of_pub {α : Type u} {m : SystemLabel α} {p : ℕ × α}
    (h : publication? m = some p) : readResult? m = none := by
  unfold publication? at h
  split at h <;> first | rfl | cases h

/-- One system step under the rely condition: its effect on the slot is `stepSlot`, a read
returns the current slot, and a Ready check observes the current slot. -/
private theorem step_facts {σ : Type v} {α : Type u} {H : InterruptHandler σ α} (hH : Rely H)
    {x x' : SystemState σ α} {m : SystemLabel α} (h : (systemLTS H).Tr x m x') :
    x'.slot = stepSlot x.slot m ∧ (∀ r, readResult? m = some r → r = x.slot) ∧
      (∀ b, m = .driver (.visible (.poll b)) → b = ready x.slot) := by
  change SystemStep H x m x' at h
  cases h with
  | driver q hp =>
    cases hp with
    | env d hr =>
      cases hr with
      | publish n v =>
        exact ⟨rfl, fun r hr => by simp [readResult?] at hr, fun b hb => by simp at hb⟩
      | read =>
        refine ⟨rfl, fun r hr => ?_, fun b hb => by simp at hb⟩
        simp only [readResult?, Option.some.injEq] at hr
        exact hr.symm
    | loadReady d s hpc =>
      refine ⟨rfl, fun r hr => by simp [readResult?] at hr, fun b hb => ?_⟩
      simp only [SystemLabel.driver.injEq, StepLabel.visible.injEq,
        DriverLabel.poll.injEq] at hb
      exact hb.symm
    | readyTaken d s hpc hr =>
      exact ⟨rfl, fun r hr => by simp [readResult?] at hr, fun b hb => by simp at hb⟩
    | readyNotTaken d s hpc hr =>
      exact ⟨rfl, fun r hr => by simp [readResult?] at hr, fun b hb => by simp at hb⟩
    | loadData d hpc hr =>
      cases hr with
      | read =>
        refine ⟨rfl, fun r hr => ?_, fun b hb => by simp at hb⟩
        simp only [readResult?, Option.some.injEq] at hr
        exact hr.symm
    | dataPresent d s n v hpc hd =>
      exact ⟨rfl, fun r hr => by simp [readResult?] at hr, fun b hb => by simp at hb⟩
    | dataAbsent d s hpc hd =>
      exact ⟨rfl, fun r hr => by simp [readResult?] at hr, fun b hb => by simp at hb⟩
    | emit d s n v hpc hd =>
      exact ⟨rfl, fun r hr => by simp [readResult?] at hr, fun b hb => by simp at hb⟩
    | record d s hpc =>
      exact ⟨rfl, fun r hr => by simp [readResult?] at hr, fun b hb => by simp at hb⟩
  | @interrupt _ _ a hi =>
    obtain ⟨-, hs⟩ := hH _ _ _ hi
    cases a with
    | localStep =>
      have hs' : _ = _ := hs
      exact ⟨hs', fun r hr => by simp [readResult?] at hr, fun b hb => by simp at hb⟩
    | publish n v =>
      have hs' := (registerLTS_tr_publish_iff _ _ n v).mp hs
      exact ⟨hs', fun r hr => by simp [readResult?] at hr, fun b hb => by simp at hb⟩

/-- Along a run, every read returns, and every Ready check observes, the slot computed by
`stepSlot` from the starting slot. -/
private theorem run_facts {σ : Type v} {α : Type u} {H : InterruptHandler σ α} (hH : Rely H)
    {x x' : SystemState σ α} {ms : List (SystemLabel α)} (h : (systemLTS H).MTr x ms x') :
    ∀ k m, ms[k]? = some m →
      (∀ r, readResult? m = some r → r = (ms.take k).foldl stepSlot x.slot) ∧
      (∀ b, m = .driver (.visible (.poll b)) → b = ready ((ms.take k).foldl stepSlot x.slot)) := by
  induction h with
  | refl => intro k m hk; simp at hk
  | @stepL x1 m0 x2 rest x3 htr hrest ih =>
    intro k m hk
    obtain ⟨hs, hr, hp⟩ := step_facts hH htr
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      exact ⟨hr, hp⟩
    | succ k =>
      simp only [List.getElem?_cons_succ] at hk
      simp only [List.take_succ_cons, List.foldl_cons]
      rw [← hs]
      exact ih k m hk

private theorem slotAt_zero {α : Type u} (ms : List (SystemLabel α)) : slotAt ms 0 = none := rfl

private theorem slotAt_succ_some {α : Type u} {ms : List (SystemLabel α)} {k : ℕ}
    {m : SystemLabel α} (h : ms[k]? = some m) : slotAt ms (k + 1) = stepSlot (slotAt ms k) m := by
  simp [slotAt, List.take_add_one, h, List.foldl_append]

private theorem slotAt_succ_none {α : Type u} {ms : List (SystemLabel α)} {k : ℕ}
    (h : ms[k]? = none) : slotAt ms (k + 1) = slotAt ms k := by
  simp [slotAt, List.take_add_one, h]

private theorem slotAt_succ_quiet {α : Type u} {ms : List (SystemLabel α)} {k : ℕ}
    (h : Quiet ms k) : slotAt ms (k + 1) = slotAt ms k := by
  cases hk : ms[k]? with
  | none => exact slotAt_succ_none hk
  | some m =>
    obtain ⟨hp, hr⟩ := h
    rw [hk] at hp hr
    rw [slotAt_succ_some hk]
    exact stepSlot_of_quiet hp hr

/-- After a publication of `(n, v)` and only quiet steps, the slot holds `(n, v)`. -/
private theorem slotAt_of_pub {α : Type u} {ms : List (SystemLabel α)} {i n : ℕ} {v : α}
    (hi : (ms[i]?).bind publication? = some (n, v)) :
    ∀ K, i < K → (∀ k, i < k → k < K → Quiet ms k) → slotAt ms K = some (n, v) := by
  intro K
  induction K with
  | zero => intro h; omega
  | succ K ih =>
    intro hiK hq
    rcases Nat.lt_succ_iff_lt_or_eq.mp hiK with hlt | heq
    · rw [slotAt_succ_quiet (hq K hlt (by omega))]
      exact ih hlt fun k h1 h2 => hq k h1 (by omega)
    · subst heq
      cases hm : ms[i]? with
      | none => rw [hm] at hi; cases hi
      | some m =>
        rw [hm] at hi
        rw [slotAt_succ_some hm]
        exact stepSlot_of_pub hi

/-- A nonempty slot was filled by the last publication, after which every step was quiet. -/
private theorem last_pub_of_slotAt {α : Type u} {ms : List (SystemLabel α)} :
    ∀ K n v, slotAt ms K = some (n, v) →
      ∃ i, i < K ∧ (ms[i]?).bind publication? = some (n, v) ∧
        ∀ k, i < k → k < K → Quiet ms k := by
  intro K
  induction K with
  | zero => intro n v h; rw [slotAt_zero] at h; cases h
  | succ K ih =>
    intro n v h
    have quiet_K : Quiet ms K → slotAt ms K = some (n, v) →
        ∃ i, i < K + 1 ∧ (ms[i]?).bind publication? = some (n, v) ∧
          ∀ k, i < k → k < K + 1 → Quiet ms k := by
      intro hq hK
      obtain ⟨i, hiK, hpi, hqi⟩ := ih n v hK
      refine ⟨i, by omega, hpi, fun k h1 h2 => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h3 | h3
      · exact hqi k h1 h3
      · subst h3; exact hq
    cases hm : ms[K]? with
    | none =>
      rw [slotAt_succ_none hm] at h
      exact quiet_K ⟨by rw [hm]; rfl, by rw [hm]; rfl⟩ h
    | some m =>
      rw [slotAt_succ_some hm] at h
      cases hp : publication? m with
      | some p =>
        rw [stepSlot_of_pub hp] at h
        refine ⟨K, by omega, by rw [hm, Option.bind_some, hp, h], fun k h1 h2 => by omega⟩
      | none =>
        cases hr : readResult? m with
        | some r =>
          rw [stepSlot_of_read hp hr] at h
          cases h
        | none =>
          rw [stepSlot_of_quiet hp hr] at h
          exact quiet_K ⟨by rw [hm, Option.bind_some, hp], by rw [hm, Option.bind_some, hr]⟩ h

/-- The cycle count after `i + d` steps splits at step `i`. -/
private theorem cycleAt_add {α : Type u} (tr : CostedTrace α) (i d : ℕ) :
    cycleAt tr (i + d) = cycleAt tr i + (((tr.map TimeM.time).drop (i + 1)).take d).sum := by
  unfold cycleAt
  rw [List.map_take, List.map_take, show i + d + 1 = (i + 1) + d by omega, List.take_add,
    List.sum_append]

private theorem cycleAt_mono {α : Type u} (tr : CostedTrace α) {i j : ℕ} (h : i ≤ j) :
    cycleAt tr i ≤ cycleAt tr j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [cycleAt_add]
  omega

/-- Interrupt cycles are additive over adjacent windows. -/
private theorem interruptCycles_add {α : Type u} (tr : CostedTrace α) {i p r : ℕ} (hip : i ≤ p)
    (hpr : p ≤ r) :
    interruptCycles tr i p + interruptCycles tr p r = interruptCycles tr i r := by
  unfold interruptCycles
  have h1 : r - i = (p - i) + (r - p) := by omega
  have h2 : (tr.drop (i + 1)).drop (p - i) = tr.drop (p + 1) := by
    rw [List.drop_drop]; congr 1; omega
  rw [h1, List.take_add, h2, List.filter_append, List.map_append, List.sum_append]

/-- The gap and budget premises: any later publication completes more than the budget after
an earlier one. -/
private theorem far_of_gap {α : Type u} {tr : CostedTrace α} {fclk Tmin : ℝ} (hfclk : 0 < fclk)
    {B : ℕ} (hgap : PublicationGap fclk Tmin tr) (hbudget : (B : ℝ) / fclk < Tmin)
    {i j : ℕ} (hij : i < j) (hi : (publicationAt tr i).isSome)
    (hj : (publicationAt tr j).isSome) :
    cycleAt tr i + B < cycleAt tr j := by
  have h := hgap i j hij hi hj
  unfold timeAt at h
  rw [← sub_div] at h
  have h' : (B : ℝ) / fclk < ((cycleAt tr j : ℝ) - cycleAt tr i) / fclk := lt_of_lt_of_le hbudget h
  rw [div_lt_div_iff_of_pos_right hfclk] at h'
  have h'' : ((cycleAt tr i + B : ℕ) : ℝ) < cycleAt tr j := by push_cast; linarith
  exact_mod_cast h''

/-- No publication completes within the budget after an earlier one. -/
private theorem no_pub_within {α : Type u} {tr : CostedTrace α} {i B : ℕ}
    (hfar : ∀ j, i < j → (publicationAt tr j).isSome → cycleAt tr i + B < cycleAt tr j)
    {k : ℕ} (hk : cycleAt tr k ≤ cycleAt tr i + B) :
    ∀ j, i < j → j ≤ k → publicationAt tr j = none := by
  intro j hij hjk
  by_contra hne
  have h1 := hfar j hij (Option.isSome_iff_ne_none.mpr hne)
  have h2 := cycleAt_mono tr hjk
  omega

private theorem lt_length_of_bind_isSome {β γ : Type u} {l : List β} {f : β → Option γ} {i : ℕ}
    (h : (l[i]?.bind f).isSome) : i < l.length := by
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at h
  simp at h

private theorem exists_of_bind_eq_some {β γ : Type u} {l : List β} {f : β → Option γ} {i : ℕ}
    {c : γ} (h : l[i]?.bind f = some c) : ∃ m, l[i]? = some m ∧ f m = some c := by
  cases hm : l[i]? with
  | none => rw [hm] at h; cases h
  | some m => rw [hm, Option.bind_some] at h; exact ⟨m, rfl, h⟩

/-- Under the costed premises, some read completes after publication `i` within the budget. -/
private theorem exists_read_within {σ : Type v} {α : Type u}
    (H : InterruptHandler σ α) (hH : Rely H) (q₀ : σ) (tr : CostedTrace α)
    (x : SystemState σ α) (hrun : (systemLTS H).MTr (initialSystem q₀) (labels tr) x)
    (fclk Tmin : ℝ) (hfclk : 0 < fclk) (Cpoll Cread Cirq Cbus : ℕ)
    (hgap : PublicationGap fclk Tmin tr)
    (hresp : ∀ i, (publicationAt tr i).isSome → RespondsWithin Cpoll Cread Cirq Cbus tr i)
    (hbudget : ((Cpoll + Cread + Cirq + Cbus : ℕ) : ℝ) / fclk < Tmin)
    (i n : ℕ) (v : α) (hi : publicationAt tr i = some (n, v)) :
    ∃ m, i < m ∧ (((labels tr)[m]?).bind readResult?).isSome ∧
      cycleAt tr m ≤ cycleAt tr i + (Cpoll + Cread + Cirq + Cbus) := by
  have hiS : (publicationAt tr i).isSome := by rw [hi]; rfl
  obtain ⟨p, hip, ⟨b, hb⟩, bus₁, bus₂, hbus, hcp, hicp, hread⟩ := hresp i hiS
  have hfar : ∀ j, i < j → (publicationAt tr j).isSome →
      cycleAt tr i + (Cpoll + Cread + Cirq + Cbus) < cycleAt tr j :=
    fun j hij hj => far_of_gap hfclk hgap hbudget hij hiS hj
  have hpB : cycleAt tr p ≤ cycleAt tr i + (Cpoll + Cread + Cirq + Cbus) := by omega
  by_cases hex : ∃ m, i < m ∧ m < p ∧ (((labels tr)[m]?).bind readResult?).isSome
  · obtain ⟨m, him, hmp, hm⟩ := hex
    exact ⟨m, him, hm, le_trans (cycleAt_mono tr hmp.le) hpB⟩
  · have hslot : slotAt (labels tr) p = some (n, v) := by
      refine slotAt_of_pub hi p hip fun k hik hkp => ⟨no_pub_within hfar hpB k hik hkp.le, ?_⟩
      cases h : ((labels tr)[k]?).bind readResult? with
      | none => rfl
      | some _ => exact absurd ⟨k, hik, hkp, by rw [h]; rfl⟩ hex
    have hpoll := (run_facts hH hrun p _ hb).2 b rfl
    change b = ready (slotAt (labels tr) p) at hpoll
    rw [hslot] at hpoll
    subst hpoll
    obtain ⟨r, hpr, ⟨res, hres⟩, hcr, hicr⟩ := hread hb
    refine ⟨r, by omega, by rw [hres]; rfl, ?_⟩
    have hadd := interruptCycles_add tr hip.le hpr.le
    omega

/-- The first read after a publication, with no publication up to it, returns that sample. -/
private theorem first_read {σ : Type v} {α : Type u}
    (H : InterruptHandler σ α) (hH : Rely H) (q₀ : σ) (tr : CostedTrace α)
    (x : SystemState σ α) (hrun : (systemLTS H).MTr (initialSystem q₀) (labels tr) x)
    (i n : ℕ) (v : α) (hi : publicationAt tr i = some (n, v)) (m : ℕ) (him : i < m)
    (hm : (((labels tr)[m]?).bind readResult?).isSome)
    (hnopub : ∀ j, i < j → j ≤ m → publicationAt tr j = none) :
    ∃ k, i < k ∧ k ≤ m ∧ ((labels tr)[k]?).bind readResult? = some (some (n, v)) := by
  classical
  have hP : ∃ k, i < k ∧ (((labels tr)[k]?).bind readResult?).isSome := ⟨m, him, hm⟩
  have hk := Nat.find_spec hP
  have hkm : Nat.find hP ≤ m := Nat.find_min' hP ⟨him, hm⟩
  refine ⟨Nat.find hP, hk.1, hkm, ?_⟩
  have hslot : slotAt (labels tr) (Nat.find hP) = some (n, v) := by
    refine slotAt_of_pub hi _ hk.1 fun k' h1 h2 => ⟨hnopub k' h1 (by omega), ?_⟩
    by_contra hne
    exact Nat.find_min hP h2 ⟨h1, Option.isSome_iff_ne_none.mpr hne⟩
  obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp hk.2
  obtain ⟨m', hm', hr'⟩ := exists_of_bind_eq_some hres
  have h := (run_facts hH hrun _ _ hm').1 res hr'
  change res = slotAt (labels tr) (Nat.find hP) at h
  rw [hres, h, hslot]

/-- A read result of a step that is not another reader's read is a driver read. -/
private theorem eq_driver_read_of_readResult {α : Type u} {m : SystemLabel α}
    {res : Option (ℕ × α)} (h : readResult? m = some res)
    (hne : ∀ r, m ≠ .driver (.visible (.env (.read r)))) :
    m = .driver (.visible (.read res)) := by
  unfold readResult? at h
  split at h
  · cases h; rfl
  · exact absurd rfl (hne _)
  · cases h

private theorem publicationIds_append {α : Type u} (l₁ l₂ : List (SystemLabel α)) :
    publicationIds (l₁ ++ l₂) = publicationIds l₁ ++ publicationIds l₂ := by
  simp [publicationIds, List.filterMap_append]

private theorem driverReadIds_append {α : Type u} (l₁ l₂ : List (SystemLabel α)) :
    driverReadIds (l₁ ++ l₂) = driverReadIds l₁ ++ driverReadIds l₂ := by
  unfold driverReadIds
  exact List.filterMap_append

private theorem publicationIds_single {α : Type u} (m : SystemLabel α) :
    publicationIds [m] = ((publication? m).map Prod.fst).toList := by
  cases h : publication? m <;> simp [publicationIds, h]

private theorem driverReadIds_single {α : Type u} (m : SystemLabel α)
    (hne : ∀ r, m ≠ .driver (.visible (.env (.read r)))) :
    driverReadIds [m] = (((readResult? m).bind id).map Prod.fst).toList := by
  cases m with
  | driver l =>
    cases l with
    | visible μ =>
      cases μ with
      | env μ =>
        cases μ with
        | publish n v => rfl
        | read r => exact absurd rfl (hne r)
      | read r => rcases r with _ | ⟨n, v⟩ <;> rfl
      | poll b => rfl
      | deliver n v => rfl
      | retry => rfl
    | internal => rfl
  | interrupt a => cases a <;> rfl

/-- A cycle bound gives the corresponding physical-time bound. -/
private theorem timeAt_sub_le {α : Type u} {tr : CostedTrace α} {fclk : ℝ} (hfclk : 0 < fclk)
    {i r B : ℕ} (h : cycleAt tr r ≤ cycleAt tr i + B) :
    timeAt fclk tr r - timeAt fclk tr i ≤ (B : ℝ) / fclk := by
  unfold timeAt
  rw [← sub_div]
  apply (div_le_div_iff_of_pos_right hfclk).mpr
  have h' : ((cycleAt tr r : ℕ) : ℝ) ≤ ((cycleAt tr i + B : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  linarith

/-! ## D. The polling deadline -/

/-- **Every publication is read before the next one.** On a costed polling trace of a system
whose interrupt satisfies the rely condition, if every publication meets the costed response
premise and the response budget is shorter than the publication gap, then every publication of
`(n, v)` is read (by the driver or another reader) as `some (n, v)` within the cycle budget and
before any later publication. -/
lemma exists_read_before_next_publication {σ : Type v} {α : Type u}
    (H : InterruptHandler σ α) (hH : Rely H) (q₀ : σ) (tr : CostedTrace α)
    (x : SystemState σ α) (hrun : (systemLTS H).MTr (initialSystem q₀) (labels tr) x)
    (fclk Tmin : ℝ) (hfclk : 0 < fclk) (Cpoll Cread Cirq Cbus : ℕ)
    (hgap : PublicationGap fclk Tmin tr)
    (hresp : ∀ i, (publicationAt tr i).isSome → RespondsWithin Cpoll Cread Cirq Cbus tr i)
    (hbudget : ((Cpoll + Cread + Cirq + Cbus : ℕ) : ℝ) / fclk < Tmin)
    (i n : ℕ) (v : α) (hi : publicationAt tr i = some (n, v)) :
    ∃ r, i < r ∧ ((labels tr)[r]?).bind readResult? = some (some (n, v)) ∧
      cycleAt tr r ≤ cycleAt tr i + (Cpoll + Cread + Cirq + Cbus) ∧
      ∀ j, i < j → (publicationAt tr j).isSome → r < j := by
  have hiS : (publicationAt tr i).isSome := by rw [hi]; rfl
  have hfar : ∀ j, i < j → (publicationAt tr j).isSome →
      cycleAt tr i + (Cpoll + Cread + Cirq + Cbus) < cycleAt tr j :=
    fun j hij hj => far_of_gap hfclk hgap hbudget hij hiS hj
  obtain ⟨m, him, hm, hmB⟩ :=
    exists_read_within H hH q₀ tr x hrun fclk Tmin hfclk Cpoll Cread Cirq Cbus hgap hresp
      hbudget i n v hi
  obtain ⟨k, hik, hkm, hk⟩ :=
    first_read H hH q₀ tr x hrun i n v hi m him hm (no_pub_within hfar hmB)
  refine ⟨k, hik, hk, le_trans (cycleAt_mono tr hkm) hmB, fun j hij hj => ?_⟩
  by_contra hle
  have h1 := hfar j hij hj
  have h2 := cycleAt_mono tr (show j ≤ m by omega)
  omega

/-- **Successful reads are fresh.** Under the same premises, every successful read of `(n, v)`
returns the latest earlier publication, with no publication in between, completed at most
`Cpoll + Cread + Cirq + Cbus` cycles after it. -/
lemma exists_fresh_publication_of_read {σ : Type v} {α : Type u}
    (H : InterruptHandler σ α) (hH : Rely H) (q₀ : σ) (tr : CostedTrace α)
    (x : SystemState σ α) (hrun : (systemLTS H).MTr (initialSystem q₀) (labels tr) x)
    (fclk Tmin : ℝ) (hfclk : 0 < fclk) (Cpoll Cread Cirq Cbus : ℕ)
    (hgap : PublicationGap fclk Tmin tr)
    (hresp : ∀ i, (publicationAt tr i).isSome → RespondsWithin Cpoll Cread Cirq Cbus tr i)
    (hbudget : ((Cpoll + Cread + Cirq + Cbus : ℕ) : ℝ) / fclk < Tmin)
    (r n : ℕ) (v : α) (hr : ((labels tr)[r]?).bind readResult? = some (some (n, v))) :
    ∃ i, i < r ∧ publicationAt tr i = some (n, v) ∧
      (∀ k, i < k → k < r → publicationAt tr k = none) ∧
      cycleAt tr r ≤ cycleAt tr i + (Cpoll + Cread + Cirq + Cbus) := by
  obtain ⟨m0, hm0, hr0⟩ := exists_of_bind_eq_some hr
  have hslot := (run_facts hH hrun r m0 hm0).1 _ hr0
  change some (n, v) = slotAt (labels tr) r at hslot
  obtain ⟨i, hir, hpi, hq⟩ := last_pub_of_slotAt r n v hslot.symm
  refine ⟨i, hir, hpi, fun k h1 h2 => (hq k h1 h2).1, ?_⟩
  obtain ⟨m, him, hm, hmB⟩ :=
    exists_read_within H hH q₀ tr x hrun fclk Tmin hfclk Cpoll Cread Cirq Cbus hgap hresp
      hbudget i n v hpi
  have hrm : r ≤ m := by
    by_contra hlt
    have := (hq m him (by omega)).2
    rw [this] at hm
    cases hm
  exact le_trans (cycleAt_mono tr hrm) hmB

/-- **With a sole reader, the driver reads every publication.** Under the same premises, if the
driver is the only reader, every publication of `(n, v)` is returned by a driver read as
`some (n, v)` before any later publication. -/
lemma exists_driver_read_before_next_publication {σ : Type v} {α : Type u}
    (H : InterruptHandler σ α) (hH : Rely H) (q₀ : σ) (tr : CostedTrace α)
    (x : SystemState σ α) (hrun : (systemLTS H).MTr (initialSystem q₀) (labels tr) x)
    (fclk Tmin : ℝ) (hfclk : 0 < fclk) (Cpoll Cread Cirq Cbus : ℕ)
    (hgap : PublicationGap fclk Tmin tr)
    (hresp : ∀ i, (publicationAt tr i).isSome → RespondsWithin Cpoll Cread Cirq Cbus tr i)
    (hbudget : ((Cpoll + Cread + Cirq + Cbus : ℕ) : ℝ) / fclk < Tmin)
    (hsole : NoOtherReader (labels tr))
    (i n : ℕ) (v : α) (hi : publicationAt tr i = some (n, v)) :
    ∃ r, i < r ∧ (labels tr)[r]? = some (.driver (.visible (.read (some (n, v))))) ∧
      ∀ j, i < j → (publicationAt tr j).isSome → r < j := by
  obtain ⟨r, hir, hr, -, hlater⟩ :=
    exists_read_before_next_publication H hH q₀ tr x hrun fclk Tmin hfclk Cpoll Cread Cirq Cbus
      hgap hresp hbudget i n v hi
  obtain ⟨m0, hm0, hr0⟩ := exists_of_bind_eq_some hr
  refine ⟨r, hir, ?_, hlater⟩
  rw [hm0, eq_driver_read_of_readResult hr0 fun r' he => hsole r r' (by rw [hm0, he])]

/-- **Lossless, in-order returned IDs.** Under the same premises, if the driver is the only
reader, the IDs returned by the driver's successful reads are exactly the publication IDs, in
order. -/
lemma driverReadIds_eq_publicationIds {σ : Type v} {α : Type u}
    (H : InterruptHandler σ α) (hH : Rely H) (q₀ : σ) (tr : CostedTrace α)
    (x : SystemState σ α) (hrun : (systemLTS H).MTr (initialSystem q₀) (labels tr) x)
    (fclk Tmin : ℝ) (hfclk : 0 < fclk) (Cpoll Cread Cirq Cbus : ℕ)
    (hgap : PublicationGap fclk Tmin tr)
    (hresp : ∀ i, (publicationAt tr i).isSome → RespondsWithin Cpoll Cread Cirq Cbus tr i)
    (hbudget : ((Cpoll + Cread + Cirq + Cbus : ℕ) : ℝ) / fclk < Tmin)
    (hsole : NoOtherReader (labels tr)) :
    driverReadIds (labels tr) = publicationIds (labels tr) := by
  set ms := labels tr with hms
  have hdr : ∀ k m, ms[k]? = some m → ∀ r, m ≠ SystemLabel.driver (.visible (.env (.read r))) :=
    fun k m hk r he => hsole k r (by rw [hk, he])
  -- a filled slot is read before any later publication, hence before the end of the trace
  have hread_of_slot : ∀ K n v, slotAt ms K = some (n, v) →
      ∃ i r, i < K ∧ i < r ∧ r < ms.length ∧ (∀ j, i < j → (publicationAt tr j).isSome → r < j) ∧
        (((ms[r]?).bind readResult?).isSome) ∧ ∀ k, i < k → k < K → Quiet ms k := by
    intro K n v hK
    obtain ⟨i, hiK, hpi, hq⟩ := last_pub_of_slotAt K n v hK
    obtain ⟨r, hir, hr, -, hlater⟩ :=
      exists_read_before_next_publication H hH q₀ tr x hrun fclk Tmin hfclk Cpoll Cread Cirq
        Cbus hgap hresp hbudget i n v hpi
    have hrS : ((ms[r]?).bind readResult?).isSome := by rw [hr]; rfl
    exact ⟨i, r, hiK, hir, lt_length_of_bind_isSome hrS, hlater, hrS, hq⟩
  have key : ∀ K, (slotAt ms K = none →
      driverReadIds (ms.take K) = publicationIds (ms.take K)) ∧
      (∀ n v, slotAt ms K = some (n, v) →
        publicationIds (ms.take K) = driverReadIds (ms.take K) ++ [n]) := by
    intro K
    induction K with
    | zero => exact ⟨fun _ => rfl, fun n v h => by rw [slotAt_zero] at h; cases h⟩
    | succ K ih =>
      rw [List.take_add_one, driverReadIds_append, publicationIds_append]
      cases hm : ms[K]? with
      | none =>
        rw [slotAt_succ_none hm]
        simpa [driverReadIds, publicationIds] using ih
      | some m =>
        rw [slotAt_succ_some hm, Option.toList_some, driverReadIds_single m (hdr K m hm),
          publicationIds_single m]
        obtain ⟨hr0, hp0⟩ := run_facts hH hrun K m hm
        change ∀ r, readResult? m = some r → r = slotAt ms K at hr0
        cases hp : publication? m with
        | some p =>
          obtain ⟨n', v'⟩ := p
          rw [stepSlot_of_pub hp, readResult_eq_none_of_pub hp]
          have hnone : slotAt ms K = none := by
            cases hs : slotAt ms K with
            | none => rfl
            | some q =>
              obtain ⟨n, v⟩ := q
              obtain ⟨i, r, hiK, hir, -, hlater, hrS, hq⟩ := hread_of_slot K n v hs
              have hrK := hlater K hiK
                (by change ((ms[K]?).bind publication?).isSome; rw [hm, Option.bind_some, hp]; rfl)
              have := (hq r hir hrK).2
              rw [this] at hrS
              cases hrS
          refine ⟨fun h => (by cases h), fun n v h => ?_⟩
          cases h
          simp [(ih.1 hnone)]
        | none =>
          cases hr : readResult? m with
          | some res =>
            rw [stepSlot_of_read hp hr]
            have hres := hr0 res hr
            refine ⟨fun _ => ?_, fun n v h => (by cases h)⟩
            cases res with
            | none => simpa using ih.1 hres.symm
            | some q =>
              obtain ⟨n, v⟩ := q
              simpa using (ih.2 n v hres.symm).symm
          | none =>
            rw [stepSlot_of_quiet hp hr]
            simpa using ih
  have hend : slotAt ms ms.length = none := by
    cases hs : slotAt ms ms.length with
    | none => rfl
    | some q =>
      obtain ⟨n, v⟩ := q
      obtain ⟨i, r, -, hir, hrl, -, hrS, hq⟩ := hread_of_slot _ n v hs
      have := (hq r hir hrl).2
      rw [this] at hrS
      cases hrS
  have := (key ms.length).1 hend
  rwa [List.take_length] at this

/-- **Costed polling sample deadline (headline).** Let a producer interrupt satisfy the rely
condition, let a costed polling trace run from an initial state, let `0 < fclk` and `0 < Tmin`,
let any two publications be at least `Tmin` seconds apart, let every publication be followed by a
driver Ready check within `Cpoll` cycles and, when Ready is observed, by a driver read within
`Cread` further cycles, with interrupt cycles bounded by `Cirq` and bus allowances by `Cbus` over
the response window, and let `(Cpoll + Cread + Cirq + Cbus) / fclk < Tmin`. Then:
(1) every publication of `(n, v)` is read as `some (n, v)` before any later publication, at most
`(Cpoll + Cread + Cirq + Cbus) / fclk` seconds, hence less than `Tmin`, after it;
(2) every successful read returns the latest earlier publication, with no publication in between,
at most `(Cpoll + Cread + Cirq + Cbus) / fclk` seconds old;
(3) if the driver is the only reader, every publication is returned by a driver read before the
next one, the driver's returned IDs are the publication IDs in order, composing them with the
supplied acquisition timestamps `acq` gives the timestamped publication stream, and the returned
timestamps are strictly increasing when the publication IDs are and `acq` is strictly
monotone. -/
lemma pollingSampleDeadline_correct {σ : Type v} {α : Type u}
    (H : InterruptHandler σ α) (hH : Rely H) (q₀ : σ) (tr : CostedTrace α)
    (x : SystemState σ α) (hrun : (systemLTS H).MTr (initialSystem q₀) (labels tr) x)
    (fclk Tmin : ℝ) (hfclk : 0 < fclk) (hTmin : 0 < Tmin) (Cpoll Cread Cirq Cbus : ℕ)
    (hgap : PublicationGap fclk Tmin tr)
    (hresp : ∀ i, (publicationAt tr i).isSome → RespondsWithin Cpoll Cread Cirq Cbus tr i)
    (hbudget : ((Cpoll + Cread + Cirq + Cbus : ℕ) : ℝ) / fclk < Tmin)
    (acq : ℕ → ℝ) :
    (∀ (i n : ℕ) (v : α), publicationAt tr i = some (n, v) →
      ∃ r, i < r ∧ ((labels tr)[r]?).bind readResult? = some (some (n, v)) ∧
        timeAt fclk tr r - timeAt fclk tr i ≤ ((Cpoll + Cread + Cirq + Cbus : ℕ) : ℝ) / fclk ∧
        timeAt fclk tr r - timeAt fclk tr i < Tmin ∧
        ∀ j, i < j → (publicationAt tr j).isSome → r < j) ∧
    (∀ (r n : ℕ) (v : α), ((labels tr)[r]?).bind readResult? = some (some (n, v)) →
      ∃ i, i < r ∧ publicationAt tr i = some (n, v) ∧
        (∀ k, i < k → k < r → publicationAt tr k = none) ∧
        timeAt fclk tr r - timeAt fclk tr i ≤ ((Cpoll + Cread + Cirq + Cbus : ℕ) : ℝ) / fclk) ∧
    (NoOtherReader (labels tr) →
      (∀ (i n : ℕ) (v : α), publicationAt tr i = some (n, v) →
        ∃ r, i < r ∧ (labels tr)[r]? = some (.driver (.visible (.read (some (n, v))))) ∧
          ∀ j, i < j → (publicationAt tr j).isSome → r < j) ∧
      driverReadIds (labels tr) = publicationIds (labels tr) ∧
      stampSamples acq (driverReadIds (labels tr)) =
        stampSamples acq (publicationIds (labels tr)) ∧
      ((publicationIds (labels tr)).Pairwise (· < ·) → StrictMono acq →
        ((driverReadIds (labels tr)).map acq).Pairwise (· < ·))) := by
  have _hTmin : 0 < Tmin := hTmin
  have hdriver := exists_driver_read_before_next_publication H hH q₀ tr x hrun fclk Tmin hfclk
    Cpoll Cread Cirq Cbus hgap hresp hbudget
  have hids := driverReadIds_eq_publicationIds H hH q₀ tr x hrun fclk Tmin hfclk
    Cpoll Cread Cirq Cbus hgap hresp hbudget
  refine ⟨fun i n v hi => ?_, fun r n v hr => ?_, fun hsole => ?_⟩
  · obtain ⟨r, hir, hr, hcyc, hlater⟩ :=
      exists_read_before_next_publication H hH q₀ tr x hrun fclk Tmin hfclk Cpoll Cread Cirq
        Cbus hgap hresp hbudget i n v hi
    have ht := timeAt_sub_le hfclk hcyc
    exact ⟨r, hir, hr, ht, lt_of_le_of_lt ht hbudget, hlater⟩
  · obtain ⟨i, hir, hi, hq, hcyc⟩ :=
      exists_fresh_publication_of_read H hH q₀ tr x hrun fclk Tmin hfclk Cpoll Cread Cirq Cbus
        hgap hresp hbudget r n v hr
    exact ⟨i, hir, hi, hq, timeAt_sub_le hfclk hcyc⟩
  · have hids' := hids hsole
    refine ⟨hdriver hsole, hids', by rw [hids'], fun hpw hacq => ?_⟩
    rw [hids', List.pairwise_map]
    exact hpw.imp fun h => hacq h

/-! ## E. Validation -/

/-- A stalling producer interrupt: an interrupt-local step that changes nothing. Its cycle charge
models the time the interrupt steals from the driver. -/
inductive StallStep {α : Type u} :
    SystemState Unit α → InterruptAction α → SystemState Unit α → Prop where
  | stall (x : SystemState Unit α) : StallStep x .localStep x

/-- The stalling interrupt as a handler. -/
def stallHandler {α : Type u} : InterruptHandler Unit α where
  Tr := StallStep

/-- The stalling interrupt satisfies the rely condition. -/
lemma rely_stallHandler {α : Type u} : Rely (stallHandler (α := α)) := by
  intro x a x' h
  cases h
  exact ⟨rfl, rfl⟩

/-- Worst phase: the environment publishes `(0, a)` in the same cycle as a Ready check that saw
an empty slot, so the driver retries and polls again; a one-cycle interrupt stall falls between
that poll and the read. Later `(1, b)` is published and read. Charges (cycles) per step:
`1 0 1 2 1 1 1 1 1 1 0 1 1 1`. -/
def worstPhaseTrace {α : Type u} (a b : α) : CostedTrace α :=
  [⟨.driver (.visible (.poll false)), 1⟩, ⟨.driver (.visible (.env (.publish 0 a))), 0⟩,
    ⟨.driver (.visible .retry), 1⟩, ⟨.driver (.visible (.poll true)), 2⟩,
    ⟨.interrupt .localStep, 1⟩, ⟨.driver .internal, 1⟩,
    ⟨.driver (.visible (.read (some (0, a)))), 1⟩, ⟨.driver .internal, 1⟩,
    ⟨.driver (.visible (.deliver 0 a)), 1⟩, ⟨.driver .internal, 1⟩,
    ⟨.driver (.visible (.env (.publish 1 b))), 0⟩, ⟨.driver (.visible (.poll true)), 1⟩,
    ⟨.driver .internal, 1⟩, ⟨.driver (.visible (.read (some (1, b)))), 1⟩]

/-! ### Worst-phase fixture facts (private) -/

private theorem fixture_lt_of_getElem?_eq_some {β : Type u} {l : List β} {i : ℕ} {b : β}
    (h : l[i]? = some b) : i < l.length :=
  (List.getElem?_eq_some_iff.mp h).1

private theorem fixture_lt_of_bind_isSome {β γ : Type u} {l : List β} {f : β → Option γ} {i : ℕ}
    (h : (l[i]?.bind f).isSome) : i < l.length := by
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at h
  simp at h

private theorem fixture_lt_of_bind_eq_some {β γ : Type u} {l : List β} {f : β → Option γ} {i : ℕ}
    {c : γ} (h : l[i]?.bind f = some c) : i < l.length :=
  fixture_lt_of_bind_isSome (by rw [h]; rfl)

private theorem fixture_worstPhase_run {α : Type u} (a b : α) :
    (systemLTS stallHandler).MTr (initialSystem ()) (labels (worstPhaseTrace a b))
      ⟨(), ⟨.branchData, true, some (1, b), some (0, a)⟩, none⟩ := by
  exact
    .stepL (SystemStep.driver _ (PollStep.loadReady _ _ rfl)) <|
    .stepL (SystemStep.driver _ (PollStep.env _ (RegisterStep.publish _ 0 a))) <|
    .stepL (SystemStep.driver _ (PollStep.readyNotTaken _ _ rfl rfl)) <|
    .stepL (SystemStep.driver _ (PollStep.loadReady _ _ rfl)) <|
    .stepL (SystemStep.interrupt (StallStep.stall _)) <|
    .stepL (SystemStep.driver _ (PollStep.readyTaken _ _ rfl rfl)) <|
    .stepL (SystemStep.driver _ (PollStep.loadData _ rfl (RegisterStep.read _))) <|
    .stepL (SystemStep.driver _ (PollStep.dataPresent _ _ 0 a rfl rfl)) <|
    .stepL (SystemStep.driver _ (PollStep.emit _ _ 0 a rfl rfl)) <|
    .stepL (SystemStep.driver _ (PollStep.record _ _ rfl)) <|
    .stepL (SystemStep.driver _ (PollStep.env _ (RegisterStep.publish _ 1 b))) <|
    .stepL (SystemStep.driver _ (PollStep.loadReady _ _ rfl)) <|
    .stepL (SystemStep.driver _ (PollStep.readyTaken _ _ rfl rfl)) <|
    .stepL (SystemStep.driver _ (PollStep.loadData _ rfl (RegisterStep.read _))) .refl

private theorem fixture_worstPhase_len {α : Type u} (a b : α) :
    (labels (worstPhaseTrace a b)).length = 14 := rfl

/-- The publications of the worst-phase trace are exactly steps `1` and `10`. -/
private theorem fixture_worstPhase_pub {α : Type u} (a b : α) (i : ℕ) (n : ℕ) (v : α)
    (h : publicationAt (worstPhaseTrace a b) i = some (n, v)) :
    (i = 1 ∧ n = 0 ∧ v = a) ∨ (i = 10 ∧ n = 1 ∧ v = b) := by
  have hi := fixture_lt_of_bind_eq_some h
  rw [fixture_worstPhase_len] at hi
  interval_cases i <;>
    simp_all [publicationAt, labels, worstPhaseTrace, publication?]

private theorem fixture_worstPhase_pub' {α : Type u} (a b : α) (i : ℕ)
    (h : (publicationAt (worstPhaseTrace a b) i).isSome) : i = 1 ∨ i = 10 := by
  obtain ⟨⟨n, v⟩, hp⟩ := Option.isSome_iff_exists.mp h
  rcases fixture_worstPhase_pub a b i n v hp with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem fixture_worstPhase_gap {α : Type u} (a b : α) :
    PublicationGap 1 8 (worstPhaseTrace a b) := by
  intro i j hij hi hj
  rcases fixture_worstPhase_pub' a b i hi with rfl | rfl <;>
    rcases fixture_worstPhase_pub' a b j hj with rfl | rfl
  · omega
  · norm_num [timeAt, cycleAt, worstPhaseTrace]
  · omega
  · omega

private theorem fixture_worstPhase_resp {α : Type u} (a b : α) (i : ℕ)
    (h : (publicationAt (worstPhaseTrace a b) i).isSome) :
    RespondsWithin 3 2 1 1 (worstPhaseTrace a b) i := by
  rcases fixture_worstPhase_pub' a b i h with rfl | rfl
  · refine ⟨3, by omega, ⟨true, rfl⟩, 0, 0, by omega, ?_, ?_, ?_⟩
    · simp [cycleAt, interruptCycles, worstPhaseTrace, isInterruptStep]
    · simp [interruptCycles, worstPhaseTrace, isInterruptStep]
    · intro _
      refine ⟨6, by omega, ⟨some (0, a), rfl⟩, ?_, ?_⟩
      · simp [cycleAt, interruptCycles, worstPhaseTrace, isInterruptStep]
      · simp [interruptCycles, worstPhaseTrace, isInterruptStep]
  · refine ⟨11, by omega, ⟨true, rfl⟩, 0, 0, by omega, ?_, ?_, ?_⟩
    · simp [cycleAt, interruptCycles, worstPhaseTrace, isInterruptStep]
    · simp [interruptCycles, worstPhaseTrace, isInterruptStep]
    · intro _
      refine ⟨13, by omega, ⟨some (1, b), rfl⟩, ?_, ?_⟩
      · simp [cycleAt, interruptCycles, worstPhaseTrace, isInterruptStep]
      · simp [interruptCycles, worstPhaseTrace, isInterruptStep]

private theorem fixture_worstPhase_sole {α : Type u} (a b : α) :
    NoOtherReader (labels (worstPhaseTrace a b)) := by
  intro k r h
  have hk := fixture_lt_of_getElem?_eq_some h
  rw [fixture_worstPhase_len] at hk
  interval_cases k <;> simp [labels, worstPhaseTrace] at h

/-- **Worst phase.** The worst-phase trace is a run of the stalling system; publication `0`
completes in the same cycle as the empty Ready check before it; at `fclk = 1`, `Tmin = 8`,
`Cpoll = 3`, `Cread = 2`, `Cirq = 1`, `Cbus = 1` it meets every premise, including the strict
budget `7 / 1 < 8`; the driver is the only reader; and it returns both publications. -/
lemma worstPhase_valid {α : Type u} (a b : α) :
    (systemLTS stallHandler).MTr (initialSystem ()) (labels (worstPhaseTrace a b))
        ⟨(), ⟨.branchData, true, some (1, b), some (0, a)⟩, none⟩ ∧
      (labels (worstPhaseTrace a b))[0]? = some (.driver (.visible (.poll false))) ∧
      publicationAt (worstPhaseTrace a b) 1 = some (0, a) ∧
      cycleAt (worstPhaseTrace a b) 1 = cycleAt (worstPhaseTrace a b) 0 ∧
      PublicationGap 1 8 (worstPhaseTrace a b) ∧
      (∀ i, (publicationAt (worstPhaseTrace a b) i).isSome →
        RespondsWithin 3 2 1 1 (worstPhaseTrace a b) i) ∧
      ((3 + 2 + 1 + 1 : ℕ) : ℝ) / 1 < 8 ∧
      NoOtherReader (labels (worstPhaseTrace a b)) ∧
      driverReadIds (labels (worstPhaseTrace a b)) = [0, 1] ∧
      publicationIds (labels (worstPhaseTrace a b)) = [0, 1] := by
  refine ⟨fixture_worstPhase_run a b, rfl, rfl, rfl, fixture_worstPhase_gap a b,
    fixture_worstPhase_resp a b, by norm_num, fixture_worstPhase_sole a b, rfl, rfl⟩

/-- Budget equal to the gap: `(0, a)` is published right after an empty Ready check, the driver
polls Ready, a one-cycle stall intervenes, and `(1, b)` is published exactly `7` cycles after
`(0, a)` and just before the read completes in the same cycle, so the read returns `(1, b)`.
Charges per step: `1 0 1 2 1 1 2 0 1 1 1 1 1`. -/
def boundaryTrace {α : Type u} (a b : α) : CostedTrace α :=
  [⟨.driver (.visible (.poll false)), 1⟩, ⟨.driver (.visible (.env (.publish 0 a))), 0⟩,
    ⟨.driver (.visible .retry), 1⟩, ⟨.driver (.visible (.poll true)), 2⟩,
    ⟨.interrupt .localStep, 1⟩, ⟨.driver .internal, 1⟩,
    ⟨.driver (.visible (.env (.publish 1 b))), 2⟩,
    ⟨.driver (.visible (.read (some (1, b)))), 0⟩, ⟨.driver .internal, 1⟩,
    ⟨.driver (.visible (.deliver 1 b)), 1⟩, ⟨.driver .internal, 1⟩,
    ⟨.driver (.visible (.poll false)), 1⟩, ⟨.driver (.visible .retry), 1⟩]

/-! ### Boundary fixture facts (private) -/

private theorem fixture_boundary_run {α : Type u} (a b : α) :
    (systemLTS stallHandler).MTr (initialSystem ()) (labels (boundaryTrace a b))
      ⟨(), ⟨.poll, false, some (1, b), some (1, b)⟩, none⟩ := by
  exact
    .stepL (SystemStep.driver _ (PollStep.loadReady _ _ rfl)) <|
    .stepL (SystemStep.driver _ (PollStep.env _ (RegisterStep.publish _ 0 a))) <|
    .stepL (SystemStep.driver _ (PollStep.readyNotTaken _ _ rfl rfl)) <|
    .stepL (SystemStep.driver _ (PollStep.loadReady _ _ rfl)) <|
    .stepL (SystemStep.interrupt (StallStep.stall _)) <|
    .stepL (SystemStep.driver _ (PollStep.readyTaken _ _ rfl rfl)) <|
    .stepL (SystemStep.driver _ (PollStep.env _ (RegisterStep.publish _ 1 b))) <|
    .stepL (SystemStep.driver _ (PollStep.loadData _ rfl (RegisterStep.read _))) <|
    .stepL (SystemStep.driver _ (PollStep.dataPresent _ _ 1 b rfl rfl)) <|
    .stepL (SystemStep.driver _ (PollStep.emit _ _ 1 b rfl rfl)) <|
    .stepL (SystemStep.driver _ (PollStep.record _ _ rfl)) <|
    .stepL (SystemStep.driver _ (PollStep.loadReady _ _ rfl)) <|
    .stepL (SystemStep.driver _ (PollStep.readyNotTaken _ _ rfl rfl)) .refl

private theorem fixture_boundary_len {α : Type u} (a b : α) :
    (labels (boundaryTrace a b)).length = 13 := rfl

private theorem fixture_boundary_pub' {α : Type u} (a b : α) (i : ℕ)
    (h : (publicationAt (boundaryTrace a b) i).isSome) : i = 1 ∨ i = 6 := by
  have hi := fixture_lt_of_bind_isSome h
  rw [fixture_boundary_len] at hi
  interval_cases i <;> simp_all [publicationAt, labels, boundaryTrace, publication?]

private theorem fixture_boundary_gap {α : Type u} (a b : α) :
    PublicationGap 1 7 (boundaryTrace a b) := by
  intro i j hij hi hj
  rcases fixture_boundary_pub' a b i hi with rfl | rfl <;>
    rcases fixture_boundary_pub' a b j hj with rfl | rfl
  · omega
  · norm_num [timeAt, cycleAt, boundaryTrace]
  · omega
  · omega

private theorem fixture_boundary_resp {α : Type u} (a b : α) (i : ℕ)
    (h : (publicationAt (boundaryTrace a b) i).isSome) :
    RespondsWithin 3 2 1 1 (boundaryTrace a b) i := by
  rcases fixture_boundary_pub' a b i h with rfl | rfl
  · refine ⟨3, by omega, ⟨true, rfl⟩, 0, 1, by omega, ?_, ?_, ?_⟩
    · simp [cycleAt, interruptCycles, boundaryTrace, isInterruptStep]
    · simp [interruptCycles, boundaryTrace, isInterruptStep]
    · intro _
      refine ⟨7, by omega, ⟨some (1, b), rfl⟩, ?_, ?_⟩
      · simp [cycleAt, interruptCycles, boundaryTrace, isInterruptStep]
      · simp [interruptCycles, boundaryTrace, isInterruptStep]
  · refine ⟨11, by omega, ⟨false, rfl⟩, 1, 0, by omega, ?_, ?_, ?_⟩
    · simp [cycleAt, interruptCycles, boundaryTrace, isInterruptStep]
    · simp [interruptCycles, boundaryTrace, isInterruptStep]
    · intro h11
      simp [labels, boundaryTrace] at h11

private theorem fixture_boundary_sole {α : Type u} (a b : α) :
    NoOtherReader (labels (boundaryTrace a b)) := by
  intro k r h
  have hk := fixture_lt_of_getElem?_eq_some h
  rw [fixture_boundary_len] at hk
  interval_cases k <;> simp [labels, boundaryTrace] at h

/-- **Equality or overload need not prevent overwrite.** The boundary trace is a run of the
stalling system with a sole reader that meets the gap premise for `Tmin = 7` (hence `6`) and the
response premise at every publication for `Cpoll = 3`, `Cread = 2`, `Cirq = 1`, `Cbus = 1`; the
budget `7 / 1` equals `7` and exceeds `6`; and publication `0` is never returned. -/
lemma budget_not_strict_loses {α : Type u} (a b : α) :
    (systemLTS stallHandler).MTr (initialSystem ()) (labels (boundaryTrace a b))
        ⟨(), ⟨.poll, false, some (1, b), some (1, b)⟩, none⟩ ∧
      PublicationGap 1 7 (boundaryTrace a b) ∧
      PublicationGap 1 6 (boundaryTrace a b) ∧
      (∀ i, (publicationAt (boundaryTrace a b) i).isSome →
        RespondsWithin 3 2 1 1 (boundaryTrace a b) i) ∧
      ((3 + 2 + 1 + 1 : ℕ) : ℝ) / 1 = 7 ∧
      (6 : ℝ) < ((3 + 2 + 1 + 1 : ℕ) : ℝ) / 1 ∧
      NoOtherReader (labels (boundaryTrace a b)) ∧
      publicationIds (labels (boundaryTrace a b)) = [0, 1] ∧
      driverReadIds (labels (boundaryTrace a b)) = [1] := by
  refine ⟨fixture_boundary_run a b, fixture_boundary_gap a b, ?_, fixture_boundary_resp a b,
    by norm_num, by norm_num, fixture_boundary_sole a b, rfl, rfl⟩
  intro i j hij hi hj
  have := fixture_boundary_gap a b i j hij hi hj
  linarith

/-- A delayed interrupt: as in the worst phase, but the interrupt stall between the Ready check
and the read takes `3` cycles, so `(1, b)`, published `8` cycles after `(0, a)`, lands before the
read. Charges per step: `1 0 1 2 3 1 1 0 1 1 1 1 1`. -/
def delayedInterruptTrace {α : Type u} (a b : α) : CostedTrace α :=
  [⟨.driver (.visible (.poll false)), 1⟩, ⟨.driver (.visible (.env (.publish 0 a))), 0⟩,
    ⟨.driver (.visible .retry), 1⟩, ⟨.driver (.visible (.poll true)), 2⟩,
    ⟨.interrupt .localStep, 3⟩, ⟨.driver .internal, 1⟩,
    ⟨.driver (.visible (.env (.publish 1 b))), 1⟩,
    ⟨.driver (.visible (.read (some (1, b)))), 0⟩, ⟨.driver .internal, 1⟩,
    ⟨.driver (.visible (.deliver 1 b)), 1⟩, ⟨.driver .internal, 1⟩,
    ⟨.driver (.visible (.poll false)), 1⟩, ⟨.driver (.visible .retry), 1⟩]

/-! ### Delayed-interrupt fixture facts (private) -/

private theorem fixture_delayed_run {α : Type u} (a b : α) :
    (systemLTS stallHandler).MTr (initialSystem ()) (labels (delayedInterruptTrace a b))
      ⟨(), ⟨.poll, false, some (1, b), some (1, b)⟩, none⟩ := by
  exact
    .stepL (SystemStep.driver _ (PollStep.loadReady _ _ rfl)) <|
    .stepL (SystemStep.driver _ (PollStep.env _ (RegisterStep.publish _ 0 a))) <|
    .stepL (SystemStep.driver _ (PollStep.readyNotTaken _ _ rfl rfl)) <|
    .stepL (SystemStep.driver _ (PollStep.loadReady _ _ rfl)) <|
    .stepL (SystemStep.interrupt (StallStep.stall _)) <|
    .stepL (SystemStep.driver _ (PollStep.readyTaken _ _ rfl rfl)) <|
    .stepL (SystemStep.driver _ (PollStep.env _ (RegisterStep.publish _ 1 b))) <|
    .stepL (SystemStep.driver _ (PollStep.loadData _ rfl (RegisterStep.read _))) <|
    .stepL (SystemStep.driver _ (PollStep.dataPresent _ _ 1 b rfl rfl)) <|
    .stepL (SystemStep.driver _ (PollStep.emit _ _ 1 b rfl rfl)) <|
    .stepL (SystemStep.driver _ (PollStep.record _ _ rfl)) <|
    .stepL (SystemStep.driver _ (PollStep.loadReady _ _ rfl)) <|
    .stepL (SystemStep.driver _ (PollStep.readyNotTaken _ _ rfl rfl)) .refl

private theorem fixture_delayed_len {α : Type u} (a b : α) :
    (labels (delayedInterruptTrace a b)).length = 13 := rfl

private theorem fixture_delayed_pub' {α : Type u} (a b : α) (i : ℕ)
    (h : (publicationAt (delayedInterruptTrace a b) i).isSome) : i = 1 ∨ i = 6 := by
  have hi := fixture_lt_of_bind_isSome h
  rw [fixture_delayed_len] at hi
  interval_cases i <;> simp_all [publicationAt, labels, delayedInterruptTrace, publication?]

private theorem fixture_delayed_not_resp {α : Type u} (a b : α) :
    ¬ RespondsWithin 3 2 1 1 (delayedInterruptTrace a b) 1 := by
  rintro ⟨p, hp, ⟨bb, hb⟩, bus₁, bus₂, hbus, hcp, hirq, hread⟩
  have hpl := fixture_lt_of_getElem?_eq_some hb
  rw [fixture_delayed_len] at hpl
  interval_cases p <;> simp [labels, delayedInterruptTrace] at hb
  · -- p = 3: Ready observed; the only later driver read is step 7
    obtain ⟨r, hr, ⟨res, hres⟩, hcr, hirq'⟩ := hread rfl
    have hrl := fixture_lt_of_getElem?_eq_some hres
    rw [fixture_delayed_len] at hrl
    interval_cases r <;> simp [labels, delayedInterruptTrace] at hres
    simp [interruptCycles, delayedInterruptTrace, isInterruptStep] at hirq'
  · -- p = 11: the Ready check is too late
    simp [cycleAt, interruptCycles, delayedInterruptTrace, isInterruptStep] at hcp
    omega

/-- **A delayed interrupt exceeds the premise.** The delayed-interrupt trace is a run of the
stalling system with a sole reader, the gap premise holds for `Tmin = 8` and the strict budget
`7 / 1 < 8` holds; the response premise holds at publication `1` (step `6`) and would hold at
publication `0` (step `1`) with `Cirq = 3`, but fails there with `Cirq = 1`; and publication `0`
is never returned. -/
lemma delayedInterrupt_loses {α : Type u} (a b : α) :
    (systemLTS stallHandler).MTr (initialSystem ()) (labels (delayedInterruptTrace a b))
        ⟨(), ⟨.poll, false, some (1, b), some (1, b)⟩, none⟩ ∧
      PublicationGap 1 8 (delayedInterruptTrace a b) ∧
      ((3 + 2 + 1 + 1 : ℕ) : ℝ) / 1 < 8 ∧
      RespondsWithin 3 2 1 1 (delayedInterruptTrace a b) 6 ∧
      RespondsWithin 3 2 3 1 (delayedInterruptTrace a b) 1 ∧
      ¬ RespondsWithin 3 2 1 1 (delayedInterruptTrace a b) 1 ∧
      NoOtherReader (labels (delayedInterruptTrace a b)) ∧
      publicationIds (labels (delayedInterruptTrace a b)) = [0, 1] ∧
      driverReadIds (labels (delayedInterruptTrace a b)) = [1] := by
  refine ⟨fixture_delayed_run a b, ?_, by norm_num, ?_, ?_, fixture_delayed_not_resp a b, ?_,
    rfl, rfl⟩
  · intro i j hij hi hj
    rcases fixture_delayed_pub' a b i hi with rfl | rfl <;>
      rcases fixture_delayed_pub' a b j hj with rfl | rfl
    · omega
    · norm_num [timeAt, cycleAt, delayedInterruptTrace]
    · omega
    · omega
  · refine ⟨11, by omega, ⟨false, rfl⟩, 1, 0, by omega, ?_, ?_, ?_⟩
    · simp [cycleAt, interruptCycles, delayedInterruptTrace, isInterruptStep]
    · simp [interruptCycles, delayedInterruptTrace, isInterruptStep]
    · intro h11
      simp [labels, delayedInterruptTrace] at h11
  · refine ⟨3, by omega, ⟨true, rfl⟩, 0, 0, by omega, ?_, ?_, ?_⟩
    · simp [cycleAt, interruptCycles, delayedInterruptTrace, isInterruptStep]
    · simp [interruptCycles, delayedInterruptTrace, isInterruptStep]
    · intro _
      refine ⟨7, by omega, ⟨some (1, b), rfl⟩, ?_, ?_⟩
      · simp [cycleAt, interruptCycles, delayedInterruptTrace, isInterruptStep]
      · simp [interruptCycles, delayedInterruptTrace, isInterruptStep]
  · intro k r h
    have hk := fixture_lt_of_getElem?_eq_some h
    rw [fixture_delayed_len] at hk
    interval_cases k <;> simp [labels, delayedInterruptTrace] at h

end PhyslibExt.Instrumentation.PollingSampleDeadline
