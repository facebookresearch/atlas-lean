/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Foundations.Semantics.Peripheral.OverwriteSampleRegister
public import CSLibExt.Foundations.Semantics.Peripheral.SampleReadyProtocol
public import CSLibExt.Foundations.Semantics.Peripheral.PollDriverSimulation

/-!
# Polling driver with a producer interrupt

The polling driver of `Cslib.Semantics.Peripheral.PollDriverSimulation`
extended with a producer interrupt that preempts it at every program
point. The closed state keeps three separate components: the
interrupt-local state, the driver-local state and the shared register
slot. A handler is an arbitrary transition relation over the whole
closed state with two actions, an interrupt-local step and an atomic
`publish id value`, so a handler that writes driver-local state or the
slot is expressible. The rely condition `Rely` requires every handler
step to preserve the whole driver-local state, to leave the slot
unchanged on a local step, and to perform a register `publish` on a
publication. Every step is one atomic transition of a sequentially
consistent interleaving; DMA, weak memory and torn accesses are not
modeled.

Observation maps polling-driver labels to themselves, an
interrupt-local step to the internal label `τ`, and an interrupt
publication to a publication of the environment, so atomic
publications and reads are retained. Under `Rely`, the refinement
relation (same slot, abstracted driver phase, interrupt state not
observed) is a stuttering simulation into the saturated sample-ready
protocol, stated with `Cslib.LTS.IsSimulation`. Consequently every
finite system trace erases to a protocol trace, its register operations
form a register trace that inherits the register's read-to-publication
correspondence, and every emitted sample was read as `some (n, v)` after
a publication of `(n, v)`, by the environment or by the interrupt, with
no publication in between.

## Main results

- `isSimulation_systemRefinement`: under `Rely`, the refinement
  relation is a simulation from the observed system into the saturated
  protocol.
- `producerInterrupt_correct`: under `Rely`, the initial states are
  related and every system trace erases to a protocol trace, runs on
  the register with its read-to-publication correspondence, and emits
  only samples fed by a read of their publication.
- `preemptionRun_valid`: a counting producer that preempts the driver
  before the Ready poll, between the poll and the read, and before the
  emit leaves the driver delivering exactly the sample it read.
- `not_rely_cacheClobberHandler`: an interrupt that overwrites the
  driver's cache violates `Rely`.
- `not_similarity_dataClobber`: an interrupt that overwrites the
  driver's loaded data violates `Rely` and makes the system not similar
  to the protocol.
-/

@[expose] public section

universe u v

namespace Cslib.Semantics.Peripheral.ProducerInterruptSimulation

open Cslib.Semantics.Peripheral.OverwriteSampleRegister
open Cslib.Semantics.Peripheral.SampleReadyProtocol
open Cslib.Semantics.Peripheral.PollDriverSimulation

/-! ### The producer interrupt, the rely condition and the closed system -/

/-- Actions of the producer interrupt handler: an interrupt-local computation step, or an
atomic publication `publish id value` to the shared sample register. -/
inductive InterruptAction (α : Type u) : Type u where
  | localStep
  | publish (id : ℕ) (value : α)

/-- State of the closed system: the interrupt-local state, the driver-local state and the shared
register slot, kept as three separate components. -/
structure SystemState (σ : Type v) (α : Type u) where
  /-- Interrupt-local state. -/
  isr : σ
  /-- Driver-local state: program point, loaded Ready bit, loaded data and cache. -/
  driver : DriverState α
  /-- The shared register slot. -/
  slot : Slot α

/-- A producer interrupt handler: a transition relation over the whole closed-system state, so
that a handler which writes driver-local state or the slot is expressible; `Rely` restricts
slot writes to publications. -/
abbrev InterruptHandler (σ : Type v) (α : Type u) :=
  Cslib.LTS (SystemState σ α) (InterruptAction α)

/-- The shared-register effect permitted for each handler action: an interrupt-local step leaves
the slot unchanged, and a publication is an atomic L1 `publish`. -/
def PermittedSlotEffect {α : Type u} : InterruptAction α → Slot α → Slot α → Prop
  | .localStep, s, s' => s' = s
  | .publish n v, s, s' => RegisterStep s (.publish n v) s'

/-- **Rely condition.** Every handler step preserves the whole driver-local state (so no handler
writes the driver's loaded data or its cache), and its only effect on the shared register is the
permitted one: none for a local step, an atomic publication for a publish. In particular no
handler reads or acknowledges the register on the driver's behalf. -/
def Rely {σ : Type v} {α : Type u} (H : InterruptHandler σ α) : Prop :=
  ∀ x a x', H.Tr x a x' → x'.driver = x.driver ∧ PermittedSlotEffect a x.slot x'.slot

/-- Labels of the closed system: a step of the polling-driver system (driver steps and the
environment's publications and reads, as in the polling-driver model), or an interrupt step. -/
inductive SystemLabel (α : Type u) : Type u where
  | driver (l : StepLabel α)
  | interrupt (a : InterruptAction α)

/-- Transitions of the closed system, a sequentially consistent interleaving. A polling-driver
system step leaves the interrupt-local state unchanged; an interrupt step is a handler step and
may preempt the driver at every program point. -/
inductive SystemStep {σ : Type v} {α : Type u} (H : InterruptHandler σ α) :
    SystemState σ α → SystemLabel α → SystemState σ α → Prop where
  | driver (q : σ) {d d' : DriverState α} {s s' : Slot α} {l : StepLabel α}
      (h : PollStep (d, s) l (d', s')) :
      SystemStep H ⟨q, d, s⟩ (.driver l) ⟨q, d', s'⟩
  | interrupt {x x' : SystemState σ α} {a : InterruptAction α} (h : H.Tr x a x') :
      SystemStep H x (.interrupt a) x'

/-- The closed driver/interrupt/register system as a `Cslib.LTS`. -/
def systemLTS {σ : Type v} {α : Type u} (H : InterruptHandler σ α) :
    Cslib.LTS (SystemState σ α) (SystemLabel α) where
  Tr := SystemStep H

/-- The initial system state: interrupt-local state `q₀`, the initial driver, an empty slot. -/
def initialSystem {σ : Type v} {α : Type u} (q₀ : σ) : SystemState σ α :=
  ⟨q₀, initialDriver, none⟩

/-! ### Erasure of interrupt-local steps, simulation and trace consequences -/

/-- Observation of a system label as a polling-driver label: driver-system labels are kept, an
interrupt-local step becomes the internal label `τ`, and an interrupt publication is retained as
an atomic publication of the environment. -/
def observe {α : Type u} : SystemLabel α → StepLabel α
  | .driver l => l
  | .interrupt .localStep => .internal
  | .interrupt (.publish n v) => .visible (.env (.publish n v))

/-- The closed system observed through `observe`. -/
def observedLTS {σ : Type v} {α : Type u} (H : InterruptHandler σ α) :
    Cslib.LTS (SystemState σ α) (StepLabel α) where
  Tr x l x' := ∃ m, observe m = l ∧ (systemLTS H).Tr x m x'

/-- Erasure of a system trace: drop driver-internal and interrupt-local steps, keep every other
step (interrupt publications as environment publications), in order. -/
def systemVisibleLabels {α : Type u} (ms : List (SystemLabel α)) : List (DriverLabel α) :=
  visibleLabels (ms.map observe)

/-- The register operations of a system trace (publications of the environment and of the
interrupt, reads of other readers and of the driver), in order. -/
def registerTrace {α : Type u} (ms : List (SystemLabel α)) : List (Label α) :=
  (systemVisibleLabels ms).filterMap registerLabel?

/-- The sample published by a system step, if it is a publication (by the environment or by the
interrupt). -/
def publication? {α : Type u} : SystemLabel α → Option (ℕ × α)
  | .driver (.visible (.env (.publish n v))) => some (n, v)
  | .interrupt (.publish n v) => some (n, v)
  | _ => none

/-- The refinement relation: same register slot, abstracted driver phase; the interrupt-local
state is not observed. -/
def systemRefinement {σ : Type v} {α : Type u} (x : SystemState σ α)
    (y : Phase α × Slot α) : Prop :=
  y = (abstractPhase x.driver, x.slot)

/-- The initial states are related. -/
theorem systemRefinement_initial {σ : Type v} {α : Type u} (q₀ : σ) :
    systemRefinement (initialSystem (α := α) q₀) (.idle, none) := by
  rfl

/-- **Conservative extension.** Every polling-driver trace is a system trace with the same
labels (wrapped as driver labels) and an untouched interrupt-local state, and wrapping then
observing a label is the identity. -/
theorem systemLTS_mtr_of_pollDriverLTS_mtr {σ : Type v} {α : Type u}
    (H : InterruptHandler σ α) (q : σ) (d d' : DriverState α) (s s' : Slot α)
    (ls : List (StepLabel α)) (h : (pollDriverLTS α).MTr (d, s) ls (d', s')) :
    (systemLTS H).MTr ⟨q, d, s⟩ (ls.map SystemLabel.driver) ⟨q, d', s'⟩ ∧
      (ls.map SystemLabel.driver).map observe = ls := by
  have hm : ∀ (p p' : DriverState α × Slot α) (l : List (StepLabel α)),
      (pollDriverLTS α).MTr p l p' →
        (systemLTS H).MTr ⟨q, p.1, p.2⟩ (l.map SystemLabel.driver) ⟨q, p'.1, p'.2⟩ := by
    intro p p' l hl
    induction hl with
    | refl => exact Cslib.LTS.MTr.refl
    | stepL htr _ ih => exact Cslib.LTS.MTr.stepL (SystemStep.driver q htr) ih
  refine ⟨hm (d, s) (d', s') ls h, ?_⟩
  rw [List.map_map]
  exact List.map_id _

/-- **Stuttering simulation with a producer interrupt.** Under the rely condition, the refinement
relation is a simulation from the observed closed system into the saturated protocol:
driver-system steps are matched as in the polling-driver simulation, interrupt-local steps by no
protocol step, and interrupt publications by the protocol's environment publication. -/
theorem isSimulation_systemRefinement {σ : Type v} {α : Type u} (H : InterruptHandler σ α)
    (hH : Rely H) :
    Cslib.LTS.IsSimulation (observedLTS H) (protocolLTS α).saturate systemRefinement := by
  rintro x y hr l x' ⟨m, rfl, htr⟩
  change y = _ at hr
  subst hr
  change SystemStep H x m x' at htr
  cases htr with
  | driver q h =>
      obtain ⟨y', hy', hr'⟩ := isSimulation_refinement rfl _ _ h
      exact ⟨y', hy', hr'⟩
  | @interrupt _ _ a h =>
      obtain ⟨hd, hs⟩ := hH _ _ _ h
      refine ⟨(abstractPhase x'.driver, x'.slot), ?_, rfl⟩
      rw [hd]
      cases a with
      | localStep =>
          have hs' : x'.slot = x.slot := hs
          rw [hs']
          exact Cslib.LTS.STr.refl
      | publish n v =>
          exact Cslib.LTS.STr.tr Relation.ReflTransGen.refl ⟨_, rfl, DriverStep.env _ hs⟩
            Relation.ReflTransGen.refl

/-- **Trace erasure.** Under the rely condition, every finite system trace from an initial state
erases, by dropping driver-internal and interrupt-local steps, to a protocol trace from the idle
empty state ending in the abstracted state. -/
theorem driverLTS_mtr_systemVisibleLabels {σ : Type v} {α : Type u}
    (H : InterruptHandler σ α) (hH : Rely H) (q₀ : σ) (ms : List (SystemLabel α))
    (x : SystemState σ α) (h : (systemLTS H).MTr (initialSystem q₀) ms x) :
    (driverLTS α).MTr (.idle, none) (systemVisibleLabels ms) (abstractPhase x.driver, x.slot) := by
  have hobs : ∀ (y y' : SystemState σ α) (l : List (SystemLabel α)), (systemLTS H).MTr y l y' →
      (observedLTS H).MTr y (l.map observe) y' := by
    intro y y' l hl
    induction hl with
    | refl => exact Cslib.LTS.MTr.refl
    | stepL htr _ ih => exact Cslib.LTS.MTr.stepL ⟨_, rfl, htr⟩ ih
  obtain ⟨y', hy', hr'⟩ := (isSimulation_systemRefinement H hH).sim_trace
    (systemRefinement_initial q₀) (ms.map observe) x (hobs _ _ _ h)
  change y' = _ at hr'
  subst hr'
  exact driverLTS_mtr_of_saturate_mtr hy'

/-- **Legal L1 trace.** Under the rely condition, the register operations of every finite system
trace from an initial state form an L1 register trace from the empty slot. -/
theorem registerLTS_mtr_registerTrace {σ : Type v} {α : Type u}
    (H : InterruptHandler σ α) (hH : Rely H) (q₀ : σ) (ms : List (SystemLabel α))
    (x : SystemState σ α) (h : (systemLTS H).MTr (initialSystem q₀) ms x) :
    (registerLTS α).MTr none (registerTrace ms) x.slot := by
  exact registerLTS_mtr_filterMap_of_driverLTS_mtr .idle (abstractPhase x.driver) none x.slot
    (systemVisibleLabels ms) (driverLTS_mtr_systemVisibleLabels H hH q₀ ms x h)

/-- **Emitted samples carry their publication.** Under the rely condition, in every finite system
trace from an initial state, every emitted sample `(n, v)` is the `some (n, v)` result of an
earlier driver read, and that read is preceded by a publication of `(n, v)` (by the environment
or by the interrupt) with no publication of either kind in between. -/
theorem exists_publication_of_deliver {σ : Type v} {α : Type u}
    (H : InterruptHandler σ α) (hH : Rely H) (q₀ : σ) (ms : List (SystemLabel α))
    (x : SystemState σ α) (h : (systemLTS H).MTr (initialSystem q₀) ms x)
    (i n : ℕ) (v : α) (hi : ms[i]? = some (.driver (.visible (.deliver n v)))) :
    ∃ j k, k < j ∧ j < i ∧ ms[j]? = some (.driver (.visible (.read (some (n, v))))) ∧
      (ms[k]?).bind publication? = some (n, v) ∧
      ∀ l : ℕ, k < l → l < j → (ms[l]?).bind publication? = none := by
  have getLt : ∀ (L : List (SystemLabel α)) (μ : SystemLabel α) (l : ℕ), l < L.length →
      (L ++ [μ])[l]? = L[l]? := fun L μ l hl => List.getElem?_append_left hl
  have getLen : ∀ (L : List (SystemLabel α)) (μ : SystemLabel α),
      (L ++ [μ])[L.length]? = some μ := fun L μ => by simp
  have getGt : ∀ (L : List (SystemLabel α)) (μ : SystemLabel α) (l : ℕ), L.length < l →
      (L ++ [μ])[l]? = none := fun L μ l hl => by
    rw [List.getElem?_eq_none_iff]
    simp only [List.length_append, List.length_singleton]
    omega
  have step : ∀ (pre : List (SystemLabel α)) (x0 x1 : SystemState σ α) (μ : SystemLabel α),
      (systemLTS H).Tr x0 μ x1 →
      (∀ (n : ℕ) (v : α), x0.slot = some (n, v) → ∃ k, k < pre.length ∧
        (pre[k]?).bind publication? = some (n, v) ∧
        ∀ l, k < l → l < pre.length → (pre[l]?).bind publication? = none) →
      (∀ (n : ℕ) (v : α), (x0.driver.pc = .branchData ∨ x0.driver.pc = .emit) →
        x0.driver.data = some (n, v) → ∃ j k, k < j ∧ j < pre.length ∧
          pre[j]? = some (.driver (.visible (.read (some (n, v))))) ∧
          (pre[k]?).bind publication? = some (n, v) ∧
          ∀ l, k < l → l < j → (pre[l]?).bind publication? = none) →
      (∀ (i n : ℕ) (v : α), pre[i]? = some (.driver (.visible (.deliver n v))) →
        ∃ j k, k < j ∧ j < i ∧ pre[j]? = some (.driver (.visible (.read (some (n, v))))) ∧
          (pre[k]?).bind publication? = some (n, v) ∧
          ∀ l, k < l → l < j → (pre[l]?).bind publication? = none) →
      (∀ (n : ℕ) (v : α), x1.slot = some (n, v) → ∃ k, k < (pre ++ [μ]).length ∧
        ((pre ++ [μ])[k]?).bind publication? = some (n, v) ∧
        ∀ l, k < l → l < (pre ++ [μ]).length → ((pre ++ [μ])[l]?).bind publication? = none) ∧
      (∀ (n : ℕ) (v : α), (x1.driver.pc = .branchData ∨ x1.driver.pc = .emit) →
        x1.driver.data = some (n, v) → ∃ j k, k < j ∧ j < (pre ++ [μ]).length ∧
          (pre ++ [μ])[j]? = some (.driver (.visible (.read (some (n, v))))) ∧
          ((pre ++ [μ])[k]?).bind publication? = some (n, v) ∧
          ∀ l, k < l → l < j → ((pre ++ [μ])[l]?).bind publication? = none) ∧
      (∀ (i n : ℕ) (v : α), (pre ++ [μ])[i]? = some (.driver (.visible (.deliver n v))) →
        ∃ j k, k < j ∧ j < i ∧
          (pre ++ [μ])[j]? = some (.driver (.visible (.read (some (n, v))))) ∧
          ((pre ++ [μ])[k]?).bind publication? = some (n, v) ∧
          ∀ l, k < l → l < j → ((pre ++ [μ])[l]?).bind publication? = none) := by
    intro pre x0 x1 μ htr hS hD hE
    have hlen : (pre ++ [μ]).length = pre.length + 1 := by simp
    have liftW : ∀ (n : ℕ) (v : α) (j k : ℕ), k < j → j < pre.length →
        pre[j]? = some (.driver (.visible (.read (some (n, v))))) →
        (pre[k]?).bind publication? = some (n, v) →
        (∀ l, k < l → l < j → (pre[l]?).bind publication? = none) →
        (pre ++ [μ])[j]? = some (.driver (.visible (.read (some (n, v))))) ∧
          ((pre ++ [μ])[k]?).bind publication? = some (n, v) ∧
          ∀ l, k < l → l < j → ((pre ++ [μ])[l]?).bind publication? = none := by
      intro n v j k hkj hj hr hp hn
      refine ⟨by rw [getLt _ _ _ hj]; exact hr, by rw [getLt _ _ _ (by omega)]; exact hp, ?_⟩
      intro l h1 h2
      rw [getLt _ _ _ (by omega)]
      exact hn l h1 h2
    have liftD : x1.driver = x0.driver →
        ∀ (n : ℕ) (v : α), (x1.driver.pc = .branchData ∨ x1.driver.pc = .emit) →
          x1.driver.data = some (n, v) → ∃ j k, k < j ∧ j < (pre ++ [μ]).length ∧
            (pre ++ [μ])[j]? = some (.driver (.visible (.read (some (n, v))))) ∧
            ((pre ++ [μ])[k]?).bind publication? = some (n, v) ∧
            ∀ l, k < l → l < j → ((pre ++ [μ])[l]?).bind publication? = none := by
      intro hd n v hpc hdat
      rw [hd] at hpc hdat
      obtain ⟨j, k, hkj, hj, hr, hp, hn⟩ := hD n v hpc hdat
      obtain ⟨a, b, c⟩ := liftW n v j k hkj hj hr hp hn
      exact ⟨j, k, hkj, by rw [hlen]; omega, a, b, c⟩
    have liftS : publication? μ = none → x1.slot = x0.slot →
        ∀ (n : ℕ) (v : α), x1.slot = some (n, v) → ∃ k, k < (pre ++ [μ]).length ∧
          ((pre ++ [μ])[k]?).bind publication? = some (n, v) ∧
          ∀ l, k < l → l < (pre ++ [μ]).length → ((pre ++ [μ])[l]?).bind publication? = none := by
      intro hpub hs n v hsl
      rw [hs] at hsl
      obtain ⟨k, hk, hp, hn⟩ := hS n v hsl
      refine ⟨k, by rw [hlen]; omega, by rw [getLt _ _ _ hk]; exact hp, ?_⟩
      intro l h1 h2
      rw [hlen] at h2
      rcases Nat.lt_or_ge l pre.length with h3 | h3
      · rw [getLt _ _ _ h3]
        exact hn l h1 h3
      · have h4 : l = pre.length := by omega
        subst h4
        rw [getLen]
        exact hpub
    have newS : ∀ (n : ℕ) (v : α), publication? μ = some (n, v) → x1.slot = some (n, v) →
        ∀ (n' : ℕ) (v' : α), x1.slot = some (n', v') → ∃ k, k < (pre ++ [μ]).length ∧
          ((pre ++ [μ])[k]?).bind publication? = some (n', v') ∧
          ∀ l, k < l → l < (pre ++ [μ]).length → ((pre ++ [μ])[l]?).bind publication? = none := by
      intro n v hpub hs n' v' hsl
      rw [hs] at hsl
      cases hsl
      refine ⟨pre.length, by rw [hlen]; omega, by rw [getLen]; exact hpub, ?_⟩
      intro l h1 h2
      rw [hlen] at h2
      omega
    have liftE : (∀ (n : ℕ) (v : α), μ = .driver (.visible (.deliver n v)) → ∃ j k, k < j ∧
          j < pre.length ∧ pre[j]? = some (.driver (.visible (.read (some (n, v))))) ∧
          (pre[k]?).bind publication? = some (n, v) ∧
          ∀ l, k < l → l < j → (pre[l]?).bind publication? = none) →
        ∀ (i n : ℕ) (v : α), (pre ++ [μ])[i]? = some (.driver (.visible (.deliver n v))) →
          ∃ j k, k < j ∧ j < i ∧
            (pre ++ [μ])[j]? = some (.driver (.visible (.read (some (n, v))))) ∧
            ((pre ++ [μ])[k]?).bind publication? = some (n, v) ∧
            ∀ l, k < l → l < j → ((pre ++ [μ])[l]?).bind publication? = none := by
      intro hnew i n v hi
      rcases lt_trichotomy i pre.length with h | h | h
      · rw [getLt _ _ _ h] at hi
        obtain ⟨j, k, hkj, hji, hr, hp, hn⟩ := hE i n v hi
        obtain ⟨a, b, c⟩ := liftW n v j k hkj (by omega) hr hp hn
        exact ⟨j, k, hkj, hji, a, b, c⟩
      · subst h
        rw [getLen] at hi
        obtain ⟨j, k, hkj, hj, hr, hp, hn⟩ := hnew n v (Option.some.inj hi)
        obtain ⟨a, b, c⟩ := liftW n v j k hkj hj hr hp hn
        exact ⟨j, k, hkj, hj, a, b, c⟩
      · rw [getGt _ _ _ h] at hi
        cases hi
    change SystemStep H x0 μ x1 at htr
    cases htr with
    | driver q h =>
        cases h with
        | env d h =>
            cases h with
            | publish n v =>
                exact ⟨newS n v rfl rfl, liftD rfl, liftE (fun _ _ h => by cases h)⟩
            | read =>
                exact ⟨(fun _ _ h => by cases h), liftD rfl, liftE (fun _ _ h => by cases h)⟩
        | loadReady d s hpc =>
            exact ⟨liftS rfl rfl, (fun _ _ hp _ => by rcases hp with hp | hp <;> cases hp),
              liftE (fun _ _ h => by cases h)⟩
        | readyTaken d s hpc hr =>
            exact ⟨liftS rfl rfl, (fun _ _ hp _ => by rcases hp with hp | hp <;> cases hp),
              liftE (fun _ _ h => by cases h)⟩
        | readyNotTaken d s hpc hr =>
            exact ⟨liftS rfl rfl, (fun _ _ hp _ => by rcases hp with hp | hp <;> cases hp),
              liftE (fun _ _ h => by cases h)⟩
        | loadData d hpc h =>
            cases h with
            | read =>
                refine ⟨(fun _ _ h => by cases h), ?_, liftE (fun _ _ h => by cases h)⟩
                intro n v _ hdat
                obtain ⟨k, hk, hp, hn⟩ := hS n v hdat
                refine ⟨pre.length, k, hk, by rw [hlen]; omega, ?_,
                  by rw [getLt _ _ _ hk]; exact hp, ?_⟩
                · rw [getLen]
                  exact congrArg (fun r => some (SystemLabel.driver (.visible (.read r)))) hdat
                · intro l h1 h2
                  rw [getLt _ _ _ h2]
                  exact hn l h1 h2
        | dataPresent d s n v hpc hd =>
            refine ⟨liftS rfl rfl, ?_, liftE (fun _ _ h => by cases h)⟩
            intro n' v' _ hdat
            obtain ⟨j, k, hkj, hj, hr, hp, hn⟩ := hD n' v' (Or.inl hpc) hdat
            obtain ⟨a, b, c⟩ := liftW n' v' j k hkj hj hr hp hn
            exact ⟨j, k, hkj, by rw [hlen]; omega, a, b, c⟩
        | dataAbsent d s hpc hd =>
            exact ⟨liftS rfl rfl, (fun _ _ hp _ => by rcases hp with hp | hp <;> cases hp),
              liftE (fun _ _ h => by cases h)⟩
        | emit d s n v hpc hd =>
            refine ⟨liftS rfl rfl, (fun _ _ hp _ => by rcases hp with hp | hp <;> cases hp),
              liftE ?_⟩
            intro n' v' h
            cases h
            exact hD _ _ (Or.inr hpc) hd
        | record d s hpc =>
            exact ⟨liftS rfl rfl, (fun _ _ hp _ => by rcases hp with hp | hp <;> cases hp),
              liftE (fun _ _ h => by cases h)⟩
    | @interrupt _ _ a h =>
        obtain ⟨hd, hs⟩ := hH _ _ _ h
        cases a with
        | localStep =>
            have hs' : x1.slot = x0.slot := hs
            exact ⟨liftS rfl hs', liftD hd, liftE (fun _ _ h => by cases h)⟩
        | publish n v =>
            have hs' : x1.slot = some (n, v) := (registerLTS_tr_publish_iff _ _ _ _).mp hs
            exact ⟨newS n v rfl hs', liftD hd, liftE (fun _ _ h => by cases h)⟩
  have run : ∀ (ls : List (SystemLabel α)) (x0 x1 : SystemState σ α),
      (systemLTS H).MTr x0 ls x1 → ∀ pre : List (SystemLabel α),
      (∀ (n : ℕ) (v : α), x0.slot = some (n, v) → ∃ k, k < pre.length ∧
        (pre[k]?).bind publication? = some (n, v) ∧
        ∀ l, k < l → l < pre.length → (pre[l]?).bind publication? = none) →
      (∀ (n : ℕ) (v : α), (x0.driver.pc = .branchData ∨ x0.driver.pc = .emit) →
        x0.driver.data = some (n, v) → ∃ j k, k < j ∧ j < pre.length ∧
          pre[j]? = some (.driver (.visible (.read (some (n, v))))) ∧
          (pre[k]?).bind publication? = some (n, v) ∧
          ∀ l, k < l → l < j → (pre[l]?).bind publication? = none) →
      (∀ (i n : ℕ) (v : α), pre[i]? = some (.driver (.visible (.deliver n v))) →
        ∃ j k, k < j ∧ j < i ∧ pre[j]? = some (.driver (.visible (.read (some (n, v))))) ∧
          (pre[k]?).bind publication? = some (n, v) ∧
          ∀ l, k < l → l < j → (pre[l]?).bind publication? = none) →
      (∀ (i n : ℕ) (v : α), (pre ++ ls)[i]? = some (.driver (.visible (.deliver n v))) →
        ∃ j k, k < j ∧ j < i ∧
          (pre ++ ls)[j]? = some (.driver (.visible (.read (some (n, v))))) ∧
          ((pre ++ ls)[k]?).bind publication? = some (n, v) ∧
          ∀ l, k < l → l < j → ((pre ++ ls)[l]?).bind publication? = none) := by
    intro ls x0 x1 hm
    induction hm with
    | refl =>
        intro pre _ _ hE
        rw [List.append_nil]
        exact hE
    | @stepL s1 μ s2 μs s3 htr _ ih =>
        intro pre hS hD hE
        obtain ⟨hS', hD', hE'⟩ := step pre s1 s2 μ htr hS hD hE
        have h' := ih (pre ++ [μ]) hS' hD' hE'
        rw [List.append_assoc, List.singleton_append] at h'
        exact h'
  have hfin := run ms _ _ h []
    (fun n v hs => by simp [initialSystem] at hs)
    (fun n v hp _ => by simp [initialSystem, initialDriver] at hp)
    (fun i n v hi => by simp at hi)
  rw [List.nil_append] at hfin
  exact hfin i n v hi

/-- **Producer-interrupt driver correctness (headline).** For every producer interrupt handler
satisfying the rely condition and every initial interrupt-local state: the initial states are
related; the refinement relation is a stuttering simulation from the observed closed system into
the saturated sample-ready protocol; and every finite system trace from the initial state
(1) erases, dropping driver-internal and interrupt-local steps and retaining atomic Publish/Read
steps, to a protocol trace ending in the abstracted state; (2) has register operations forming a
legal L1 register trace from the empty slot; (3) on that L1 trace, every successful read of
`(n, v)` is preceded by `publish n v` with no publication in between, and successful read IDs
inject, ID-preservingly, into publication IDs; (4) if the publication IDs of that L1 trace are
strictly increasing, so are its successful read IDs; and (5) every emitted sample `(n, v)` is the
`some (n, v)` result of an earlier driver read preceded by a publication of `(n, v)` with no
publication in between. -/
theorem producerInterrupt_correct {σ : Type v} {α : Type u} (H : InterruptHandler σ α)
    (hH : Rely H) (q₀ : σ) :
    systemRefinement (initialSystem (α := α) q₀) (.idle, none) ∧
      Cslib.LTS.IsSimulation (observedLTS H) (protocolLTS α).saturate systemRefinement ∧
      ∀ (ms : List (SystemLabel α)) (x : SystemState σ α),
        (systemLTS H).MTr (initialSystem q₀) ms x →
          (driverLTS α).MTr (.idle, none) (systemVisibleLabels ms)
              (abstractPhase x.driver, x.slot) ∧
            (registerLTS α).MTr none (registerTrace ms) x.slot ∧
            (∀ (i n : ℕ) (v : α), (registerTrace ms)[i]? = some (.read (some (n, v))) →
              ∃ j, j < i ∧ (registerTrace ms)[j]? = some (.publish n v) ∧
                ∀ k m w, j < k → k < i → (registerTrace ms)[k]? ≠ some (.publish m w)) ∧
            (∃ f : Fin (readIds (registerTrace ms)).length →
                Fin (publishIds (registerTrace ms)).length,
              Function.Injective f ∧
                ∀ k, (publishIds (registerTrace ms))[f k] = (readIds (registerTrace ms))[k]) ∧
            ((publishIds (registerTrace ms)).Pairwise (· < ·) →
              (readIds (registerTrace ms)).Pairwise (· < ·)) ∧
            ∀ (i n : ℕ) (v : α), ms[i]? = some (.driver (.visible (.deliver n v))) →
              ∃ j k, k < j ∧ j < i ∧ ms[j]? = some (.driver (.visible (.read (some (n, v))))) ∧
                (ms[k]?).bind publication? = some (n, v) ∧
                ∀ l : ℕ, k < l → l < j → (ms[l]?).bind publication? = none := by
  refine ⟨systemRefinement_initial q₀, isSimulation_systemRefinement H hH, ?_⟩
  intro ms x h
  have h1 := driverLTS_mtr_systemVisibleLabels H hH q₀ ms x h
  have h2 := registerLTS_mtr_registerTrace H hH q₀ ms x h
  exact ⟨h1, h2, fun i n v hi => exists_publish_index_of_read_mem _ _ h2 i n v hi,
    exists_injective_readIds_to_publishIds _ _ h2, fun hinc => readIds_pairwise_lt _ _ h2 hinc,
    fun i n v hi => exists_publication_of_deliver H hH q₀ ms x h i n v hi⟩

/-! ### Validation -/

/-- A counting producer: an interrupt-local step arms the next sample, then an atomic publication
publishes `(k, sample k)` and advances the counter. Driver state and slot are otherwise
untouched. -/
inductive CounterStep {α : Type u} (sample : ℕ → α) :
    SystemState (ℕ × Bool) α → InterruptAction α → SystemState (ℕ × Bool) α → Prop where
  | arm (k : ℕ) (d : DriverState α) (s : Slot α) :
      CounterStep sample ⟨(k, false), d, s⟩ .localStep ⟨(k, true), d, s⟩
  | fire (k : ℕ) (d : DriverState α) (s : Slot α) :
      CounterStep sample ⟨(k, true), d, s⟩ (.publish k (sample k))
        ⟨(k + 1, false), d, some (k, sample k)⟩

/-- The counting producer as an interrupt handler. -/
def counterHandler {α : Type u} (sample : ℕ → α) : InterruptHandler (ℕ × Bool) α where
  Tr := CounterStep sample

/-- The counting producer satisfies the rely condition. -/
theorem rely_counterHandler {α : Type u} (sample : ℕ → α) : Rely (counterHandler sample) := by
  intro x a x' h
  cases h with
  | arm k d s => exact ⟨rfl, rfl⟩
  | fire k d s => exact ⟨rfl, RegisterStep.publish _ _ _⟩

/-- A run with preemption at the three program points: the interrupt arms and publishes `0`
before the Ready poll; arms and publishes `1` between the Ready poll and the read (after the
branch, before the load); and arms and publishes `2` after the read, before the emit. The driver
reads and emits `(1, sample 1)`. -/
def preemptionRun {α : Type u} (sample : ℕ → α) : List (SystemLabel α) :=
  [.interrupt .localStep, .interrupt (.publish 0 (sample 0)),
    .driver (.visible (.poll true)), .driver .internal,
    .interrupt .localStep, .interrupt (.publish 1 (sample 1)),
    .driver (.visible (.read (some (1, sample 1)))), .driver .internal,
    .interrupt .localStep, .interrupt (.publish 2 (sample 2)),
    .driver (.visible (.deliver 1 (sample 1))), .driver .internal]

/-- **Preemption before Ready, between Ready and Read, and before emit.** The preemption run is a
system trace of the counting producer; its erasure is a protocol trace ending idle with sample
`2` pending; its register operations are the L1 trace `publish 0, publish 1, read (1, _),
publish 2`; and the only sample delivered is the one with ID `1`, not the newer `2`. -/
theorem preemptionRun_valid {α : Type u} (sample : ℕ → α) :
    (systemLTS (counterHandler sample)).MTr (initialSystem (0, false)) (preemptionRun sample)
        ⟨(3, false), ⟨.poll, true, some (1, sample 1), some (1, sample 1)⟩,
          some (2, sample 2)⟩ ∧
      (driverLTS α).MTr (.idle, none) (systemVisibleLabels (preemptionRun sample))
        (.idle, some (2, sample 2)) ∧
      registerTrace (preemptionRun sample) =
        [.publish 0 (sample 0), .publish 1 (sample 1), .read (some (1, sample 1)),
          .publish 2 (sample 2)] ∧
      deliveredIds (systemVisibleLabels (preemptionRun sample)) = [1] := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · exact
      .stepL (SystemStep.interrupt (CounterStep.arm _ _ _)) <|
      .stepL (SystemStep.interrupt (CounterStep.fire _ _ _)) <|
      .stepL (SystemStep.driver _ (PollStep.loadReady _ _ rfl)) <|
      .stepL (SystemStep.driver _ (PollStep.readyTaken _ _ rfl rfl)) <|
      .stepL (SystemStep.interrupt (CounterStep.arm _ _ _)) <|
      .stepL (SystemStep.interrupt (CounterStep.fire _ _ _)) <|
      .stepL (SystemStep.driver _ (PollStep.loadData _ rfl (RegisterStep.read _))) <|
      .stepL (SystemStep.driver _ (PollStep.dataPresent _ _ 1 (sample 1) rfl rfl)) <|
      .stepL (SystemStep.interrupt (CounterStep.arm _ _ _)) <|
      .stepL (SystemStep.interrupt (CounterStep.fire _ _ _)) <|
      .stepL (SystemStep.driver _ (PollStep.emit _ _ 1 (sample 1) rfl rfl)) <|
      .stepL (SystemStep.driver _ (PollStep.record _ _ rfl)) .refl
  · exact
      .stepL (DriverStep.env _ (RegisterStep.publish _ 0 (sample 0))) <|
      .stepL (DriverStep.poll _) <|
      .stepL (DriverStep.env _ (RegisterStep.publish _ 1 (sample 1))) <|
      .stepL (DriverStep.read (RegisterStep.read _)) <|
      .stepL (DriverStep.env _ (RegisterStep.publish _ 2 (sample 2))) <|
      .stepL (DriverStep.deliver _ _ _) .refl

/-- Faulty interrupt: an interrupt-local step that overwrites the driver's cache of the last
emitted sample with `c`. -/
inductive CacheClobberStep {α : Type u} (c : ℕ × α) :
    SystemState Unit α → InterruptAction α → SystemState Unit α → Prop where
  | clobber (x : SystemState Unit α) :
      CacheClobberStep c x .localStep { x with driver := { x.driver with cache := some c } }

/-- The cache-clobbering interrupt as a handler. -/
def cacheClobberHandler {α : Type u} (c : ℕ × α) : InterruptHandler Unit α where
  Tr := CacheClobberStep c

/-- **An interrupt that overwrites driver-local cached data violates the rely condition.** -/
theorem not_rely_cacheClobberHandler {α : Type u} (c : ℕ × α) :
    ¬ Rely (cacheClobberHandler c) := by
  intro hR
  have h := (hR (initialSystem ()) .localStep _ (CacheClobberStep.clobber _)).1
  have h2 := congrArg DriverState.cache h
  simp [initialSystem, initialDriver] at h2

/-- Faulty interrupt: an interrupt-local step that overwrites the driver's loaded data (its
local copy of the sample it read) with `some c`. -/
inductive DataClobberStep {α : Type u} (c : ℕ × α) :
    SystemState Unit α → InterruptAction α → SystemState Unit α → Prop where
  | clobber (x : SystemState Unit α) :
      DataClobberStep c x .localStep { x with driver := { x.driver with data := some c } }

/-- The data-clobbering interrupt as a handler. -/
def dataClobberHandler {α : Type u} (c : ℕ × α) : InterruptHandler Unit α where
  Tr := DataClobberStep c

/-- The data-clobbering interrupt violates the rely condition. -/
theorem not_rely_dataClobberHandler {α : Type u} (c : ℕ × α) :
    ¬ Rely (dataClobberHandler c) := by
  intro hR
  have h := (hR (initialSystem ()) .localStep _ (DataClobberStep.clobber _)).1
  have h2 := congrArg DriverState.data h
  simp [initialSystem, initialDriver] at h2

/-- A data-clobbering run: the environment publishes `(0, a)`; the driver polls, branches and
reads it; the interrupt overwrites the loaded data with `(1, b)`; the driver branches and emits
`(1, b)`. -/
def dataClobberRun {α : Type u} (a b : α) : List (SystemLabel α) :=
  [.driver (.visible (.env (.publish 0 a))), .driver (.visible (.poll true)), .driver .internal,
    .driver (.visible (.read (some (0, a)))), .interrupt .localStep, .driver .internal,
    .driver (.visible (.deliver 1 b))]

/-- **Violating the rely condition breaks the correspondence (trace form).** The data-clobbering
run is a system trace; its erasure is no protocol trace; and the emitted sample `(1, b)` was
never published in it. -/
theorem dataClobberRun_not_protocol_trace {α : Type u} (a b : α) :
    (∃ x, (systemLTS (dataClobberHandler (1, b))).MTr (initialSystem ()) (dataClobberRun a b) x) ∧
      (¬ ∃ y, (driverLTS α).MTr (.idle, none) (systemVisibleLabels (dataClobberRun a b)) y) ∧
      ∀ k : ℕ, ((dataClobberRun a b)[k]?).bind publication? ≠ some (1, b) := by
  refine ⟨⟨⟨(), ⟨.record, true, some (1, b), none⟩, none⟩, ?_⟩, ?_, ?_⟩
  · exact
      .stepL (SystemStep.driver _ (PollStep.env _ (RegisterStep.publish _ 0 a))) <|
      .stepL (SystemStep.driver _ (PollStep.loadReady _ _ rfl)) <|
      .stepL (SystemStep.driver _ (PollStep.readyTaken _ _ rfl rfl)) <|
      .stepL (SystemStep.driver _ (PollStep.loadData _ rfl (RegisterStep.read _))) <|
      .stepL (SystemStep.interrupt (DataClobberStep.clobber _)) <|
      .stepL (SystemStep.driver _ (PollStep.dataPresent _ _ 1 b rfl rfl)) <|
      .stepL (SystemStep.driver _ (PollStep.emit _ _ 1 b rfl rfl)) .refl
  · rintro ⟨y, h⟩
    change (driverLTS α).MTr (.idle, none)
      [.env (.publish 0 a), .poll true, .read (some (0, a)), .deliver 1 b] y at h
    cases h with | stepL h1 r1 =>
    cases h1 with | env _ h1 =>
    cases h1
    cases r1 with | stepL h2 r2 =>
    cases h2
    cases r2 with | stepL h3 r3 =>
    cases h3 with | read h3 =>
    cases h3
    cases r3 with | stepL h4 r4 =>
    cases h4
  · intro k
    rcases k with _ | _ | _ | _ | _ | _ | _ | k
    all_goals simp [dataClobberRun, publication?]

/-- **Violating the rely condition breaks the simulation.** The data-clobbering system is not
similar to the saturated protocol from the initial states. -/
theorem not_similarity_dataClobber {α : Type u} (a b : α) :
    ¬ Cslib.LTS.Similarity (observedLTS (dataClobberHandler (1, b))) (protocolLTS α).saturate
      (initialSystem (α := α) ()) (.idle, none) := by
  rintro ⟨r, hr, hsim⟩
  have hobs : ∀ (y y' : SystemState Unit α) (l : List (SystemLabel α)),
      (systemLTS (dataClobberHandler (1, b))).MTr y l y' →
      (observedLTS (dataClobberHandler (1, b))).MTr y (l.map observe) y' := by
    intro y y' l hl
    induction hl with
    | refl => exact Cslib.LTS.MTr.refl
    | stepL htr _ ih => exact Cslib.LTS.MTr.stepL ⟨_, rfl, htr⟩ ih
  obtain ⟨x, hx⟩ := (dataClobberRun_not_protocol_trace a b).1
  obtain ⟨y', hy', -⟩ := hsim.sim_trace hr _ _ (hobs _ _ _ hx)
  exact (dataClobberRun_not_protocol_trace a b).2.1 ⟨y', driverLTS_mtr_of_saturate_mtr hy'⟩

end Cslib.Semantics.Peripheral.ProducerInterruptSimulation
