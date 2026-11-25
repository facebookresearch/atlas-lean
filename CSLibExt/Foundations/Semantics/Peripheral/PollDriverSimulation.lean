/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Foundations.Semantics.Peripheral.OverwriteSampleRegister
public import CSLibExt.Foundations.Semantics.Peripheral.SampleReadyProtocol
public import Cslib.Foundations.Semantics.LTS.Simulation

/-!
# Polling driver simulation

A polling driver for the overwrite-sample register, modelled as a
labeled transition system with a program counter and three local
variables: the last loaded Ready bit, the last loaded optional value
and a cache of the last emitted sample. Its two volatile accesses are
the Ready poll and the atomic optional read of the sample-ready
protocol; its emits deliver a sample. Branching after a nonempty
observation and recording the cache are internal `τ` steps; branching
back to the poll after an empty observation is the protocol's visible
`retry`. Publications and reads by other permitted readers interleave
at every program point. Every register access is one atomic
transition of a sequentially consistent interleaving; no compiler
reordering or weak-memory behavior is modeled.

The driver is related to the closed sample-ready protocol (all steps
visible) by a stuttering simulation into its saturation, stated with
`Cslib.LTS.IsSimulation`. Consequently every finite driver trace
erases, by dropping its internal steps, to a protocol trace, its
register operations form a register trace, and every emitted sample
`(n, v)` was read as `some (n, v)` after the publication `publish n v`
with no other publication in between.

## Main results

- `isSimulation_refinement`: the refinement relation is a simulation
  from the driver into the saturated protocol.
- `pollDriver_correct`: the initial states are related, and every
  driver trace erases to a protocol trace, runs on the register and
  preserves sample IDs and values.
- `threePollRun_valid`: a three-iteration run with an empty read and a
  successful read delivers exactly the sample with ID `1`.
- `not_similarity_staleCacheDriver`: a driver that emits its cached
  sample on an empty read is not similar to the protocol.
-/

@[expose] public section

universe u

namespace Cslib.Semantics.Peripheral.PollDriverSimulation

open Cslib.Semantics.Peripheral.OverwriteSampleRegister
open Cslib.Semantics.Peripheral.SampleReadyProtocol

/-! ### Labels and the specification -/

/-- Labels shared by the driver and the specification: a visible protocol event, or an
internal local computation step of the driver. -/
inductive StepLabel (α : Type u) : Type u where
  | visible (μ : DriverLabel α)
  | internal

/-- The internal label is the canonical `τ`. -/
instance instHasTauStepLabel (α : Type u) : Cslib.HasTau (StepLabel α) :=
  ⟨StepLabel.internal⟩

/-- The protocol event carried by a label, if it is visible. -/
def visibleLabel? {α : Type u} : StepLabel α → Option (DriverLabel α)
  | .visible μ => some μ
  | .internal => none

/-- Erasure of internal steps: the visible protocol events of a trace, in order. -/
def visibleLabels {α : Type u} (ls : List (StepLabel α)) : List (DriverLabel α) :=
  ls.filterMap visibleLabel?

/-- The sampled-register trace specification over the shared labels: the closed sample-ready
protocol system, every step visible, no internal steps. -/
def protocolLTS (α : Type u) : Cslib.LTS (Phase α × Slot α) (StepLabel α) where
  Tr x l x' := ∃ μ, l = .visible μ ∧ (driverLTS α).Tr x μ x'

/-! ### The polling driver -/

/-- Program points of the polling driver loop. -/
inductive ProgramPoint : Type where
  /-- About to load the Ready register. -/
  | poll
  /-- About to branch on the loaded Ready bit. -/
  | branchReady
  /-- About to load the data register (atomic optional read). -/
  | load
  /-- About to branch on the loaded optional value. -/
  | branchData
  /-- About to emit the loaded sample. -/
  | emit
  /-- About to record the emitted sample in the local cache. -/
  | record
  deriving DecidableEq

/-- Driver local state: program point, last loaded Ready bit, last loaded optional value, and
a cache of the last emitted sample. -/
structure DriverState (α : Type u) : Type u where
  /-- Program point. -/
  pc : ProgramPoint
  /-- Last loaded Ready bit. -/
  readyBit : Bool
  /-- Last loaded optional value of the data register. -/
  data : Option (ℕ × α)
  /-- Last emitted sample. -/
  cache : Option (ℕ × α)

/-- The initial driver state: about to poll, nothing loaded, empty cache. -/
def initialDriver {α : Type u} : DriverState α :=
  ⟨.poll, false, none, none⟩

/-- Transitions of the closed driver/register system. Environment steps (publications and reads
by other permitted readers) are L1 register steps at every program point. The two volatile
accesses are the Ready load (a protocol `poll`) and the data load (a protocol `read`, an atomic
L1 read). Branching after a nonempty observation and recording the cache are internal; branching
back after an empty observation is the protocol `retry`; the emit is the protocol `deliver`. -/
inductive PollStep {α : Type u} :
    DriverState α × Slot α → StepLabel α → DriverState α × Slot α → Prop where
  | env (d : DriverState α) {s s' : Slot α} {μ : Label α} (h : RegisterStep s μ s') :
      PollStep (d, s) (.visible (.env μ)) (d, s')
  | loadReady (d : DriverState α) (s : Slot α) (hpc : d.pc = .poll) :
      PollStep (d, s) (.visible (.poll (ready s)))
        ({ d with pc := .branchReady, readyBit := ready s }, s)
  | readyTaken (d : DriverState α) (s : Slot α) (hpc : d.pc = .branchReady)
      (hr : d.readyBit = true) :
      PollStep (d, s) .internal ({ d with pc := .load }, s)
  | readyNotTaken (d : DriverState α) (s : Slot α) (hpc : d.pc = .branchReady)
      (hr : d.readyBit = false) :
      PollStep (d, s) (.visible .retry) ({ d with pc := .poll }, s)
  | loadData (d : DriverState α) {s s' : Slot α} {r : Option (ℕ × α)} (hpc : d.pc = .load)
      (h : RegisterStep s (.read r) s') :
      PollStep (d, s) (.visible (.read r)) ({ d with pc := .branchData, data := r }, s')
  | dataPresent (d : DriverState α) (s : Slot α) (n : ℕ) (v : α) (hpc : d.pc = .branchData)
      (hd : d.data = some (n, v)) :
      PollStep (d, s) .internal ({ d with pc := .emit }, s)
  | dataAbsent (d : DriverState α) (s : Slot α) (hpc : d.pc = .branchData)
      (hd : d.data = none) :
      PollStep (d, s) (.visible .retry) ({ d with pc := .poll }, s)
  | emit (d : DriverState α) (s : Slot α) (n : ℕ) (v : α) (hpc : d.pc = .emit)
      (hd : d.data = some (n, v)) :
      PollStep (d, s) (.visible (.deliver n v)) ({ d with pc := .record }, s)
  | record (d : DriverState α) (s : Slot α) (hpc : d.pc = .record) :
      PollStep (d, s) .internal ({ d with pc := .poll, cache := d.data }, s)

/-- The polling driver closed system as a `Cslib.LTS`. -/
def pollDriverLTS (α : Type u) : Cslib.LTS (DriverState α × Slot α) (StepLabel α) where
  Tr := PollStep

/-- Faulty variant: on an empty data load it emits the cached sample, if any, instead of
retrying; every other `PollStep` (environment steps included) is kept. -/
inductive StaleCacheStep {α : Type u} :
    DriverState α × Slot α → StepLabel α → DriverState α × Slot α → Prop where
  | base {x x' : DriverState α × Slot α} {l : StepLabel α} (h : PollStep x l x')
      (hne : ¬ (x.1.pc = .branchData ∧ x.1.data = none ∧ l = .visible .retry)) :
      StaleCacheStep x l x'
  | emitCached (d : DriverState α) (s : Slot α) (n : ℕ) (v : α) (hpc : d.pc = .branchData)
      (hd : d.data = none) (hc : d.cache = some (n, v)) :
      StaleCacheStep (d, s) (.visible (.deliver n v)) ({ d with pc := .poll }, s)
  | retryNoCache (d : DriverState α) (s : Slot α) (hpc : d.pc = .branchData)
      (hd : d.data = none) (hc : d.cache = none) :
      StaleCacheStep (d, s) (.visible .retry) ({ d with pc := .poll }, s)

/-- The faulty stale-cache driver as a `Cslib.LTS`. -/
def staleCacheDriverLTS (α : Type u) : Cslib.LTS (DriverState α × Slot α) (StepLabel α) where
  Tr := StaleCacheStep

/-! ### The refinement relation -/

/-- Protocol phase represented by a driver state. -/
def abstractPhase {α : Type u} (d : DriverState α) : Phase α :=
  match d.pc with
  | .poll => .idle
  | .branchReady => .polled d.readyBit
  | .load => .polled true
  | .branchData => .fetched d.data
  | .emit => .fetched d.data
  | .record => .idle

/-- The refinement relation: same register slot, abstracted driver phase. -/
def refinement {α : Type u} (x : DriverState α × Slot α) (y : Phase α × Slot α) : Prop :=
  y = (abstractPhase x.1, x.2)

/-! ### Erasure of the saturated specification -/

/-- The specification has no internal steps, so its `τ`-closure is the identity. -/
private theorem protocolLTS_τSTr_eq {α : Type u} {y y' : Phase α × Slot α}
    (hy : (protocolLTS α).τSTr y y') : y = y' := by
  induction hy with
  | refl => rfl
  | tail _ hst _ =>
      obtain ⟨μ, hμ, -⟩ := hst
      cases hμ

/-- A saturated specification step is either a stutter on `τ` or one visible protocol step. -/
private theorem protocolLTS_saturate_tr {α : Type u} {y y' : Phase α × Slot α}
    {l : StepLabel α} (hy : (protocolLTS α).saturate.Tr y l y') :
    (l = .internal ∧ y = y') ∨ ∃ μ, l = .visible μ ∧ (driverLTS α).Tr y μ y' := by
  change (protocolLTS α).STr y l y' at hy
  cases hy with
  | refl => exact Or.inl ⟨rfl, rfl⟩
  | tr h1 h2 h3 =>
      obtain ⟨μ, rfl, h2⟩ := h2
      obtain rfl := protocolLTS_τSTr_eq h1
      obtain rfl := protocolLTS_τSTr_eq h3
      exact Or.inr ⟨μ, rfl, h2⟩

/-- A saturated specification trace erases to a protocol trace between the same states. -/
private theorem driverLTS_mtr_of_saturate_mtr {α : Type u} {y y' : Phase α × Slot α}
    {ms : List (StepLabel α)} (hy : (protocolLTS α).saturate.MTr y ms y') :
    (driverLTS α).MTr y (visibleLabels ms) y' := by
  induction hy with
  | refl => exact .refl
  | stepL h1 _ ih =>
      rcases protocolLTS_saturate_tr h1 with ⟨rfl, rfl⟩ | ⟨μ, rfl, h2⟩
      · exact ih
      · exact .stepL h2 ih

/-! ### Simulation and its trace consequences -/

/-- The initial states are related. -/
theorem refinement_initial {α : Type u} :
    refinement ((initialDriver, none) : DriverState α × Slot α) (.idle, none) := by
  rfl

/-- **Stuttering simulation.** The refinement relation is a simulation from the polling
driver into the saturated protocol: visible driver steps are matched by the same protocol step,
internal driver steps by no protocol step. -/
theorem isSimulation_refinement {α : Type u} :
    Cslib.LTS.IsSimulation (pollDriverLTS α) (protocolLTS α).saturate refinement := by
  have vis : ∀ {y y' : Phase α × Slot α} {μ : DriverLabel α}, (driverLTS α).Tr y μ y' →
      (protocolLTS α).saturate.Tr y (.visible μ) y' := fun h =>
    Cslib.LTS.STr.tr Relation.ReflTransGen.refl ⟨_, rfl, h⟩ Relation.ReflTransGen.refl
  have tau : ∀ {y : Phase α × Slot α}, (protocolLTS α).saturate.Tr y .internal y :=
    fun {_} => Cslib.LTS.STr.refl
  rintro ⟨d, s⟩ y hr l x' htr
  change y = _ at hr
  subst hr
  refine ⟨(abstractPhase x'.1, x'.2), ?_, rfl⟩
  change PollStep (d, s) l x' at htr
  cases htr with
  | env d h => exact vis (DriverStep.env _ h)
  | loadReady d s hpc =>
      simp only [abstractPhase, hpc]
      exact vis (DriverStep.poll s)
  | readyTaken d s hpc hr =>
      simp only [abstractPhase, hpc, hr]
      exact tau
  | readyNotTaken d s hpc hr =>
      simp only [abstractPhase, hpc, hr]
      exact vis (DriverStep.retryNotReady s)
  | loadData d hpc h =>
      simp only [abstractPhase, hpc]
      exact vis (DriverStep.read h)
  | dataPresent d s n v hpc hd =>
      simp only [abstractPhase, hpc]
      exact tau
  | dataAbsent d s hpc hd =>
      simp only [abstractPhase, hpc, hd]
      exact vis (DriverStep.retryEmpty s)
  | emit d s n v hpc hd =>
      simp only [abstractPhase, hpc, hd]
      exact vis (DriverStep.deliver n v s)
  | record d s hpc =>
      simp only [abstractPhase, hpc]
      exact tau

/-- The polling driver is similar to the protocol from the initial states. -/
theorem similarity_initial {α : Type u} :
    Cslib.LTS.Similarity (pollDriverLTS α) (protocolLTS α).saturate
      ((initialDriver, none) : DriverState α × Slot α) (.idle, none) := by
  exact ⟨refinement, refinement_initial, isSimulation_refinement⟩

/-- **Trace erasure.** Every finite driver trace from the initial state erases, by dropping its
internal steps, to a protocol trace from the idle empty state ending in the abstracted state. -/
theorem driverLTS_mtr_visibleLabels {α : Type u} (ls : List (StepLabel α))
    (x : DriverState α × Slot α) (h : (pollDriverLTS α).MTr (initialDriver, none) ls x) :
    (driverLTS α).MTr (.idle, none) (visibleLabels ls) (abstractPhase x.1, x.2) := by
  obtain ⟨y', hy', hr'⟩ := isSimulation_refinement.sim_trace refinement_initial ls x h
  change y' = _ at hr'
  subst hr'
  exact driverLTS_mtr_of_saturate_mtr hy'

/-- A delivery in a driver trace is fed either by an earlier driver read of the delivered
sample or by the data already loaded in the starting state. -/
private theorem exists_read_of_emit_aux {α : Type u} (y z : DriverState α × Slot α)
    (ms : List (StepLabel α)) (hy : (pollDriverLTS α).MTr y ms z) :
    ∀ (i n : ℕ) (v : α), ms[i]? = some (.visible (.deliver n v)) →
      (∃ j, j < i ∧ ms[j]? = some (.visible (.read (some (n, v))))) ∨
        y.1.data = some (n, v) := by
  induction hy with
  | refl => intro i n v hi; simp at hi
  | @stepL x1 μ x2 μs x3 htr _ ih =>
      intro i n v hi
      cases i with
      | zero =>
          rw [List.getElem?_cons_zero] at hi
          have hμ : μ = .visible (.deliver n v) := by simpa using hi
          subst hμ
          change PollStep x1 _ x2 at htr
          cases htr with
          | emit d s n' v' hpc hd => exact Or.inr hd
      | succ i' =>
          rw [List.getElem?_cons_succ] at hi
          rcases ih i' n v hi with ⟨j, hj, hread⟩ | hmid
          · exact Or.inl ⟨j + 1, by omega, by rwa [List.getElem?_cons_succ]⟩
          · change PollStep x1 μ x2 at htr
            cases htr with
            | @loadData d s s' r hpc hr =>
                have e : r = some (n, v) := hmid
                subst e
                exact Or.inl ⟨0, by omega, by simp⟩
            | _ => exact Or.inr hmid

/-- A successful driver read in a driver trace is preceded by the matching publication with no
other publication in between, or the sample was already in the starting slot. -/
private theorem exists_publish_of_read_aux {α : Type u} (y z : DriverState α × Slot α)
    (ms : List (StepLabel α)) (hy : (pollDriverLTS α).MTr y ms z) :
    ∀ (j n : ℕ) (v : α), ms[j]? = some (.visible (.read (some (n, v)))) →
      (∃ k, k < j ∧ ms[k]? = some (.visible (.env (.publish n v))) ∧
        ∀ l m w, k < l → l < j → ms[l]? ≠ some (.visible (.env (.publish m w)))) ∨
      (y.2 = some (n, v) ∧ ∀ l m w, l < j → ms[l]? ≠ some (.visible (.env (.publish m w)))) := by
  induction hy with
  | refl => intro j n v hj; simp at hj
  | @stepL x1 μ x2 μs x3 htr _ ih =>
      intro j n v hj
      cases j with
      | zero =>
          rw [List.getElem?_cons_zero] at hj
          have hμ : μ = .visible (.read (some (n, v))) := by simpa using hj
          subst hμ
          change PollStep x1 _ x2 at htr
          cases htr with
          | loadData d hpc hr =>
              cases hr
              right
              refine ⟨rfl, ?_⟩
              intro l m w hl
              exact absurd hl (Nat.not_lt_zero _)
      | succ j' =>
          rw [List.getElem?_cons_succ] at hj
          rcases ih j' n v hj with ⟨k, hk, hpub, hnopub⟩ | ⟨hmid, hnopub⟩
          · left
            refine ⟨k + 1, by omega, ?_, ?_⟩
            · rwa [List.getElem?_cons_succ]
            · intro l m w hl1 hl2 hcon
              cases l with
              | zero => exact absurd hl1 (Nat.not_lt_zero _)
              | succ l' =>
                  rw [List.getElem?_cons_succ] at hcon
                  exact hnopub l' m w (by omega) (by omega) hcon
          · have key : (∃ m w, μ = .visible (.env (.publish m w)) ∧ x2.2 = some (m, w)) ∨
                x2.2 = none ∨ (x2.2 = x1.2 ∧ ∀ m w, μ ≠ .visible (.env (.publish m w))) := by
              change PollStep x1 μ x2 at htr
              cases htr with
              | env d hr =>
                  cases hr with
                  | publish m w => exact Or.inl ⟨m, w, rfl, rfl⟩
                  | read => exact Or.inr (Or.inl rfl)
              | loadData d hpc hr =>
                  cases hr
                  exact Or.inr (Or.inl rfl)
              | _ => exact Or.inr (Or.inr ⟨rfl, by intro m w hc; cases hc⟩)
            rcases key with ⟨m, w, rfl, h2⟩ | h2 | ⟨h2, hne⟩
            · rw [hmid] at h2
              simp only [Option.some.injEq, Prod.mk.injEq] at h2
              obtain ⟨rfl, rfl⟩ := h2
              left
              refine ⟨0, by omega, by simp, ?_⟩
              intro l m' w' hl1 hl2 hcon
              cases l with
              | zero => exact absurd hl1 (lt_irrefl _)
              | succ l' =>
                  rw [List.getElem?_cons_succ] at hcon
                  exact hnopub l' m' w' (by omega) hcon
            · rw [hmid] at h2
              cases h2
            · right
              refine ⟨h2.symm.trans hmid, ?_⟩
              intro l m w hl hcon
              cases l with
              | zero =>
                  rw [List.getElem?_cons_zero] at hcon
                  exact hne m w (by simpa using hcon)
              | succ l' =>
                  rw [List.getElem?_cons_succ] at hcon
                  exact hnopub l' m w (by omega) hcon

/-- **Sample IDs and values are preserved.** In every finite driver trace from the initial
state, every emitted sample `(n, v)` is the `some (n, v)` result of an earlier driver read, and
that read is preceded by the publication `publish n v` with no other publication in between. -/
theorem exists_publish_of_emit {α : Type u} (ls : List (StepLabel α))
    (x : DriverState α × Slot α) (h : (pollDriverLTS α).MTr (initialDriver, none) ls x)
    (i n : ℕ) (v : α) (hi : ls[i]? = some (.visible (.deliver n v))) :
    ∃ j k, k < j ∧ j < i ∧ ls[j]? = some (.visible (.read (some (n, v)))) ∧
      ls[k]? = some (.visible (.env (.publish n v))) ∧
      ∀ l m w, k < l → l < j → ls[l]? ≠ some (.visible (.env (.publish m w))) := by
  rcases exists_read_of_emit_aux _ _ ls h i n v hi with ⟨j, hj, hread⟩ | hmid
  · rcases exists_publish_of_read_aux _ _ ls h j n v hread with
      ⟨k, hk, hpub, hnopub⟩ | ⟨hmid, -⟩
    · exact ⟨j, k, hk, hj, hread, hpub, hnopub⟩
    · simp at hmid
  · simp [initialDriver] at hmid

/-- **Polling driver correctness (headline).** The initial states are related by the
refinement relation; the refinement relation is a stuttering simulation from the polling driver
into the saturated sample-ready protocol; and every finite driver trace from the initial state
(1) erases to a protocol trace ending in the abstracted state, (2) performs register operations
forming an L1 register trace from the empty slot, and (3) emits only samples `(n, v)` returned
as `some (n, v)` by an earlier driver read that is preceded by `publish n v` with no other
publication in between. -/
theorem pollDriver_correct {α : Type u} :
    refinement ((initialDriver, none) : DriverState α × Slot α) (.idle, none) ∧
      Cslib.LTS.IsSimulation (pollDriverLTS α) (protocolLTS α).saturate refinement ∧
      ∀ (ls : List (StepLabel α)) (x : DriverState α × Slot α),
        (pollDriverLTS α).MTr (initialDriver, none) ls x →
          (driverLTS α).MTr (.idle, none) (visibleLabels ls) (abstractPhase x.1, x.2) ∧
          (registerLTS α).MTr none ((visibleLabels ls).filterMap registerLabel?) x.2 ∧
          ∀ (i n : ℕ) (v : α), ls[i]? = some (.visible (.deliver n v)) →
            ∃ j k, k < j ∧ j < i ∧ ls[j]? = some (.visible (.read (some (n, v)))) ∧
              ls[k]? = some (.visible (.env (.publish n v))) ∧
              ∀ l m w, k < l → l < j → ls[l]? ≠ some (.visible (.env (.publish m w))) := by
  refine ⟨refinement_initial, isSimulation_refinement, fun ls x h => ⟨?_, ?_, ?_⟩⟩
  · exact driverLTS_mtr_visibleLabels ls x h
  · exact registerLTS_mtr_filterMap_of_driverLTS_mtr _ _ _ _ _
      (driverLTS_mtr_visibleLabels ls x h)
  · exact fun i n v hi => exists_publish_of_emit ls x h i n v hi

/-! ### Validation -/

/-- A three-iteration run: Ready false and retry; then a publication, Ready true, another reader
clears the slot, the driver's read is empty and it retries; then a publication, Ready true, a
successful read and an emit. -/
def threePollRun {α : Type u} (a c : α) : List (StepLabel α) :=
  [.visible (.poll false), .visible .retry,
    .visible (.env (.publish 0 a)), .visible (.poll true), .internal,
    .visible (.env (.read (some (0, a)))), .visible (.read none), .visible .retry,
    .visible (.env (.publish 1 c)), .visible (.poll true), .internal,
    .visible (.read (some (1, c))), .internal, .visible (.deliver 1 c), .internal]

/-- **Two or more poll iterations, an empty read and a successful read.** The three-iteration
run is a driver trace; its erasure is a protocol trace ending idle and empty, and the only
sample delivered is the one with ID `1`. -/
theorem threePollRun_valid {α : Type u} (a c : α) :
    (pollDriverLTS α).MTr (initialDriver, none) (threePollRun a c)
        (⟨.poll, true, some (1, c), some (1, c)⟩, none) ∧
      (driverLTS α).MTr (.idle, none) (visibleLabels (threePollRun a c)) (.idle, none) ∧
      deliveredIds (visibleLabels (threePollRun a c)) = [1] := by
  refine ⟨?_, ?_, rfl⟩
  · exact
      .stepL (PollStep.loadReady _ _ rfl) <|
      .stepL (PollStep.readyNotTaken _ _ rfl rfl) <|
      .stepL (PollStep.env _ (RegisterStep.publish _ 0 a)) <|
      .stepL (PollStep.loadReady _ _ rfl) <|
      .stepL (PollStep.readyTaken _ _ rfl rfl) <|
      .stepL (PollStep.env _ (RegisterStep.read _)) <|
      .stepL (PollStep.loadData _ rfl (RegisterStep.read _)) <|
      .stepL (PollStep.dataAbsent _ _ rfl rfl) <|
      .stepL (PollStep.env _ (RegisterStep.publish _ 1 c)) <|
      .stepL (PollStep.loadReady _ _ rfl) <|
      .stepL (PollStep.readyTaken _ _ rfl rfl) <|
      .stepL (PollStep.loadData _ rfl (RegisterStep.read _)) <|
      .stepL (PollStep.dataPresent _ _ 1 c rfl rfl) <|
      .stepL (PollStep.emit _ _ 1 c rfl rfl) <|
      .stepL (PollStep.record _ _ rfl) .refl
  · exact
      .stepL (DriverStep.poll _) <|
      .stepL (DriverStep.retryNotReady _) <|
      .stepL (DriverStep.env _ (RegisterStep.publish _ 0 a)) <|
      .stepL (DriverStep.poll _) <|
      .stepL (DriverStep.env _ (RegisterStep.read _)) <|
      .stepL (DriverStep.read (RegisterStep.read _)) <|
      .stepL (DriverStep.retryEmpty _) <|
      .stepL (DriverStep.env _ (RegisterStep.publish _ 1 c)) <|
      .stepL (DriverStep.poll _) <|
      .stepL (DriverStep.read (RegisterStep.read _)) <|
      .stepL (DriverStep.deliver _ _ _) .refl

/-- A stale-cache run: deliver `(0, a)`, then a second round whose slot another reader clears
between the Ready poll and the driver's read; the faulty driver emits the cached `(0, a)`. -/
def staleCacheRun {α : Type u} (a : α) : List (StepLabel α) :=
  [.visible (.env (.publish 0 a)), .visible (.poll true), .internal,
    .visible (.read (some (0, a))), .internal, .visible (.deliver 0 a), .internal,
    .visible (.env (.publish 1 a)), .visible (.poll true), .internal,
    .visible (.env (.read (some (1, a)))), .visible (.read none), .visible (.deliver 0 a)]

/-- **A driver that emits a cached value on `none` fails the simulation (trace form).** The
stale-cache run is a trace of the faulty driver, and its erasure is not a protocol trace. -/
theorem staleCacheRun_not_protocol_trace {α : Type u} (a : α) :
    (∃ x, (staleCacheDriverLTS α).MTr (initialDriver, none) (staleCacheRun a) x) ∧
      ¬ ∃ y, (driverLTS α).MTr (.idle, none) (visibleLabels (staleCacheRun a)) y := by
  refine ⟨⟨(⟨.poll, true, none, some (0, a)⟩, none), ?_⟩, ?_⟩
  · refine .stepL (StaleCacheStep.base (PollStep.env _ (RegisterStep.publish _ 0 a)) ?_) ?_
    · simp [initialDriver]
    refine .stepL (StaleCacheStep.base (PollStep.loadReady _ _ rfl) ?_) ?_
    · simp [initialDriver]
    refine .stepL (StaleCacheStep.base (PollStep.readyTaken _ _ rfl rfl) ?_) ?_
    · simp
    refine .stepL (StaleCacheStep.base (PollStep.loadData _ rfl (RegisterStep.read _)) ?_) ?_
    · simp
    refine .stepL (StaleCacheStep.base (PollStep.dataPresent _ _ 0 a rfl rfl) ?_) ?_
    · simp
    refine .stepL (StaleCacheStep.base (PollStep.emit _ _ 0 a rfl rfl) ?_) ?_
    · simp
    refine .stepL (StaleCacheStep.base (PollStep.record _ _ rfl) ?_) ?_
    · simp
    refine .stepL (StaleCacheStep.base (PollStep.env _ (RegisterStep.publish _ 1 a)) ?_) ?_
    · simp
    refine .stepL (StaleCacheStep.base (PollStep.loadReady _ _ rfl) ?_) ?_
    · simp
    refine .stepL (StaleCacheStep.base (PollStep.readyTaken _ _ rfl rfl) ?_) ?_
    · simp
    refine .stepL (StaleCacheStep.base (PollStep.env _ (RegisterStep.read _)) ?_) ?_
    · simp
    refine .stepL (StaleCacheStep.base (PollStep.loadData _ rfl (RegisterStep.read _)) ?_) ?_
    · simp
    exact .stepL (StaleCacheStep.emitCached _ _ 0 a rfl rfl rfl) .refl
  · rintro ⟨y, h⟩
    change (driverLTS α).MTr (.idle, none)
      [.env (.publish 0 a), .poll true, .read (some (0, a)), .deliver 0 a,
        .env (.publish 1 a), .poll true, .env (.read (some (1, a))), .read none,
        .deliver 0 a] y at h
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
    cases r4 with | stepL h5 r5 =>
    cases h5 with | env _ h5 =>
    cases h5
    cases r5 with | stepL h6 r6 =>
    cases h6
    cases r6 with | stepL h7 r7 =>
    cases h7 with | env _ h7 =>
    cases h7
    cases r7 with | stepL h8 r8 =>
    cases h8 with | read h8 =>
    cases h8
    cases r8 with | stepL h9 r9 =>
    cases h9

/-- **A driver that emits a cached value on `none` fails the simulation.** For any inhabited
value type, the faulty driver is not similar to the saturated protocol from the initial
states: no simulation relation relates them. -/
theorem not_similarity_staleCacheDriver {α : Type u} (a : α) :
    ¬ Cslib.LTS.Similarity (staleCacheDriverLTS α) (protocolLTS α).saturate
      ((initialDriver, none) : DriverState α × Slot α) (.idle, none) := by
  rintro ⟨r, hr, hsim⟩
  obtain ⟨⟨x, hx⟩, hnot⟩ := staleCacheRun_not_protocol_trace a
  obtain ⟨y', hy', -⟩ := hsim.sim_trace hr _ x hx
  exact hnot ⟨y', driverLTS_mtr_of_saturate_mtr hy'⟩

end Cslib.Semantics.Peripheral.PollDriverSimulation
