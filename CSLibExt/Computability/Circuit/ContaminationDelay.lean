/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Computability.Circuit.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.WithBot

/-!
# Contamination delays and hold-time certificates

A hold check asks how *soon* a register's data input can change after a clock edge, so it needs
the minimum delay through a circuit rather than the maximum. This file annotates a straight-line
circuit (`Cslib.Circuits.Circuit`) with one real contamination delay per gate, indexed by
`Fin c.size`, and computes earliest change times by min-plus propagation. Times live in
`WithTop ℝ` (seconds), with `⊤` meaning "never changes".

* `Line.earliest`: a gate can first change at its contamination delay plus the earliest change
  among the wires it reads, the minimum folded from `⊤`. A constant (zero-input) gate gets `⊤`,
  not a transition at its own delay. `Program.earliests`, `Program.wireEarliests` and
  `Circuit.outputEarliests` propagate the recursion through a program and to the outputs.
* `StableBefore s τ`: after the clock edge at time `0`, the signal `s : ℝ → U` takes a single
  value at every time before `τ`, that is on `[0, τ)`. Changes before the edge are unconstrained,
  so a signal may carry the previous cycle's transitions.
* `Line.Causal`, `Program.Causal`: the gate-delay model after the edge. A gate's contamination
  delay is nonnegative, and if every wire it reads is stable on `[0, τ)`, its output is stable on
  `[0, cdelay + τ)`: no gate responds to a change sooner than its contamination delay. The model
  constrains only times from the edge on. A circuit still settling from the previous cycle can
  violate it, but it does not say that any signal was settled before the edge.
* `SettledBefore s δ`: before the edge, `s` already holds its value at the edge on `[-δ, 0]`.
  This is the pre-edge (setup) side of a capture, which a setup analysis would supply.
* `HoldMet s hold u`: a register clocked at time `0` sees its data input `s` unchanged from the
  edge until `hold + u`, the hold time plus the clock uncertainty.
* `CaptureMet s setup hold u`: `s` holds its value at the edge on all of
  `[-(setup + u), hold + u)`. The clock uncertainty widens both sides of the capture window.

The durations `δ`, `setup`, `hold`, `u` and the minimum clock-to-Q delay `tqMin` are elapsed
times, so they are nonnegative reals (`ℝ≥0`); a negative duration cannot be stated.

## Main results

* `Program.stableBefore_wireEarliests`: under the causal model, if every input is stable
  before its stated earliest change, every wire is stable before its computed earliest change.
* `Program.le_wireEarliests`: with nonnegative delays, no wire changes before the inputs do.
* `Circuit.holdMet_of_le_outputEarliests`: if the launching register's outputs cannot change
  after the edge before its minimum clock-to-Q delay `tqMin`, then
  `hold + u ≤ tqMin + earliest_path` certifies hold at the receiving register, where
  `earliest_path` is the output's earliest change with every input changing at time `0`.
* `Circuit.captureMet_of_le_outputEarliests`: adding the explicit premise that the receiving
  register's data input settled `setup + u` seconds before the edge, the same certificate gives
  a single value on `[-(setup + u), hold + u)`.

The min-delay model is separate from any max-delay (setup) analysis: nothing here uses arrival
times or depth. The hold certificate constrains only the window after the edge and needs no
pre-edge premise; settling before the edge is the explicit premise `SettledBefore` of the
capture certificate. Delays are premises of the model; setup timing, clock-domain crossing and
glitch freedom are out of scope.
-/

@[expose] public section

namespace Cslib.Circuits

open scoped NNReal

universe v

/-! ### Signals and the causal gate-delay model -/

/-- From the clock edge at time `0`, a signal holds a single value at every time
strictly before `τ`, that is on `[0, τ)`; with `τ = ⊤` it never changes after the
edge. Times before the edge are unconstrained. -/
def StableBefore {U : Type*} (s : ℝ → U) (τ : WithTop ℝ) : Prop :=
  ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → 0 ≤ t₂ → (t₁ : WithTop ℝ) < τ → (t₂ : WithTop ℝ) < τ → s t₁ = s t₂

/-- **Causal gate-delay model for one gate, after the clock edge.** The gate
reading `line` has nonnegative contamination delay `cdelay` and output signal
`out`: whenever every wire it reads is stable on `[0, τ)`, its output is stable
on `[0, cdelay + τ)`. A gate with no inputs is therefore constant after the
edge. Only times from the edge at `0` on are constrained: this does not say the
output had settled before the edge (see `SettledBefore`). -/
def Line.Causal {σ : Signature.{v}} {inputCount gateCount : Nat} {U : Type*}
    (line : Line σ inputCount gateCount) (wireSignal : Wire inputCount gateCount → ℝ → U)
    (cdelay : ℝ) (out : ℝ → U) : Prop :=
  0 ≤ cdelay ∧ ∀ τ : WithTop ℝ, (∀ k, StableBefore (wireSignal (line.wires k)) τ) →
    StableBefore out ((cdelay : WithTop ℝ) + τ)

/-- **Causal gate-delay model for a program.** Every gate obeys `Line.Causal`
for its contamination delay, reading the signals of the inputs and of the
earlier gates. -/
def Program.Causal {σ : Signature.{v}} {inputCount : Nat} {U : Type*} :
    {gateCount : Nat} → Program σ inputCount gateCount → (Fin gateCount → ℝ) →
      (Fin inputCount → ℝ → U) → (Fin gateCount → ℝ → U) → Prop
  | _, .empty, _, _, _ => True
  | _, .gate p line, cdelay, inputSignal, gateSignal =>
      p.Causal (fun j => cdelay j.castSucc) inputSignal (fun j => gateSignal j.castSucc) ∧
        line.Causal (Wire.elim inputSignal (fun j => gateSignal j.castSucc))
          (cdelay (Fin.last _)) (gateSignal (Fin.last _))

/-- **Hold check at the receiving register.** The register is clocked at time
`0`; its data input `s` must not change from the edge until the hold time `hold`
plus the clock uncertainty `u`, that is on `[0, hold + u)`. -/
def HoldMet {U : Type*} (s : ℝ → U) (hold u : ℝ≥0) : Prop :=
  StableBefore s (((hold : ℝ) + u : ℝ) : WithTop ℝ)

/-- **Settled before the edge.** The signal `s` already holds its value at the
clock edge at time `0` throughout the `δ` seconds before it, that is on
`[-δ, 0]`. -/
def SettledBefore {U : Type*} (s : ℝ → U) (δ : ℝ≥0) : Prop :=
  ∀ t : ℝ, -(δ : ℝ) ≤ t → t ≤ 0 → s t = s 0

/-- **Capture check at the receiving register.** The register is clocked at time
`0`; its data input `s` holds its value at the edge from the setup time `setup`
plus the clock uncertainty `u` before the edge until the hold time `hold` plus
`u` after it, that is on `[-(setup + u), hold + u)`. -/
def CaptureMet {U : Type*} (s : ℝ → U) (setup hold u : ℝ≥0) : Prop :=
  ∀ t : ℝ, -((setup : ℝ) + u) ≤ t → (t : WithTop ℝ) < (((hold : ℝ) + u : ℝ) : WithTop ℝ) →
    s t = s 0

/-! ### Earliest change: min-plus propagation of contamination delays -/

/-- The earliest time a line's output may change: the contamination delay plus
the earliest change among the wires it reads, the minimum folded from `⊤`. A
constant (zero-input) gate never changes. -/
def Line.earliest {σ : Signature.{v}} {inputCount gateCount : Nat}
    (line : Line σ inputCount gateCount)
    (wireEarliest : Wire inputCount gateCount → WithTop ℝ) (cdelay : ℝ) : WithTop ℝ :=
  (cdelay : WithTop ℝ) + Fin.foldl (σ.Arity line.op)
    (fun t k => min t (wireEarliest (line.wires k))) ⊤

/-- The earliest change of every gate of a program, for a contamination delay
on every gate and an earliest change on every original input. -/
def Program.earliests {σ : Signature.{v}} {inputCount : Nat} :
    {gateCount : Nat} → Program σ inputCount gateCount →
      (Fin gateCount → ℝ) → (Fin inputCount → WithTop ℝ) → Fin gateCount → WithTop ℝ
  | _, .empty, _, _ => Fin.elim0
  | _, .gate p line, cdelay, inputEarliest =>
      let prior := p.earliests (fun j => cdelay j.castSucc) inputEarliest
      Fin.lastCases
        (line.earliest (Wire.elim inputEarliest prior) (cdelay (Fin.last _))) prior

/-- The earliest change of every input or gate wire of a program. -/
def Program.wireEarliests {σ : Signature.{v}} {inputCount gateCount : Nat}
    (p : Program σ inputCount gateCount) (cdelay : Fin gateCount → ℝ)
    (inputEarliest : Fin inputCount → WithTop ℝ) : Wire inputCount gateCount → WithTop ℝ :=
  Wire.elim inputEarliest (p.earliests cdelay inputEarliest)

/-- The earliest change of every designated output of a circuit. -/
def Circuit.outputEarliests {σ : Signature.{v}} {inputCount outputCount : Nat}
    (c : Circuit σ inputCount outputCount) (cdelay : Fin c.size → ℝ)
    (inputEarliest : Fin inputCount → WithTop ℝ) : Fin outputCount → WithTop ℝ :=
  c.program.wireEarliests cdelay inputEarliest ∘ c.outputs

/-! ### The minimum fold -/

/-- A lower bound of the start value and of every term bounds the minimum fold. -/
private theorem le_foldl_min (n : Nat) (g : Fin n → WithTop ℝ) (x t : WithTop ℝ)
    (hx : t ≤ x) (hg : ∀ j, t ≤ g j) : t ≤ Fin.foldl n (fun t k => min t (g k)) x := by
  induction n with
  | zero => simpa [Fin.foldl_zero] using hx
  | succ n ih =>
    rw [Fin.foldl_succ_last]
    exact le_min (ih (fun k => g k.castSucc) (fun j => hg _)) (hg _)

/-- The minimum fold is at most every term. -/
private theorem foldl_min_le (n : Nat) (g : Fin n → WithTop ℝ) (x : WithTop ℝ) (j : Fin n) :
    Fin.foldl n (fun t k => min t (g k)) x ≤ g j := by
  induction n with
  | zero => exact j.elim0
  | succ n ih =>
    rw [Fin.foldl_succ_last]
    induction j using Fin.lastCases with
    | last => exact min_le_right _ _
    | cast j => exact (min_le_left _ _).trans (ih (fun k => g k.castSucc) j)

/-- Shifting the start value and every term by `a` shifts the minimum fold by `a`. -/
private theorem foldl_min_add (a : ℝ) (n : Nat) (g : Fin n → WithTop ℝ) (x : WithTop ℝ) :
    Fin.foldl n (fun t k => min t ((a : WithTop ℝ) + g k)) ((a : WithTop ℝ) + x)
      = (a : WithTop ℝ) + Fin.foldl n (fun t k => min t (g k)) x := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    rw [Fin.foldl_succ_last, Fin.foldl_succ_last, ih (fun k => g k.castSucc), min_add_add_left]

/-- Stability before `τ` implies stability before any earlier time. -/
private theorem StableBefore.mono {U : Type*} {s : ℝ → U} {τ τ' : WithTop ℝ} (hle : τ' ≤ τ)
    (h : StableBefore s τ) : StableBefore s τ' := fun t₁ t₂ h₀₁ h₀₂ h₁ h₂ =>
  h t₁ t₂ h₀₁ h₀₂ (lt_of_lt_of_le h₁ hle) (lt_of_lt_of_le h₂ hle)

/-! ### Line earliest: no-transition constants and min over fan-in -/

/-- **No-transition constants.** A gate with no inputs never changes. -/
theorem Line.earliest_of_arity_eq_zero {σ : Signature.{v}} {inputCount gateCount : Nat}
    (line : Line σ inputCount gateCount) (wireEarliest : Wire inputCount gateCount → WithTop ℝ)
    (cdelay : ℝ) (h : σ.Arity line.op = 0) :
    line.earliest wireEarliest cdelay = ⊤ := by
  have hfold : Fin.foldl (σ.Arity line.op)
      (fun t k => min t (wireEarliest (line.wires k))) ⊤ = ⊤ :=
    le_antisymm le_top (le_foldl_min _ _ _ _ le_rfl (fun j => absurd j.2 (by omega)))
  unfold Line.earliest
  rw [hfold]
  exact WithTop.add_top _

/-- A gate's earliest change is at most its delay plus any fan-in's earliest
change. -/
theorem Line.earliest_le_add_wireEarliest {σ : Signature.{v}} {inputCount gateCount : Nat}
    (line : Line σ inputCount gateCount) (wireEarliest : Wire inputCount gateCount → WithTop ℝ)
    (cdelay : ℝ) (j : Fin (σ.Arity line.op)) :
    line.earliest wireEarliest cdelay ≤ (cdelay : WithTop ℝ) + wireEarliest (line.wires j) := by
  unfold Line.earliest
  gcongr
  exact foldl_min_le _ _ _ j

/-- The fold is the greatest lower bound from `⊤`: any `t` below every fan-in's
earliest change gives `cdelay + t ≤` the gate's earliest change. -/
theorem Line.add_le_earliest_of_forall_le {σ : Signature.{v}} {inputCount gateCount : Nat}
    (line : Line σ inputCount gateCount) (wireEarliest : Wire inputCount gateCount → WithTop ℝ)
    (cdelay : ℝ) (t : WithTop ℝ) (h : ∀ j, t ≤ wireEarliest (line.wires j)) :
    (cdelay : WithTop ℝ) + t ≤ line.earliest wireEarliest cdelay := by
  unfold Line.earliest
  gcongr
  exact le_foldl_min _ _ _ _ le_top h

/-! ### Program earliest: structural equations -/

/-- The newest gate's earliest change is its line's earliest change over the
earlier wires. -/
theorem Program.earliests_gate_last {σ : Signature.{v}} {inputCount gateCount : Nat}
    (p : Program σ inputCount gateCount) (line : Line σ inputCount gateCount)
    (cdelay : Fin (gateCount + 1) → ℝ) (inputEarliest : Fin inputCount → WithTop ℝ) :
    (p.gate line).earliests cdelay inputEarliest (Fin.last gateCount)
      = line.earliest (p.wireEarliests (fun j => cdelay j.castSucc) inputEarliest)
          (cdelay (Fin.last gateCount)) := by
  simp [Program.earliests, Program.wireEarliests]

/-- Adding a gate does not change earlier gates' earliest changes. -/
theorem Program.earliests_gate_castSucc {σ : Signature.{v}} {inputCount gateCount : Nat}
    (p : Program σ inputCount gateCount) (line : Line σ inputCount gateCount)
    (cdelay : Fin (gateCount + 1) → ℝ) (inputEarliest : Fin inputCount → WithTop ℝ)
    (j : Fin gateCount) :
    (p.gate line).earliests cdelay inputEarliest j.castSucc
      = p.earliests (fun k => cdelay k.castSucc) inputEarliest j := by
  simp [Program.earliests]

/-- An input wire's earliest change is its stated earliest change. -/
theorem Program.wireEarliests_input {σ : Signature.{v}} {inputCount gateCount : Nat}
    (p : Program σ inputCount gateCount) (cdelay : Fin gateCount → ℝ)
    (inputEarliest : Fin inputCount → WithTop ℝ) (i : Fin inputCount) :
    p.wireEarliests cdelay inputEarliest (.input i) = inputEarliest i := by
  rfl

/-! ### Time shift and the launch bound -/

/-- Delaying every input's earliest change by `a` delays every wire's by `a`
(a never-changing wire stays `⊤`). -/
theorem Program.wireEarliests_add {σ : Signature.{v}} {inputCount gateCount : Nat}
    (p : Program σ inputCount gateCount) (cdelay : Fin gateCount → ℝ)
    (inputEarliest : Fin inputCount → WithTop ℝ) (a : ℝ) (w : Wire inputCount gateCount) :
    p.wireEarliests cdelay (fun i => (a : WithTop ℝ) + inputEarliest i) w
      = (a : WithTop ℝ) + p.wireEarliests cdelay inputEarliest w := by
  induction p with
  | empty =>
    cases w with
    | input i => rfl
    | gate j => exact j.elim0
  | gate p line ih =>
    cases w with
    | input i => rfl
    | gate j =>
      induction j using Fin.lastCases with
      | last =>
        change (p.gate line).earliests cdelay _ (Fin.last _)
          = (a : WithTop ℝ) + (p.gate line).earliests cdelay inputEarliest (Fin.last _)
        rw [Program.earliests_gate_last, Program.earliests_gate_last]
        have hw : p.wireEarliests (fun j => cdelay j.castSucc)
              (fun i => (a : WithTop ℝ) + inputEarliest i)
            = fun w => (a : WithTop ℝ) + p.wireEarliests (fun j => cdelay j.castSucc)
              inputEarliest w := funext (ih _)
        rw [hw]
        unfold Line.earliest
        rw [← WithTop.add_top (a : WithTop ℝ), foldl_min_add, WithTop.add_top]
        rw [← add_assoc, ← add_assoc, add_comm (cdelay (Fin.last _) : WithTop ℝ)]
      | cast j =>
        change (p.gate line).earliests cdelay _ j.castSucc
          = (a : WithTop ℝ) + (p.gate line).earliests cdelay inputEarliest j.castSucc
        rw [Program.earliests_gate_castSucc, Program.earliests_gate_castSucc]
        exact ih _ (.gate j)

/-- The output form of `Program.wireEarliests_add`. -/
theorem Circuit.outputEarliests_add {σ : Signature.{v}} {inputCount outputCount : Nat}
    (c : Circuit σ inputCount outputCount) (cdelay : Fin c.size → ℝ)
    (inputEarliest : Fin inputCount → WithTop ℝ) (a : ℝ) (o : Fin outputCount) :
    c.outputEarliests cdelay (fun i => (a : WithTop ℝ) + inputEarliest i) o
      = (a : WithTop ℝ) + c.outputEarliests cdelay inputEarliest o :=
  c.program.wireEarliests_add cdelay inputEarliest a (c.outputs o)

/-- **No change before launch.** With nonnegative contamination delays and no
input changing before `a`, no wire changes before `a`. -/
theorem Program.le_wireEarliests {σ : Signature.{v}} {inputCount gateCount : Nat}
    (p : Program σ inputCount gateCount) (cdelay : Fin gateCount → ℝ)
    (inputEarliest : Fin inputCount → WithTop ℝ) (a : ℝ)
    (hcdelay : ∀ j, 0 ≤ cdelay j) (hinput : ∀ i, (a : WithTop ℝ) ≤ inputEarliest i)
    (w : Wire inputCount gateCount) :
    (a : WithTop ℝ) ≤ p.wireEarliests cdelay inputEarliest w := by
  induction p with
  | empty =>
    cases w with
    | input i => exact hinput i
    | gate j => exact j.elim0
  | gate p line ih =>
    cases w with
    | input i => exact hinput i
    | gate j =>
      induction j using Fin.lastCases with
      | last =>
        change (a : WithTop ℝ) ≤ (p.gate line).earliests cdelay inputEarliest (Fin.last _)
        rw [Program.earliests_gate_last]
        refine le_trans ?_ (line.add_le_earliest_of_forall_le _ _ (a : WithTop ℝ)
          (fun k => ih _ (fun j => hcdelay _) _))
        rw [← WithTop.coe_add, WithTop.coe_le_coe]
        exact le_add_of_nonneg_left (hcdelay (Fin.last _))
      | cast j =>
        change (a : WithTop ℝ) ≤ (p.gate line).earliests cdelay inputEarliest j.castSucc
        rw [Program.earliests_gate_castSucc]
        exact ih _ (fun k => hcdelay _) (.gate j)

/-! ### Soundness and the hold certificate -/

/-- **Soundness of min-plus propagation.** Under the causal gate-delay model,
if every input is stable before its stated earliest change, every wire is
stable before its computed earliest change. -/
theorem Program.stableBefore_wireEarliests {σ : Signature.{v}} {inputCount gateCount : Nat}
    {U : Type*} (p : Program σ inputCount gateCount) (cdelay : Fin gateCount → ℝ)
    (inputEarliest : Fin inputCount → WithTop ℝ)
    (inputSignal : Fin inputCount → ℝ → U) (gateSignal : Fin gateCount → ℝ → U)
    (hcausal : p.Causal cdelay inputSignal gateSignal)
    (hinput : ∀ i, StableBefore (inputSignal i) (inputEarliest i))
    (w : Wire inputCount gateCount) :
    StableBefore (Wire.elim inputSignal gateSignal w)
      (p.wireEarliests cdelay inputEarliest w) := by
  induction p with
  | empty =>
    cases w with
    | input i => exact hinput i
    | gate j => exact j.elim0
  | gate p line ih =>
    obtain ⟨hp, hl⟩ := hcausal
    cases w with
    | input i => exact hinput i
    | gate j =>
      induction j using Fin.lastCases with
      | last =>
        change StableBefore (gateSignal (Fin.last _))
          ((p.gate line).earliests cdelay inputEarliest (Fin.last _))
        rw [Program.earliests_gate_last]
        apply hl.2
        intro k
        refine StableBefore.mono ?_ (ih _ _ hp (line.wires k))
        have h := line.earliest_le_add_wireEarliest
          (p.wireEarliests (fun j => cdelay j.castSucc) inputEarliest) 0 k
        simpa [Line.earliest] using h
      | cast j =>
        change StableBefore (gateSignal j.castSucc)
          ((p.gate line).earliests cdelay inputEarliest j.castSucc)
        rw [Program.earliests_gate_castSucc]
        exact ih _ _ hp (.gate j)

/-- The output form of `Program.stableBefore_wireEarliests`. -/
theorem Circuit.stableBefore_outputEarliests {σ : Signature.{v}} {inputCount outputCount : Nat}
    {U : Type*} (c : Circuit σ inputCount outputCount) (cdelay : Fin c.size → ℝ)
    (inputEarliest : Fin inputCount → WithTop ℝ)
    (inputSignal : Fin inputCount → ℝ → U) (gateSignal : Fin c.size → ℝ → U)
    (hcausal : c.program.Causal cdelay inputSignal gateSignal)
    (hinput : ∀ i, StableBefore (inputSignal i) (inputEarliest i))
    (o : Fin outputCount) :
    StableBefore (Wire.elim inputSignal gateSignal (c.outputs o))
      (c.outputEarliests cdelay inputEarliest o) :=
  c.program.stableBefore_wireEarliests cdelay inputEarliest inputSignal gateSignal
    hcausal hinput (c.outputs o)

/-- **Hold certificate.** A register clocked at time `0` launches the circuit
inputs, which after the edge cannot change before its minimum clock-to-Q delay
`tqMin`. Under the causal gate-delay model, if `hold + u ≤ tqMin + earliest_path`, where
`earliest_path` is the output's earliest change with inputs changing at time
`0`, the receiving register's hold check passes. -/
theorem Circuit.holdMet_of_le_outputEarliests {σ : Signature.{v}}
    {inputCount outputCount : Nat} {U : Type*} (c : Circuit σ inputCount outputCount)
    (cdelay : Fin c.size → ℝ)
    (inputSignal : Fin inputCount → ℝ → U) (gateSignal : Fin c.size → ℝ → U)
    (tqMin hold u : ℝ≥0)
    (hcausal : c.program.Causal cdelay inputSignal gateSignal)
    (hlaunch : ∀ i, StableBefore (inputSignal i) ((tqMin : ℝ) : WithTop ℝ))
    (o : Fin outputCount)
    (hcert : (((hold : ℝ) + u : ℝ) : WithTop ℝ) ≤
      ((tqMin : ℝ) : WithTop ℝ) + c.outputEarliests cdelay (fun _ => 0) o) :
    HoldMet (Wire.elim inputSignal gateSignal (c.outputs o)) hold u := by
  have hs := c.stableBefore_outputEarliests cdelay (fun _ => ((tqMin : ℝ) : WithTop ℝ))
    inputSignal gateSignal hcausal hlaunch o
  have hshift := c.outputEarliests_add cdelay (fun _ => 0) (tqMin : ℝ) o
  simp only [add_zero] at hshift
  rw [hshift] at hs
  exact StableBefore.mono hcert hs

/-- **Capture certificate.** Under the premises of
`Circuit.holdMet_of_le_outputEarliests`, if the receiving register's data input
also settled `setup + u` seconds before the edge, it holds its value at the edge
on `[-(setup + u), hold + u)`. -/
theorem Circuit.captureMet_of_le_outputEarliests {σ : Signature.{v}}
    {inputCount outputCount : Nat} {U : Type*} (c : Circuit σ inputCount outputCount)
    (cdelay : Fin c.size → ℝ)
    (inputSignal : Fin inputCount → ℝ → U) (gateSignal : Fin c.size → ℝ → U)
    (tqMin setup hold u : ℝ≥0)
    (hcausal : c.program.Causal cdelay inputSignal gateSignal)
    (hlaunch : ∀ i, StableBefore (inputSignal i) ((tqMin : ℝ) : WithTop ℝ))
    (o : Fin outputCount)
    (hsettled : SettledBefore (Wire.elim inputSignal gateSignal (c.outputs o)) (setup + u))
    (hcert : (((hold : ℝ) + u : ℝ) : WithTop ℝ) ≤
      ((tqMin : ℝ) : WithTop ℝ) + c.outputEarliests cdelay (fun _ => 0) o) :
    CaptureMet (Wire.elim inputSignal gateSignal (c.outputs o)) setup hold u := by
  have hhold := c.holdMet_of_le_outputEarliests cdelay inputSignal gateSignal tqMin hold u
    hcausal hlaunch o hcert
  intro t hlo hhi
  rcases le_or_gt t 0 with ht | ht
  · exact hsettled t (by rw [NNReal.coe_add]; exact hlo) ht
  · exact hhold t 0 ht.le le_rfl hhi
      (lt_trans (WithTop.coe_lt_coe.mpr ht) hhi)

end Cslib.Circuits
