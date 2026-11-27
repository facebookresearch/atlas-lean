/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Computability.Circuit.Depth
public import Mathlib.Basic.Real.Basic

/-!
# Arrival times of a circuit with gate delays

A CSLib circuit is a topologically ordered straight-line program with designated output wires,
so it has no combinational cycles. This file annotates it with a real delay on every gate and a
real arrival time on every input. A gate's output arrives at its delay plus the latest arrival
among the wires it reads, the maximum taken from the time origin `0` (`Line.arrival`). A constant
gate, one with no arguments, therefore arrives at its delay, just as `Line.depth` gives it depth
`1`. `Program.arrivals`, `Program.wireArrivals` and `Circuit.outputArrivals` give the arrival
time of every gate, every wire and every designated output.

The main result, `Circuit.outputArrivals_le_add_mul_outputDepths_of_nonneg_bound`, bounds
arrival times by depth: if every delay is at most a bound `D ≥ 0` and every input arrives by
`a0 ≥ 0`, then every designated output arrives by `a0 + D * d`, where `d` is its depth
`Circuit.outputDepths`. Hence every output arrives by `a0 + D * Circuit.depth`
(`Circuit.outputArrivals_le_add_mul_depth_of_nonneg_bound`). Individual delays may be negative.
Both premises are needed: with a negative bound `D`, or with inputs arriving before the origin,
an output can arrive later than the bound. The forms without the `_of_nonneg_bound` suffix
(`Circuit.outputArrivals_le_add_mul_outputDepths`, `Circuit.outputArrivals_le_add_mul_depth`)
assume instead that every delay lies in `[0, D]`; that gives `0 ≤ D` whenever the circuit has a
gate, and a circuit without gates meets the bound for every `D`.

Delays are premises of the model, not measured hardware values; hold times, clock-domain
crossings and glitches are outside it.
-/

@[expose] public section

namespace Cslib.Circuits

universe v

/-- The arrival time of a line's output: the gate delay plus the latest
arrival among the wires it reads, the maximum folded from the time origin
`0`. A constant (zero-input) gate therefore arrives at its delay. -/
def Line.arrival {σ : Signature.{v}} {inputCount gateCount : Nat}
    (line : Line σ inputCount gateCount)
    (wireArrivals : Wire inputCount gateCount → ℝ) (delay : ℝ) : ℝ :=
  delay + Fin.foldl (σ.Arity line.op)
    (fun t k => max t (wireArrivals (line.wires k))) 0

/-- The arrival time of every gate of a program, for a delay on every gate
and an arrival time on every original input. -/
def Program.arrivals {σ : Signature.{v}} {inputCount : Nat} :
    {gateCount : Nat} → Program σ inputCount gateCount →
      (Fin gateCount → ℝ) → (Fin inputCount → ℝ) → Fin gateCount → ℝ
  | _, .empty, _, _ => Fin.elim0
  | _, .gate p line, delay, inputArrival =>
      let prior := p.arrivals (fun j => delay j.castSucc) inputArrival
      Fin.lastCases
        (line.arrival (Wire.elim inputArrival prior) (delay (Fin.last _))) prior

/-- The arrival time of every input or gate wire of a program. -/
def Program.wireArrivals {σ : Signature.{v}} {inputCount gateCount : Nat}
    (p : Program σ inputCount gateCount) (delay : Fin gateCount → ℝ)
    (inputArrival : Fin inputCount → ℝ) : Wire inputCount gateCount → ℝ :=
  Wire.elim inputArrival (p.arrivals delay inputArrival)

/-- The arrival time of every designated output of a circuit. -/
def Circuit.outputArrivals {σ : Signature.{v}} {inputCount outputCount : Nat}
    (c : Circuit σ inputCount outputCount) (delay : Fin c.size → ℝ)
    (inputArrival : Fin inputCount → ℝ) : Fin outputCount → ℝ :=
  c.program.wireArrivals delay inputArrival ∘ c.outputs

private theorem foldl_max_le_of_forall_le {α : Type*} [LinearOrder α] {n : Nat}
    (g : Fin n → α) (b t : α) (hb : b ≤ t) (h : ∀ j, g j ≤ t) :
    Fin.foldl n (fun s k => max s (g k)) b ≤ t := by
  induction n with
  | zero => rw [Fin.foldl_zero]; exact hb
  | succ n ih =>
    rw [Fin.foldl_succ_last]
    exact max_le (ih _ (fun k => h k.castSucc)) (h _)

private theorem le_foldl_max_of_mem {α : Type*} [LinearOrder α] {n : Nat}
    (g : Fin n → α) (b : α) (j : Fin n) :
    g j ≤ Fin.foldl n (fun s k => max s (g k)) b := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    rw [Fin.foldl_succ_last]
    refine Fin.lastCases ?_ (fun i => ?_) j
    · exact le_max_right _ _
    · exact le_trans (ih (fun k => g k.castSucc) i) (le_max_left _ _)

/-- A gate with no inputs arrives at its delay. -/
theorem Line.arrival_of_arity_eq_zero {σ : Signature.{v}} {inputCount gateCount : Nat}
    (line : Line σ inputCount gateCount) (wireArrivals : Wire inputCount gateCount → ℝ)
    (delay : ℝ) (h : σ.Arity line.op = 0) :
    line.arrival wireArrivals delay = delay := by
  simp only [Line.arrival, h, Fin.foldl_zero, add_zero]

/-- Every fan-in arrival plus the delay is at most the gate's arrival. -/
theorem Line.add_wireArrival_le_arrival {σ : Signature.{v}} {inputCount gateCount : Nat}
    (line : Line σ inputCount gateCount) (wireArrivals : Wire inputCount gateCount → ℝ)
    (delay : ℝ) (j : Fin (σ.Arity line.op)) :
    delay + wireArrivals (line.wires j) ≤ line.arrival wireArrivals delay :=
  add_le_add_right (le_foldl_max_of_mem (fun k => wireArrivals (line.wires k)) 0 j) delay

/-- The gate's arrival is the delay plus the least upper bound, from `0`, of
its fan-in arrivals: any `t ≥ 0` bounding every fan-in arrival bounds the
arrival by `delay + t`. -/
theorem Line.arrival_le_of_forall_le {σ : Signature.{v}} {inputCount gateCount : Nat}
    (line : Line σ inputCount gateCount) (wireArrivals : Wire inputCount gateCount → ℝ)
    (delay t : ℝ) (ht : 0 ≤ t) (h : ∀ j, wireArrivals (line.wires j) ≤ t) :
    line.arrival wireArrivals delay ≤ delay + t :=
  add_le_add_right
    (foldl_max_le_of_forall_le (fun k => wireArrivals (line.wires k)) 0 t ht h) delay

/-- The newest gate arrives by its line's arrival over the earlier wires. -/
theorem Program.arrivals_gate_last {σ : Signature.{v}} {inputCount gateCount : Nat}
    (p : Program σ inputCount gateCount) (line : Line σ inputCount gateCount)
    (delay : Fin (gateCount + 1) → ℝ) (inputArrival : Fin inputCount → ℝ) :
    (p.gate line).arrivals delay inputArrival (Fin.last gateCount)
      = line.arrival (p.wireArrivals (fun j => delay j.castSucc) inputArrival)
          (delay (Fin.last gateCount)) := by
  simp [Program.arrivals, Program.wireArrivals]

/-- Adding a gate does not change earlier arrivals. -/
theorem Program.arrivals_gate_castSucc {σ : Signature.{v}} {inputCount gateCount : Nat}
    (p : Program σ inputCount gateCount) (line : Line σ inputCount gateCount)
    (delay : Fin (gateCount + 1) → ℝ) (inputArrival : Fin inputCount → ℝ)
    (j : Fin gateCount) :
    (p.gate line).arrivals delay inputArrival j.castSucc
      = p.arrivals (fun k => delay k.castSucc) inputArrival j := by
  simp [Program.arrivals]

/-- An input wire arrives at its given arrival time. -/
theorem Program.wireArrivals_input {σ : Signature.{v}} {inputCount gateCount : Nat}
    (p : Program σ inputCount gateCount) (delay : Fin gateCount → ℝ)
    (inputArrival : Fin inputCount → ℝ) (i : Fin inputCount) :
    p.wireArrivals delay inputArrival (.input i) = inputArrival i := by
  rfl

/-- Under delays at most a bound `D ≥ 0` and input arrivals at most `a0 ≥ 0`,
every wire arrives no later than `a0 + D` times its depth. The delays themselves
may be negative. -/
theorem Program.wireArrivals_le_add_mul_wireDepths_of_nonneg_bound {σ : Signature.{v}}
    {inputCount gateCount : Nat} (p : Program σ inputCount gateCount)
    (delay : Fin gateCount → ℝ) (inputArrival : Fin inputCount → ℝ) (a0 D : ℝ)
    (ha0 : 0 ≤ a0) (hinput : ∀ i, inputArrival i ≤ a0)
    (hD : 0 ≤ D) (hdelay_le : ∀ j, delay j ≤ D)
    (w : Wire inputCount gateCount) :
    p.wireArrivals delay inputArrival w ≤ a0 + D * (p.wireDepths w : ℝ) := by
  induction p with
  | empty =>
    cases w with
    | input i => simpa [Program.wireArrivals_input] using hinput i
    | gate j => exact Fin.elim0 j
  | @gate gateCount p line ih =>
    cases w with
    | input i => simpa [Program.wireArrivals_input] using hinput i
    | gate j =>
      refine Fin.lastCases ?_ (fun i => ?_) j
      · change (p.gate line).arrivals delay inputArrival (Fin.last gateCount) ≤
          a0 + D * ((p.gate line).depths (Fin.last gateCount) : ℝ)
        rw [Program.arrivals_gate_last, Program.depths_gate_last]
        set M : Nat := Fin.foldl (σ.Arity line.op)
          (fun d k => max d (p.wireDepths (line.wires k))) 0 with hM
        have hfan : ∀ k : Fin (σ.Arity line.op),
            p.wireArrivals (fun j => delay j.castSucc) inputArrival (line.wires k)
              ≤ a0 + D * (M : ℝ) := by
          intro k
          have hmem : (p.wireDepths (line.wires k) : ℝ) ≤ (M : ℝ) :=
            Nat.cast_le.mpr (le_foldl_max_of_mem (fun k => p.wireDepths (line.wires k)) 0 k)
          exact le_trans (ih _ (fun j => hdelay_le j.castSucc) (line.wires k))
            (add_le_add_right (mul_le_mul_of_nonneg_left hmem hD) a0)
        have ht : (0 : ℝ) ≤ a0 + D * (M : ℝ) :=
          add_nonneg ha0 (mul_nonneg hD (Nat.cast_nonneg M))
        have hdepth : ((line.depth p.wireDepths : Nat) : ℝ) = (M : ℝ) + 1 := by
          simp only [Line.depth, ← hM, Nat.cast_succ]
        rw [hdepth, mul_add, mul_one]
        refine le_trans (Line.arrival_le_of_forall_le line _ (delay (Fin.last _)) _ ht hfan) ?_
        calc delay (Fin.last _) + (a0 + D * (M : ℝ))
            = (a0 + D * (M : ℝ)) + delay (Fin.last _) := add_comm _ _
          _ ≤ (a0 + D * (M : ℝ)) + D := add_le_add_right (hdelay_le _) _
          _ = a0 + (D * (M : ℝ) + D) := add_assoc _ _ _
      · change (p.gate line).arrivals delay inputArrival i.castSucc ≤
          a0 + D * ((p.gate line).depths i.castSucc : ℝ)
        rw [Program.arrivals_gate_castSucc, Program.depths_gate_castSucc]
        exact ih _ (fun k => hdelay_le k.castSucc) (.gate i)

/-- Under delays in `[0, D]` and input arrivals at most `a0 ≥ 0`, every wire
arrives no later than `a0 + D` times its depth. -/
theorem Program.wireArrivals_le_add_mul_wireDepths {σ : Signature.{v}}
    {inputCount gateCount : Nat} (p : Program σ inputCount gateCount)
    (delay : Fin gateCount → ℝ) (inputArrival : Fin inputCount → ℝ) (a0 D : ℝ)
    (ha0 : 0 ≤ a0) (hinput : ∀ i, inputArrival i ≤ a0)
    (hdelay_nonneg : ∀ j, 0 ≤ delay j) (hdelay_le : ∀ j, delay j ≤ D)
    (w : Wire inputCount gateCount) :
    p.wireArrivals delay inputArrival w ≤ a0 + D * (p.wireDepths w : ℝ) := by
  by_cases hD : 0 ≤ D
  · exact p.wireArrivals_le_add_mul_wireDepths_of_nonneg_bound delay inputArrival a0 D ha0
      hinput hD hdelay_le w
  · -- A negative bound `D` admits no gate, so `w` is an input of depth `0`.
    cases w with
    | input i => simpa [Program.wireArrivals_input] using hinput i
    | gate j => exact absurd (le_trans (hdelay_nonneg j) (hdelay_le j)) hD

/-- Under delays at most a bound `D ≥ 0` and input arrivals at most `a0 ≥ 0`,
every designated output arrives no later than `a0 + D` times its depth. -/
theorem Circuit.outputArrivals_le_add_mul_outputDepths_of_nonneg_bound {σ : Signature.{v}}
    {inputCount outputCount : Nat} (c : Circuit σ inputCount outputCount)
    (delay : Fin c.size → ℝ) (inputArrival : Fin inputCount → ℝ) (a0 D : ℝ)
    (ha0 : 0 ≤ a0) (hinput : ∀ i, inputArrival i ≤ a0)
    (hD : 0 ≤ D) (hdelay_le : ∀ j, delay j ≤ D)
    (o : Fin outputCount) :
    c.outputArrivals delay inputArrival o ≤ a0 + D * (c.outputDepths o : ℝ) :=
  Program.wireArrivals_le_add_mul_wireDepths_of_nonneg_bound c.program delay inputArrival
    a0 D ha0 hinput hD hdelay_le (c.outputs o)

/-- Under the same premises every designated output arrives no later than
`a0 + D` times the circuit depth. -/
theorem Circuit.outputArrivals_le_add_mul_depth_of_nonneg_bound {σ : Signature.{v}}
    {inputCount outputCount : Nat} (c : Circuit σ inputCount outputCount)
    (delay : Fin c.size → ℝ) (inputArrival : Fin inputCount → ℝ) (a0 D : ℝ)
    (ha0 : 0 ≤ a0) (hinput : ∀ i, inputArrival i ≤ a0)
    (hD : 0 ≤ D) (hdelay_le : ∀ j, delay j ≤ D)
    (o : Fin outputCount) :
    c.outputArrivals delay inputArrival o ≤ a0 + D * (c.depth : ℝ) :=
  le_trans
    (c.outputArrivals_le_add_mul_outputDepths_of_nonneg_bound delay inputArrival a0 D ha0
      hinput hD hdelay_le o)
    (add_le_add_right
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (c.outputDepths_le_depth o)) hD) a0)

/-- Under delays in `[0, D]` and input arrivals at most `a0 ≥ 0`, every
designated output arrives no later than `a0 + D` times its depth. -/
theorem Circuit.outputArrivals_le_add_mul_outputDepths {σ : Signature.{v}}
    {inputCount outputCount : Nat} (c : Circuit σ inputCount outputCount)
    (delay : Fin c.size → ℝ) (inputArrival : Fin inputCount → ℝ) (a0 D : ℝ)
    (ha0 : 0 ≤ a0) (hinput : ∀ i, inputArrival i ≤ a0)
    (hdelay_nonneg : ∀ j, 0 ≤ delay j) (hdelay_le : ∀ j, delay j ≤ D)
    (o : Fin outputCount) :
    c.outputArrivals delay inputArrival o ≤ a0 + D * (c.outputDepths o : ℝ) :=
  Program.wireArrivals_le_add_mul_wireDepths c.program delay inputArrival
    a0 D ha0 hinput hdelay_nonneg hdelay_le (c.outputs o)

/-- Under the same premises every designated output arrives no later than
`a0 + D` times the circuit depth. -/
theorem Circuit.outputArrivals_le_add_mul_depth {σ : Signature.{v}}
    {inputCount outputCount : Nat} (c : Circuit σ inputCount outputCount)
    (delay : Fin c.size → ℝ) (inputArrival : Fin inputCount → ℝ) (a0 D : ℝ)
    (ha0 : 0 ≤ a0) (hinput : ∀ i, inputArrival i ≤ a0)
    (hdelay_nonneg : ∀ j, 0 ≤ delay j) (hdelay_le : ∀ j, delay j ≤ D)
    (o : Fin outputCount) :
    c.outputArrivals delay inputArrival o ≤ a0 + D * (c.depth : ℝ) := by
  have hhead := Circuit.outputArrivals_le_add_mul_outputDepths c delay inputArrival
    a0 D ha0 hinput hdelay_nonneg hdelay_le o
  by_cases hD : 0 ≤ D
  · have hle : (c.outputDepths o : ℝ) ≤ (c.depth : ℝ) :=
      Nat.cast_le.mpr (c.outputDepths_le_depth o)
    exact le_trans hhead (add_le_add_right (mul_le_mul_of_nonneg_left hle hD) a0)
  · -- A negative bound `D` admits no gate, so every output is an input of depth `0`.
    have hsize : c.size = 0 := by
      by_contra hne
      have hpos : 0 < c.size := Nat.pos_of_ne_zero hne
      exact hD (le_trans (hdelay_nonneg ⟨0, hpos⟩) (hdelay_le ⟨0, hpos⟩))
    have hall : ∀ k, c.outputDepths k = 0 := by
      intro k
      simp only [Circuit.outputDepths, Function.comp_apply]
      cases c.outputs k with
      | input i => exact Program.wireDepths_input _ _
      | gate j => rw [hsize] at j; exact Fin.elim0 j
    have hdepth0 : c.depth = 0 := Nat.le_zero.mp (c.depth_le_iff.mpr fun k => (hall k).le)
    rw [hall o, Nat.cast_zero, mul_zero, add_zero] at hhead
    rw [hdepth0, Nat.cast_zero, mul_zero, add_zero]
    exact hhead

end Cslib.Circuits
