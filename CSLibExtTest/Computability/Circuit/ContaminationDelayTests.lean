/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Circuit.ContaminationDelay
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! Tests for contamination-delay propagation and the hold certificate on a circuit with a slow
path and a short bypass that passes setup but fails hold, plus a constant output. -/

namespace Cslib.Circuits

/-! ### The circuit -/

/-- Binary gates and constants over `Bool`. -/
private abbrev σ2 : Signature := fullSignature 2 Bool

/-- A buffer: a binary gate that reads one wire twice and returns it. -/
private def bufLine {n g : ℕ} (w : Wire n g) : Line σ2 n g :=
  ⟨FullOp.fn (fun f => f 0), ![w, w]⟩

/-- A binary XOR gate. -/
private def xorLine {n g : ℕ} (v w : Wire n g) : Line σ2 n g :=
  ⟨FullOp.fn (fun f => f 0 ^^ f 1), ![v, w]⟩

/-- A constant gate, with no inputs. -/
private def conLine {n g : ℕ} (b : Bool) : Line σ2 n g := ⟨FullOp.con b, Fin.elim0⟩

/-- The first three gates: `g0 = buf input`, `g1 = buf g0` (the slow path), and
`g2 = xor g1 input` (the input also reaches `g2` directly, the short bypass). -/
private def prog3 : Program σ2 1 3 :=
  ((Program.empty.gate (bufLine (.input 0))).gate (bufLine (.gate 0))).gate
    (xorLine (.gate 1) (.input 0))

/-- Four gates: `prog3` and the constant `g3`. -/
private def prog : Program σ2 1 4 := prog3.gate (conLine true)

/-- One input, the launching register's output. Output `0` is `g2`, the receiving register's
data input; output `1` is the constant `g3`. -/
private def circ : Circuit σ2 1 2 := ⟨prog, ![.gate 2, .gate 3]⟩

/-- Contamination delays, in seconds. -/
private noncomputable def cdelay : Fin 4 → ℝ := ![3, 3, 1/2, 1]

private theorem cdelay_nonneg (j : Fin 4) : 0 ≤ cdelay j := by
  fin_cases j <;> norm_num [cdelay]

/-! ### Earliest changes -/

/-- With the input changing at `0`, `g2` can change at `1/2` through the bypass, not at the
slow path's `6`. -/
private theorem outputEarliests_zero :
    circ.outputEarliests cdelay (fun _ => 0) 0 = ((1/2 : ℝ) : WithTop ℝ) := by
  change prog.earliests cdelay (fun _ => 0) (Fin.last 2).castSucc = _
  rw [prog, Program.earliests_gate_castSucc, prog3, Program.earliests_gate_last]
  apply le_antisymm
  · refine (Line.earliest_le_add_wireEarliest _ _ _ ⟨1, Nat.one_lt_two⟩).trans (le_of_eq ?_)
    change ((1/2 : ℝ) : WithTop ℝ) + 0 = _
    exact add_zero _
  · calc ((1/2 : ℝ) : WithTop ℝ) = ((cdelay 2 : ℝ) : WithTop ℝ) + ((0 : ℝ) : WithTop ℝ) := by
          norm_num [cdelay]
      _ ≤ _ := Line.add_le_earliest_of_forall_le _ _ _ _ fun _ =>
          Program.le_wireEarliests _ _ _ 0 (fun _ => cdelay_nonneg _) (fun _ => le_rfl) _

/-- The constant `g3` never changes. -/
private theorem outputEarliests_one : circ.outputEarliests cdelay (fun _ => 0) 1 = ⊤ := by
  change prog.earliests cdelay (fun _ => 0) (Fin.last 3) = ⊤
  rw [prog, Program.earliests_gate_last]
  exact Line.earliest_of_arity_eq_zero _ _ _ rfl

/-- Launching at `tqMin = 1` shifts the earliest change of `g2` to `3/2`. -/
example : circ.outputEarliests cdelay (fun _ => ((1 : ℝ) : WithTop ℝ)) 0
    = ((3/2 : ℝ) : WithTop ℝ) := by
  have h := circ.outputEarliests_add cdelay (fun _ => 0) 1 0
  simp only [add_zero] at h
  rw [h, outputEarliests_zero, ← WithTop.coe_add]
  norm_num

/-- With nonnegative delays, nothing changes before the launch. -/
example (w : Wire 1 4) :
    ((1 : ℝ) : WithTop ℝ) ≤ prog.wireEarliests cdelay (fun _ => ((1 : ℝ) : WithTop ℝ)) w :=
  prog.le_wireEarliests cdelay _ 1 cdelay_nonneg (fun _ => le_rfl) w

/-! ### Signals obeying the causal model -/

/-- The launching register's output: `false` before `tqMin = 1`, `true` from `1` on. -/
private noncomputable def inSig : Fin 1 → ℝ → Bool := fun _ t => decide (1 ≤ t)

/-- Gate signals with transport delays `4, 4, 1/2, 1`, each at least the contamination delay:
the slow path through `g0` and `g1` takes `8`, the bypass `1/2`. -/
private noncomputable def s0 (t : ℝ) : Bool := inSig 0 (t - 4)
private noncomputable def s1 (t : ℝ) : Bool := s0 (t - 4)
private noncomputable def s2 (t : ℝ) : Bool := s1 (t - 1/2) ^^ inSig 0 (t - 1/2)
private def s3 (_ : ℝ) : Bool := true

private noncomputable def gSig : Fin 4 → ℝ → Bool := ![s0, s1, s2, s3]

/-- A gate whose output is a function of its inputs `δ` seconds earlier obeys the causal model
for any contamination delay at most `δ`. -/
private theorem causal_of_transport {σ : Signature} {m g : ℕ} {U : Type*} (line : Line σ m g)
    (W : Wire m g → ℝ → U) (d δ : ℝ) (hd : d ≤ δ) (out : ℝ → U)
    (F : (Fin (σ.Arity line.op) → U) → U)
    (hout : ∀ t, out t = F fun k => W (line.wires k) (t - δ)) : line.Causal W d out := by
  have shift : ∀ {t : ℝ} {τ : WithTop ℝ}, (t : WithTop ℝ) < (d : WithTop ℝ) + τ →
      ((t - δ : ℝ) : WithTop ℝ) < τ := by
    intro t τ h
    induction τ using WithTop.recTopCoe with
    | top => exact WithTop.coe_lt_top _
    | coe r =>
      rw [← WithTop.coe_add, WithTop.coe_lt_coe] at h
      rw [WithTop.coe_lt_coe]
      linarith
  intro τ h t₁ t₂ h₁ h₂
  rw [hout, hout]
  congr 1
  funext k
  exact h k _ _ (shift h₁) (shift h₂)

private theorem prog_causal : prog.Causal cdelay inSig gSig :=
  ⟨⟨⟨⟨trivial, causal_of_transport _ _ _ 4 (show (3 : ℝ) ≤ 4 by norm_num) _
      (fun f : Fin 2 → Bool => f 0) fun _ => rfl⟩,
    causal_of_transport _ _ _ 4 (show (3 : ℝ) ≤ 4 by norm_num) _
      (fun f : Fin 2 → Bool => f 0) fun _ => rfl⟩,
    causal_of_transport _ _ _ (1/2) (show (1/2 : ℝ) ≤ 1/2 from le_rfl) _
      (fun f : Fin 2 → Bool => f 0 ^^ f 1) fun _ => rfl⟩,
    causal_of_transport _ _ _ 1 (show (1 : ℝ) ≤ 1 from le_rfl) _
      (fun _ : Fin 0 → Bool => true) fun _ => rfl⟩

private theorem launch_stable : ∀ i, StableBefore (inSig i) ((1 : ℝ) : WithTop ℝ) := by
  intro i t₁ t₂ h₁ h₂
  rw [WithTop.coe_lt_coe] at h₁ h₂
  simp [inSig, not_le.mpr h₁, not_le.mpr h₂]

private theorem s2_eq (t : ℝ) : s2 t = (decide (1 ≤ t - 17/2) ^^ decide (1 ≤ t - 1/2)) := by
  simp only [s2, s1, s0, inSig]
  congr 3
  ring

private theorem s2_of_lt {t : ℝ} (ht : t < 3/2) : s2 t = false := by
  rw [s2_eq, decide_eq_false (by linarith), decide_eq_false (by linarith)]
  rfl

/-! ### Setup passes, hold fails -/

/-- **Setup passes.** With the next edge at `T = 12`, setup time `1` and uncertainty `1/2`, the
slow path settles in time: `g2` holds its final value from `12 - 1 - 1/2` on. -/
example : ∀ t : ℝ, 12 - 1 - 1/2 ≤ t → s2 t = false := by
  intro t ht
  rw [s2_eq, decide_eq_true (by linarith), decide_eq_true (by linarith)]
  rfl

/-- **Hold at the boundary.** With `hold + u = 1 + 1/2 = tqMin + earliest_path`, the
certificate gives hold. -/
example : HoldMet s2 1 (1/2) :=
  circ.holdMet_of_le_outputEarliests cdelay inSig gSig 1 1 (1/2) prog_causal launch_stable 0
    (by rw [outputEarliests_zero, ← WithTop.coe_add])

/-- The boundary is attained: the bypass changes `g2` at `3/2`, so any longer hold window
fails. -/
example : ¬ HoldMet s2 1 (3/4) := by
  intro h
  have := h 0 (3/2) (by rw [WithTop.coe_lt_coe]; norm_num) (by rw [WithTop.coe_lt_coe]; norm_num)
  rw [s2_of_lt (by norm_num), s2_eq] at this
  norm_num at this

/-- **Hold fails.** With `hold = 2` and `u = 1/2` the certificate fails, and the hold check
really fails: `g2` changes at `3/2`, although the slow path settles only at `19/2`. -/
example : ¬ ((2 + 1/2 : ℝ) : WithTop ℝ) ≤
    ((1 : ℝ) : WithTop ℝ) + circ.outputEarliests cdelay (fun _ => 0) 0 := by
  rw [outputEarliests_zero, ← WithTop.coe_add, WithTop.coe_le_coe]
  norm_num

example : ¬ HoldMet s2 2 (1/2) := by
  intro h
  have := h 0 2 (by rw [WithTop.coe_lt_coe]; norm_num) (by rw [WithTop.coe_lt_coe]; norm_num)
  rw [s2_of_lt (by norm_num), s2_eq] at this
  norm_num at this

/-- **No-transition output.** The constant meets any hold requirement. -/
example : HoldMet s3 100 (1/2) :=
  circ.holdMet_of_le_outputEarliests cdelay inSig gSig 1 100 (1/2) prog_causal launch_stable 1
    (by rw [outputEarliests_one, WithTop.add_top]; exact le_top)

end Cslib.Circuits
