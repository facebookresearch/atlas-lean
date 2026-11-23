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

/-! Tests for contamination-delay propagation and the hold and capture certificates on a circuit
with a slow path and a short bypass that passes setup but fails hold, plus a constant output,
repeated launches, a late launch, a signal that changes at the edge and a negative delay. -/

namespace Cslib.Circuits

open scoped NNReal

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

/-- The hold certificate's premise for output `0`, a nonnegative real inequality. -/
private theorem cert_zero (tqMin hold u : ℝ≥0) (h : (hold : ℝ) + u ≤ tqMin + 1/2) :
    (((hold : ℝ) + u : ℝ) : WithTop ℝ) ≤
      ((tqMin : ℝ) : WithTop ℝ) + circ.outputEarliests cdelay (fun _ => 0) 0 := by
  rw [outputEarliests_zero, ← WithTop.coe_add, WithTop.coe_le_coe]
  exact h

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

/-- Gate signals driven by the launching register's output `x`, with transport delays
`4, 4, 1/2, 1`, each at least the contamination delay: the slow path through `g0` and `g1`
takes `8`, the bypass `1/2`. -/
private noncomputable def s0 (x : ℝ → Bool) (t : ℝ) : Bool := x (t - 4)
private noncomputable def s1 (x : ℝ → Bool) (t : ℝ) : Bool := s0 x (t - 4)
private noncomputable def s2 (x : ℝ → Bool) (t : ℝ) : Bool := s1 x (t - 1/2) ^^ x (t - 1/2)
private def s3 (_ : ℝ) : Bool := true

private noncomputable def gSig (x : ℝ → Bool) : Fin 4 → ℝ → Bool := ![s0 x, s1 x, s2 x, s3]

private theorem s2_eq (x : ℝ → Bool) (t : ℝ) : s2 x t = (x (t - 17/2) ^^ x (t - 1/2)) := by
  simp only [s2, s1, s0]
  congr 2
  ring

/-- A gate whose output is a function of its inputs `δ` seconds earlier, and whose inputs did
not change during the `δ` seconds before the edge, obeys the causal model for any nonnegative
contamination delay at most `δ`. -/
private theorem causal_of_transport {σ : Signature} {m g : ℕ} {U : Type*} (line : Line σ m g)
    (W : Wire m g → ℝ → U) (d δ : ℝ) (hd₀ : 0 ≤ d) (hd : d ≤ δ) (out : ℝ → U)
    (F : (Fin (σ.Arity line.op) → U) → U)
    (hout : ∀ t, out t = F fun k => W (line.wires k) (t - δ))
    (hsettled : ∀ k t, -δ ≤ t → t ≤ 0 → W (line.wires k) t = W (line.wires k) 0) :
    line.Causal W d out := by
  have shift : ∀ {t : ℝ} {τ : WithTop ℝ}, (t : WithTop ℝ) < (d : WithTop ℝ) + τ →
      ((t - δ : ℝ) : WithTop ℝ) < τ := by
    intro t τ h
    induction τ using WithTop.recTopCoe with
    | top => exact WithTop.coe_lt_top _
    | coe r =>
      rw [← WithTop.coe_add, WithTop.coe_lt_coe] at h
      rw [WithTop.coe_lt_coe]
      linarith
  refine ⟨hd₀, fun τ h t₁ t₂ h₀₁ h₀₂ h₁ h₂ => ?_⟩
  have key : ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < (d : WithTop ℝ) + τ →
      ∀ k, W (line.wires k) (t - δ) = W (line.wires k) 0 := by
    intro t h₀ ht k
    by_cases hle : t - δ ≤ 0
    · exact hsettled k _ (by linarith) hle
    · have hpos : 0 < t - δ := lt_of_not_ge hle
      exact h k _ _ hpos.le le_rfl (shift ht)
        (lt_trans (WithTop.coe_lt_coe.mpr hpos) (shift ht))
  rw [hout, hout]
  congr 1
  funext k
  rw [key t₁ h₀₁ h₁ k, key t₂ h₀₂ h₂ k]

/-- The program obeys the causal model whenever the launching register's output did not change
during the slow path's `17/2` seconds before the edge (the previous cycle settled). -/
private theorem prog_causal (x : ℝ → Bool) (hx : ∀ t, -17/2 ≤ t → t ≤ 0 → x t = x 0) :
    prog.Causal cdelay (fun _ => x) (gSig x) :=
  ⟨⟨⟨⟨trivial, causal_of_transport _ _ _ 4 (show (0 : ℝ) ≤ 3 by norm_num)
      (show (3 : ℝ) ≤ 4 by norm_num) _
      (fun f : Fin 2 → Bool => f 0) (fun _ => rfl) fun k t h₁ h₂ => by
        fin_cases k <;> exact hx t (by linarith) h₂⟩,
    causal_of_transport _ _ _ 4 (show (0 : ℝ) ≤ 3 by norm_num)
      (show (3 : ℝ) ≤ 4 by norm_num) _
      (fun f : Fin 2 → Bool => f 0) (fun _ => rfl) fun k t h₁ h₂ => by
        fin_cases k <;>
          exact (hx (t - 4) (by linarith) (by linarith)).trans
            (hx (0 - 4) (by norm_num) (by norm_num)).symm⟩,
    causal_of_transport _ _ _ (1/2) (show (0 : ℝ) ≤ 1/2 by norm_num)
      (show (1/2 : ℝ) ≤ 1/2 from le_rfl) _
      (fun f : Fin 2 → Bool => f 0 ^^ f 1) (fun _ => rfl) fun k t h₁ h₂ => by
        fin_cases k
        · exact (hx (t - 4 - 4) (by linarith) (by linarith)).trans
            (hx (0 - 4 - 4) (by norm_num) (by norm_num)).symm
        · exact hx t (by linarith) h₂⟩,
    causal_of_transport _ _ _ 1 (show (0 : ℝ) ≤ 1 by norm_num) (show (1 : ℝ) ≤ 1 from le_rfl) _
      (fun _ : Fin 0 → Bool => true) (fun _ => rfl) fun k => k.elim0⟩

/-! ### Single launch: setup passes, hold fails -/

/-- The launching register's output: `false` before `tqMin = 1`, `true` from `1` on. -/
private noncomputable def x₁ (t : ℝ) : Bool := decide (1 ≤ t)

private theorem x₁_settled (t : ℝ) (_ : -17/2 ≤ t) (ht : t ≤ 0) : x₁ t = x₁ 0 := by
  simp [x₁, show ¬ 1 ≤ t by linarith]

private theorem launch_stable₁ : ∀ _ : Fin 1, StableBefore x₁ ((1 : ℝ) : WithTop ℝ) := by
  intro _ t₁ t₂ _ _ h₁ h₂
  rw [WithTop.coe_lt_coe] at h₁ h₂
  simp [x₁, not_le.mpr h₁, not_le.mpr h₂]

private theorem s2_of_lt {t : ℝ} (ht : t < 3/2) : s2 x₁ t = false := by
  rw [s2_eq, x₁, x₁, decide_eq_false (by linarith), decide_eq_false (by linarith)]
  rfl

/-- **Setup passes.** With the next edge at `T = 12`, setup time `1` and uncertainty `1/2`, the
slow path settles in time: `g2` holds its final value from `12 - 1 - 1/2` on. -/
example : ∀ t : ℝ, 12 - 1 - 1/2 ≤ t → s2 x₁ t = false := by
  intro t ht
  rw [s2_eq, x₁, x₁, decide_eq_true (by linarith), decide_eq_true (by linarith)]
  rfl

/-- **Hold at the boundary.** With `hold + u = 1 + 1/2 = tqMin + earliest_path`, the
certificate gives hold. -/
example : HoldMet (s2 x₁) 1 (1/2) :=
  circ.holdMet_of_le_outputEarliests cdelay (fun _ => x₁) (gSig x₁) 1 1 (1/2)
    (prog_causal x₁ x₁_settled) launch_stable₁ 0
    (cert_zero _ _ _ (by norm_num))

/-- The boundary is attained: the bypass changes `g2` at `3/2`, so any longer hold window
fails. -/
example : ¬ HoldMet (s2 x₁) 1 (3/4) := by
  intro h
  have := h 0 (3/2) le_rfl (by norm_num) (by rw [WithTop.coe_lt_coe]; norm_num)
    (by rw [WithTop.coe_lt_coe]; norm_num)
  rw [s2_of_lt (by norm_num), s2_eq, x₁, x₁] at this
  norm_num at this

/-- **Hold fails.** With `hold = 2` and `u = 1/2` the certificate fails, and the hold check
really fails: `g2` changes at `3/2`, although the slow path settles only at `19/2`. -/
example : ¬ ((2 + 1/2 : ℝ) : WithTop ℝ) ≤
    ((1 : ℝ) : WithTop ℝ) + circ.outputEarliests cdelay (fun _ => 0) 0 := by
  rw [outputEarliests_zero, ← WithTop.coe_add, WithTop.coe_le_coe]
  norm_num

example : ¬ HoldMet (s2 x₁) 2 (1/2) := by
  intro h
  have := h 0 2 le_rfl (by norm_num) (by rw [WithTop.coe_lt_coe]; norm_num)
    (by rw [WithTop.coe_lt_coe]; norm_num)
  rw [s2_of_lt (by norm_num), s2_eq, x₁, x₁] at this
  norm_num at this

/-- **No-transition output.** The constant meets any hold requirement. -/
example : HoldMet s3 100 (1/2) :=
  circ.holdMet_of_le_outputEarliests cdelay (fun _ => x₁) (gSig x₁) 1 100 (1/2)
    (prog_causal x₁ x₁_settled) launch_stable₁ 1
    (by rw [outputEarliests_one, WithTop.add_top]; exact le_top)

/-! ### Repeated launches: hold constrains only the window after the edge -/

/-- Hold says nothing before the edge: a signal that changed at `-1` and is constant on
`[0, 1)` meets a one-second hold check. -/
example : HoldMet (fun t : ℝ => decide (-1 ≤ t)) 1 0 := by
  intro t₁ t₂ h₀₁ h₀₂ _ _
  simp [show (-1 : ℝ) ≤ t₁ by linarith, show (-1 : ℝ) ≤ t₂ by linarith]

/-- The launching register's output over two cycles: launched at `-11` by the previous edge
at `-12`, and at `1` by the edge at `0`. -/
private noncomputable def x₂ (t : ℝ) : Bool := decide (-11 ≤ t) ^^ decide (1 ≤ t)

private theorem x₂_settled (t : ℝ) (ht₀ : -17/2 ≤ t) (ht : t ≤ 0) : x₂ t = x₂ 0 := by
  simp [x₂, show (-11 : ℝ) ≤ t by linarith, show ¬ 1 ≤ t by linarith]

private theorem launch_stable₂ : ∀ _ : Fin 1, StableBefore x₂ ((1 : ℝ) : WithTop ℝ) := by
  intro _ t₁ t₂ h₀₁ h₀₂ h₁ h₂
  rw [WithTop.coe_lt_coe] at h₁ h₂
  simp [x₂, show (-11 : ℝ) ≤ t₁ by linarith, show (-11 : ℝ) ≤ t₂ by linarith,
    not_le.mpr h₁, not_le.mpr h₂]

/-- `g2` carries the previous cycle's transition: it changes at `-5/2`, before the edge. -/
example : s2 x₂ (-3) ≠ s2 x₂ 0 := by
  rw [s2_eq, s2_eq]
  norm_num [x₂]

/-- **Hold over repeated launches.** The same certificate gives hold although `g2` changed
during the previous cycle. -/
example : HoldMet (s2 x₂) 1 (1/2) :=
  circ.holdMet_of_le_outputEarliests cdelay (fun _ => x₂) (gSig x₂) 1 1 (1/2)
    (prog_causal x₂ x₂_settled) launch_stable₂ 0
    (cert_zero _ _ _ (by norm_num))

/-! ### Capture: the pre-edge premise is separate -/

/-- **Capture with a single launch.** `g2` has been `false` since long before the edge, so the
capture certificate gives one value on `[-3/2, 3/2)`. -/
example : CaptureMet (s2 x₁) 1 1 (1/2) :=
  circ.captureMet_of_le_outputEarliests cdelay (fun _ => x₁) (gSig x₁) 1 1 1 (1/2)
    (prog_causal x₁ x₁_settled) launch_stable₁ 0
    (fun t _ ht => (s2_of_lt (by linarith)).trans (s2_of_lt (by norm_num)).symm)
    (cert_zero _ _ _ (by norm_num))

/-- `g2` over repeated launches has settled `5/2` seconds before the edge. -/
private theorem s2_x₂_settled (δ : ℝ≥0) (hδ : (δ : ℝ) ≤ 5/2) : SettledBefore (s2 x₂) δ := by
  have hx : ∀ r : ℝ, -11 ≤ r → r < 1 → x₂ r = true := fun r h₁ h₂ => by
    rw [x₂, decide_eq_true h₁, decide_eq_false (not_le.mpr h₂)]
    rfl
  intro t h₁ h₂
  have h₁ : -5/2 ≤ t := by linarith
  rw [s2_eq, s2_eq, hx (t - 17/2) (by linarith) (by linarith), hx (t - 1/2) (by linarith)
    (by linarith), hx (0 - 17/2) (by norm_num) (by norm_num),
    hx (0 - 1/2) (by norm_num) (by norm_num)]

/-- **Capture over repeated launches.** With setup `2` and uncertainty `1/2` the window opens at
`-5/2`, exactly where `g2` last changed, and the capture certificate applies. -/
example : CaptureMet (s2 x₂) 2 1 (1/2) :=
  circ.captureMet_of_le_outputEarliests cdelay (fun _ => x₂) (gSig x₂) 1 2 1 (1/2)
    (prog_causal x₂ x₂_settled) launch_stable₂ 0 (s2_x₂_settled _ (by norm_num))
    (cert_zero _ _ _ (by norm_num))

/-- **Uncertainty widens the setup side.** With setup `9/4` and uncertainty `1/2` the window opens
at `-11/4`, so the change of `g2` at `-5/2` falls inside it, although it is outside `[-9/4, 0]`. -/
example : ¬ CaptureMet (s2 x₂) (9/4) 1 (1/2) := by
  intro h
  have := h (-21/8) (by norm_num) (by rw [WithTop.coe_lt_coe]; norm_num)
  rw [s2_eq, s2_eq] at this
  norm_num [x₂] at this

/-- A signal that changes at `-5/4` and is stable afterward: with setup `1` and uncertainty `1/2`
the change lies in the setup aperture `[-3/2, 0]`, so capture fails, although the signal is
constant on `[-1, 1/2)`. -/
example : ¬ CaptureMet (fun t : ℝ => decide (-5/4 ≤ t)) 1 0 (1/2) := fun h => by
  have := h (-3/2) (by norm_num) (by rw [WithTop.coe_lt_coe]; norm_num)
  norm_num at this

example : ∀ t : ℝ, -1 ≤ t → t < 1/2 → decide (-5/4 ≤ t) = decide (-5/4 ≤ (0 : ℝ)) :=
  fun t h _ => decide_eq_decide.mpr ⟨fun _ => by norm_num, fun _ => by linarith⟩

/-- **The setup side can fail while hold passes.** `g2` changes at `-5/2`, inside a
three-second setup window, so capture fails although hold holds. -/
example : ¬ CaptureMet (s2 x₂) 3 1 (1/2) := by
  intro h
  have := h (-3) (by norm_num) (by rw [WithTop.coe_lt_coe]; norm_num)
  rw [s2_eq, s2_eq] at this
  norm_num [x₂] at this

/-- A signal that changes exactly at the edge. -/
private noncomputable def edgeSig (t : ℝ) : Bool := decide (0 ≤ t)

/-- **The causal model says nothing before the edge.** A gate whose output changes exactly at
the edge obeys the model for any nonnegative delay, whatever it reads. -/
example (W : Wire 1 0 → ℝ → Bool) (d : ℝ) (hd : 0 ≤ d) :
    (bufLine (.input 0) : Line σ2 1 0).Causal W d edgeSig :=
  ⟨hd, fun _ _ t₁ t₂ h₀₁ h₀₂ _ _ => by simp [edgeSig, h₀₁, h₀₂]⟩

/-- Such a signal meets hold, but it was not settled before the edge, so capture fails. -/
example : HoldMet edgeSig 1 0 := fun t₁ t₂ h₀₁ h₀₂ _ _ => by simp [edgeSig, h₀₁, h₀₂]

example (δ : ℝ≥0) (hδ : 0 < δ) : ¬ SettledBefore edgeSig δ := fun h => by
  have hδ' : (0 : ℝ) < δ := hδ
  have := h (-δ) le_rfl (by linarith)
  simp [edgeSig, not_le.mpr (neg_lt_zero.mpr hδ')] at this

example : ¬ CaptureMet edgeSig 1 1 0 := fun h => by
  have := h (-1) (by norm_num) (by rw [WithTop.coe_lt_coe]; norm_num)
  norm_num [edgeSig] at this

/-! ### Violated premises -/

/-- A launch at `-8`, too late for the slow path to settle before the edge, changes `g2` at
`1/2`. The launch premise still holds after the edge. -/
private noncomputable def x₃ (t : ℝ) : Bool := decide (-8 ≤ t) ^^ decide (1 ≤ t)

private theorem launch_stable₃ : ∀ _ : Fin 1, StableBefore x₃ ((1 : ℝ) : WithTop ℝ) := by
  intro _ t₁ t₂ h₀₁ h₀₂ h₁ h₂
  rw [WithTop.coe_lt_coe] at h₁ h₂
  simp [x₃, show (-8 : ℝ) ≤ t₁ by linarith, show (-8 : ℝ) ≤ t₂ by linarith,
    not_le.mpr h₁, not_le.mpr h₂]

private theorem not_holdMet₃ : ¬ HoldMet (s2 x₃) 1 (1/2) := by
  intro h
  have := h 0 1 le_rfl (by norm_num) (by rw [WithTop.coe_lt_coe]; norm_num)
    (by rw [WithTop.coe_lt_coe]; norm_num)
  rw [s2_eq, s2_eq] at this
  norm_num [x₃] at this

/-- **Late launch.** A circuit still settling at the edge can violate the causal model: these
signals violate it, since otherwise the certificate would give the hold check that fails. -/
example : ¬ prog.Causal cdelay (fun _ => x₃) (gSig x₃) := fun hcausal =>
  not_holdMet₃ (circ.holdMet_of_le_outputEarliests cdelay (fun _ => x₃) (gSig x₃) 1 1 (1/2)
    hcausal launch_stable₃ 0 (cert_zero _ _ _ (by norm_num)))

/-- **Negative delays are not causal.** A gate with contamination delay `-1` never obeys the
model, whatever its signals. -/
example (W : Wire 1 3 → ℝ → Bool) (out : ℝ → Bool) :
    ¬ (conLine true : Line σ2 1 3).Causal W (-1) out := fun h => by
  have := h.1
  norm_num at this

end Cslib.Circuits
