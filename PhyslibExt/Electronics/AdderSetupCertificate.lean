/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Circuit.AnnotatedArrival
public import CSLibExt.Computability.Circuit.Arithmetic.CarryLookahead

/-!
# Setup-timing certificates for the ripple-carry and carry-lookahead adders

## i. Overview

A register-to-register path through a combinational circuit is launched by a
clock edge at time `0` and captured by the next edge at the clock period `T`
(all times in seconds). The circuit inputs are the launching register's
outputs, which settle no later than its clock-to-Q bound `tq`. Every gate has
a real delay, and output arrival times are those of the gate-delay model
`Cslib.Circuits.Circuit.outputArrivals`: a gate settles at its delay plus the
latest arrival among the wires it reads. The capturing register's setup
constraint is met (`SetupMet`) when every designated output settles at least
the setup time `ts` plus the clock uncertainty `u` before the capturing edge.

If every delay lies in `[0, D]` and `0 ≤ tq`, the depth bound of the
gate-delay model gives the setup certificate
`tq + D * depth + ts + u ≤ T → SetupMet` (`setupMet_of_depth`). At the exact
depths of the existing adders, `2 n + 1` for the `n`-bit ripple-carry adder
(`1 ≤ n`) and `2 K + 3` for the `n`-bit Kogge-Stone carry-lookahead adder with
`K` prefix levels (`1 ≤ K`, `2 ≤ n`; `2 log₂ n + 5` with `claLevels n` levels),
this gives `rippleCarryAdder_setupMet`, `carryLookaheadAdder_setupMet` and
`carryLookaheadAdder_claLevels_setupMet`.

Under uniform gate delays the certificate is exact for every circuit without
constant gates (`setupMet_uniform_iff_of_noConstantGates`, its signature-wide
form `setupMet_uniform_iff`, and the two adder `_uniform_iff` forms): a
violated certificate is a real setup violation of the model, whether or not
the adder computes the right sum. A constant gate settles at its delay alone
while counting one level of depth, so exactness needs the premise.

Delays are premises of the model, not extracted silicon timing; unit depth is
not physical latency; hold timing, clock-domain crossing and glitches are out
of scope.

## ii. Key results

- `setupMet_of_depth`: the setup certificate for any circuit.
- `rippleCarryAdder_setupMet`, `carryLookaheadAdder_setupMet`,
  `carryLookaheadAdder_claLevels_setupMet`: the certificates for the two
  adders at their width hypotheses.
- `outputArrivals_uniform_of_noConstantGates`,
  `setupMet_uniform_iff_of_noConstantGates`: exactness under uniform delays
  for a circuit whose gates all read at least one wire.
- `outputArrivals_uniform`, `setupMet_uniform_iff`,
  `rippleCarryAdder_setupMet_uniform_iff`,
  `carryLookaheadAdder_setupMet_uniform_iff`: the same for a signature
  without constants, and for the two adders.

## iii. Table of contents

- A. The setup timing model
- B. The setup certificate
- C. Adder certificates
- D. Exactness under uniform delays

## iv. References

- D. M. Harris and S. L. Harris, *Digital Design and Computer Architecture*,
  second edition, Morgan Kaufmann, 2012: Section 3.5 (timing of sequential
  logic, the setup constraint `tpcq + tpd + tsetup ≤ Tc`, clock skew) and
  Section 5.2.1 (ripple-carry and carry-lookahead adders).
- P. M. Kogge and H. S. Stone, "A Parallel Algorithm for the Efficient
  Solution of a General Class of Recurrence Equations", *IEEE Transactions on
  Computers* C-22 (1973), 786–793.
-/

@[expose] public section

namespace PhyslibExt.Electronics.AdderSetupCertificate

open Cslib.Circuits

universe v

/-! ## A. The setup timing model -/

/-- **Setup timing model.** One register-to-register path through the
circuit `c`: a clock edge at time `0` launches it and the next edge, at the
period `T`, captures it. The circuit inputs (the launching register's
outputs) settle at `inputArrival`, gate `j` has delay `delay j`, and output
arrival times are those of the gate-delay model. The capturing register's
setup constraint holds when every designated output settles at least the
setup time `ts` plus the clock uncertainty `u` before the capturing edge. -/
def SetupMet {σ : Signature.{v}} {inputCount outputCount : ℕ}
    (c : Circuit σ inputCount outputCount) (delay : Fin c.size → ℝ)
    (inputArrival : Fin inputCount → ℝ) (ts u T : ℝ) : Prop :=
  ∀ o, c.outputArrivals delay inputArrival o + ts + u ≤ T

/-! ## B. The setup certificate -/

/-- **Setup certificate.** If every gate delay lies in `[0, D]`, the launching
register's outputs settle by the clock-to-Q bound `tq ≥ 0`, and
`tq + D * depth + ts + u ≤ T`, the setup constraint is met. -/
theorem setupMet_of_depth {σ : Signature.{v}} {inputCount outputCount : ℕ}
    (c : Circuit σ inputCount outputCount) (delay : Fin c.size → ℝ)
    (inputArrival : Fin inputCount → ℝ) (tq D ts u T : ℝ)
    (htq : 0 ≤ tq) (hinput : ∀ i, inputArrival i ≤ tq)
    (hdelay_nonneg : ∀ j, 0 ≤ delay j) (hdelay_le : ∀ j, delay j ≤ D)
    (hcert : tq + D * (c.depth : ℝ) + ts + u ≤ T) :
    SetupMet c delay inputArrival ts u T := by
  intro o
  have h := Circuit.outputArrivals_le_add_mul_depth c delay inputArrival tq D htq hinput
    hdelay_nonneg hdelay_le o
  exact le_trans (add_le_add_left (add_le_add_left h ts) u) hcert

/-! ## C. Adder certificates -/

/-- **Ripple-carry certificate.** For `n ≥ 1` bits the adder has depth
`2 n + 1`, so `tq + D * (2 n + 1) + ts + u ≤ T` certifies setup. -/
lemma rippleCarryAdder_setupMet (n : ℕ) (hn : 1 ≤ n)
    (delay : Fin (rippleCarryAdder n).size → ℝ) (inputArrival : Fin (2 * n + 1) → ℝ)
    (tq D ts u T : ℝ) (htq : 0 ≤ tq) (hinput : ∀ i, inputArrival i ≤ tq)
    (hdelay_nonneg : ∀ j, 0 ≤ delay j) (hdelay_le : ∀ j, delay j ≤ D)
    (hcert : tq + D * ((2 * n + 1 : ℕ) : ℝ) + ts + u ≤ T) :
    SetupMet (rippleCarryAdder n) delay inputArrival ts u T := by
  refine setupMet_of_depth _ _ _ _ _ _ _ _ htq hinput hdelay_nonneg hdelay_le ?_
  rw [rippleCarryAdder_depth hn]
  exact hcert

/-- **Carry-lookahead certificate.** With `K ≥ 1` Kogge-Stone levels and
`n ≥ 2` bits the adder has depth `2 K + 3`, so
`tq + D * (2 K + 3) + ts + u ≤ T` certifies setup. -/
lemma carryLookaheadAdder_setupMet (n K : ℕ) (hK : 1 ≤ K) (hn : 2 ≤ n)
    (delay : Fin (CarryLookahead.carryLookaheadAdder n K).size → ℝ)
    (inputArrival : Fin (2 * n + 1) → ℝ)
    (tq D ts u T : ℝ) (htq : 0 ≤ tq) (hinput : ∀ i, inputArrival i ≤ tq)
    (hdelay_nonneg : ∀ j, 0 ≤ delay j) (hdelay_le : ∀ j, delay j ≤ D)
    (hcert : tq + D * ((2 * K + 3 : ℕ) : ℝ) + ts + u ≤ T) :
    SetupMet (CarryLookahead.carryLookaheadAdder n K) delay inputArrival ts u T := by
  refine setupMet_of_depth _ _ _ _ _ _ _ _ htq hinput hdelay_nonneg hdelay_le ?_
  rw [CarryLookahead.carryLookaheadAdder_depth hK hn]
  exact hcert

/-- **Carry-lookahead certificate at `claLevels n` levels.** For `n ≥ 2`
bits, `tq + D * (2 log₂ n + 5) + ts + u ≤ T` certifies setup. -/
lemma carryLookaheadAdder_claLevels_setupMet (n : ℕ) (hn : 2 ≤ n)
    (delay : Fin (CarryLookahead.carryLookaheadAdder n
      (CarryLookahead.claLevels n)).size → ℝ)
    (inputArrival : Fin (2 * n + 1) → ℝ)
    (tq D ts u T : ℝ) (htq : 0 ≤ tq) (hinput : ∀ i, inputArrival i ≤ tq)
    (hdelay_nonneg : ∀ j, 0 ≤ delay j) (hdelay_le : ∀ j, delay j ≤ D)
    (hcert : tq + D * ((2 * Nat.log2 n + 5 : ℕ) : ℝ) + ts + u ≤ T) :
    SetupMet (CarryLookahead.carryLookaheadAdder n (CarryLookahead.claLevels n))
      delay inputArrival ts u T := by
  refine setupMet_of_depth _ _ _ _ _ _ _ _ htq hinput hdelay_nonneg hdelay_le ?_
  rw [CarryLookahead.carryLookaheadAdder_depth_claLevels hn]
  exact hcert

/-! ## D. Exactness under uniform delays -/

/-- Every gate of the program reads at least one wire: no gate of `p` is a
constant. Only the operations the program uses matter; the signature may
also offer constants. -/
def NoConstantGates {σ : Signature.{v}} {m : ℕ} : {g : ℕ} → Program σ m g → Prop
  | _, .empty => True
  | _, .gate p line => NoConstantGates p ∧ 0 < σ.Arity line.op

/-- A signature without constants admits no constant gate. -/
lemma noConstantGates_of_arity_pos {σ : Signature.{v}} {m : ℕ} (hσ : ∀ op, 0 < σ.Arity op) :
    ∀ {g : ℕ} (p : Program σ m g), NoConstantGates p
  | _, .empty => trivial
  | _, .gate p line => ⟨noConstantGates_of_arity_pos hσ p, hσ line.op⟩

/-- The fold-max from `0` of the values `a0 + D * f k` over a nonempty index
type is `a0 + D` times the fold-max of `f`. -/
private lemma foldl_max_add_mul : ∀ {n : ℕ} (f : Fin n → ℕ) (a0 D : ℝ),
    0 ≤ a0 → 0 ≤ D → 0 < n →
    Fin.foldl n (fun t k => max t (a0 + D * (f k : ℝ))) 0
      = a0 + D * ((Fin.foldl n (fun d k => max d (f k)) 0 : ℕ) : ℝ) := by
  intro n
  induction n with
  | zero => intro f a0 D ha0 hD hn; omega
  | succ n ih =>
    intro f a0 D ha0 hD hn
    simp only [Fin.foldl_succ_last]
    by_cases hn0 : n = 0
    · subst hn0
      simp only [Fin.foldl_zero]
      have hV : (0 : ℝ) ≤ a0 + D * ((f (Fin.last 0) : ℕ) : ℝ) :=
        add_nonneg ha0 (mul_nonneg hD (Nat.cast_nonneg _))
      rw [max_eq_right hV, max_eq_right (Nat.zero_le _)]
    · have hih : Fin.foldl n (fun t k => max t (a0 + D * ((f k.castSucc : ℕ) : ℝ))) 0
          = a0 + D * ((Fin.foldl n (fun d k => max d (f k.castSucc)) 0 : ℕ) : ℝ) :=
        ih _ _ _ ha0 hD (Nat.pos_of_ne_zero hn0)
      rw [hih, Nat.cast_max]
      have hmono : Monotone (fun x : ℝ => a0 + D * x) := fun x y h =>
        add_le_add_right (mul_le_mul_of_nonneg_left h hD) a0
      exact (Monotone.map_max hmono).symm

/-- The fold-max from `0` over a nonempty index type is attained. -/
private lemma foldl_max_attained : ∀ {n : ℕ} (f : Fin n → ℕ), 0 < n →
    ∃ k, Fin.foldl n (fun d i => max d (f i)) 0 = f k := by
  intro n
  induction n with
  | zero => intro f hn; omega
  | succ n ih =>
    intro f hn
    simp only [Fin.foldl_succ_last]
    by_cases h : Fin.foldl n (fun d i => max d (f i.castSucc)) 0 ≤ f (Fin.last n)
    · exact ⟨Fin.last n, max_eq_right h⟩
    · simp only [not_le] at h
      by_cases hn0 : n = 0
      · subst hn0
        simp only [Fin.foldl_zero] at h
        omega
      · obtain ⟨i, hi⟩ := ih (fun j => f j.castSucc) (Nat.pos_of_ne_zero hn0)
        have hi' : Fin.foldl n (fun d i => max d (f i.castSucc)) 0 = f i.castSucc := hi
        exact ⟨i.castSucc, by rw [max_eq_left (le_of_lt h), hi']⟩

/-- Uniform wire arrivals follow from uniform gate arrivals. -/
private lemma wireArrivals_uniform {σ : Signature.{v}} {m g : ℕ} (p : Program σ m g)
    (a0 D : ℝ)
    (hall : ∀ j, p.arrivals (fun _ => D) (fun _ => a0) j
      = a0 + D * ((p.depths j : ℕ) : ℝ))
    (w : Wire m g) :
    p.wireArrivals (fun _ => D) (fun _ => a0) w
      = a0 + D * ((p.wireDepths w : ℕ) : ℝ) := by
  cases w with
  | input i => simp [Program.wireArrivals, Program.wireDepths, Wire.elim]
  | gate i =>
    simp only [Program.wireArrivals, Program.wireDepths, Wire.elim]
    exact hall i

/-- Under uniform delays every gate arrives at `a0 + D` times its depth. -/
private lemma arrivals_uniform_gate : ∀ {σ : Signature.{v}} {m g : ℕ} (p : Program σ m g)
    (_hp : NoConstantGates p) (a0 D : ℝ) (_ha0 : 0 ≤ a0) (_hD : 0 ≤ D) (j : Fin g),
    p.arrivals (fun _ => D) (fun _ => a0) j = a0 + D * ((p.depths j : ℕ) : ℝ) := by
  intro σ m g p
  induction p with
  | empty =>
    intro _ a0 D _ _ j
    exact Fin.elim0 j
  | gate p line ih =>
    intro hp a0 D ha0 hD j
    obtain ⟨hp, hop⟩ := hp
    refine Fin.lastCases ?_ ?_ j
    · simp only [Program.arrivals_gate_last, Program.depths_gate_last, Line.arrival,
        Line.depth]
      have hwire : ∀ k, p.wireArrivals (fun _ => D) (fun _ => a0) (line.wires k)
          = a0 + D * ((p.wireDepths (line.wires k) : ℕ) : ℝ) :=
        fun k => wireArrivals_uniform p a0 D (fun j => ih hp a0 D ha0 hD j) (line.wires k)
      simp only [hwire]
      have hfold : Fin.foldl (σ.Arity line.op)
            (fun t k => max t (a0 + D * ((p.wireDepths (line.wires k) : ℕ) : ℝ))) 0
          = a0 + D * ((Fin.foldl (σ.Arity line.op)
            (fun d k => max d (p.wireDepths (line.wires k))) 0 : ℕ) : ℝ) :=
        foldl_max_add_mul _ _ _ ha0 hD hop
      rw [hfold, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, mul_add, mul_one]
      ac_rfl
    · intro i
      simp only [Program.arrivals_gate_castSucc, Program.depths_gate_castSucc]
      exact ih hp a0 D ha0 hD i

/-- The circuit depth is attained by some designated output. -/
private lemma depth_attained {σ : Signature.{v}} {m n : ℕ} (c : Circuit σ m n)
    (hn : 0 < n) : ∃ o, c.outputDepths o = c.depth := by
  obtain ⟨k, hk⟩ := foldl_max_attained (fun o => c.outputDepths o) hn
  exact ⟨k, hk.symm⟩

/-- For a circuit without constant gates, uniform delay `D ≥ 0` and every
input arriving at `a0 ≥ 0`, every designated output arrives exactly at
`a0 + D` times its depth. -/
lemma outputArrivals_uniform_of_noConstantGates {σ : Signature.{v}}
    {inputCount outputCount : ℕ} (c : Circuit σ inputCount outputCount)
    (hc : NoConstantGates c.program) (a0 D : ℝ) (ha0 : 0 ≤ a0) (hD : 0 ≤ D)
    (o : Fin outputCount) :
    c.outputArrivals (fun _ => D) (fun _ => a0) o = a0 + D * (c.outputDepths o : ℝ) :=
  wireArrivals_uniform c.program a0 D (arrivals_uniform_gate c.program hc a0 D ha0 hD)
    (c.outputs o)

/-- **The certificate is exact under uniform delays.** For a circuit with at
least one output and no constant gate, uniform delay `D ≥ 0` and inputs
settling at `tq ≥ 0`, setup holds iff `tq + D * depth + ts + u ≤ T`. -/
lemma setupMet_uniform_iff_of_noConstantGates {σ : Signature.{v}}
    {inputCount outputCount : ℕ} (c : Circuit σ inputCount outputCount)
    (hc : NoConstantGates c.program) (hout : 0 < outputCount) (tq D ts u T : ℝ)
    (htq : 0 ≤ tq) (hD : 0 ≤ D) :
    SetupMet c (fun _ => D) (fun _ => tq) ts u T ↔
      tq + D * (c.depth : ℝ) + ts + u ≤ T := by
  constructor
  · intro h
    obtain ⟨o, ho⟩ := depth_attained c hout
    have harr := outputArrivals_uniform_of_noConstantGates c hc tq D htq hD o
    rw [ho] at harr
    have ho' := h o
    rw [harr] at ho'
    exact ho'
  · intro hcert o
    have hmul : D * ((c.outputDepths o : ℕ) : ℝ) ≤ D * (c.depth : ℝ) :=
      mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (c.outputDepths_le_depth o)) hD
    have h1 : tq + D * ((c.outputDepths o : ℕ) : ℝ) + ts + u
        ≤ tq + D * (c.depth : ℝ) + ts + u :=
      add_le_add_left (add_le_add_left (add_le_add (le_refl tq) hmul) ts) u
    rw [outputArrivals_uniform_of_noConstantGates c hc tq D htq hD o]
    exact le_trans h1 hcert

/-- With every operation of the signature taking at least one argument,
uniform delay `D ≥ 0` and every input arriving at `a0 ≥ 0`, every designated
output arrives exactly at `a0 + D` times its depth. For a signature that
also offers constants, use `outputArrivals_uniform_of_noConstantGates`. -/
lemma outputArrivals_uniform {σ : Signature.{v}} {inputCount outputCount : ℕ}
    (hσ : ∀ op, 0 < σ.Arity op) (c : Circuit σ inputCount outputCount)
    (a0 D : ℝ) (ha0 : 0 ≤ a0) (hD : 0 ≤ D) (o : Fin outputCount) :
    c.outputArrivals (fun _ => D) (fun _ => a0) o = a0 + D * (c.outputDepths o : ℝ) :=
  outputArrivals_uniform_of_noConstantGates c (noConstantGates_of_arity_pos hσ _) a0 D ha0 hD o

/-- **The certificate is exact under uniform delays**, for a signature whose
operations all take an argument. For a circuit with at least one output,
uniform delay `D ≥ 0` and inputs settling at `tq ≥ 0`, setup holds iff
`tq + D * depth + ts + u ≤ T`. For a signature that also offers constants,
use `setupMet_uniform_iff_of_noConstantGates`. -/
lemma setupMet_uniform_iff {σ : Signature.{v}} {inputCount outputCount : ℕ}
    (hσ : ∀ op, 0 < σ.Arity op) (c : Circuit σ inputCount outputCount)
    (hout : 0 < outputCount) (tq D ts u T : ℝ) (htq : 0 ≤ tq) (hD : 0 ≤ D) :
    SetupMet c (fun _ => D) (fun _ => tq) ts u T ↔
      tq + D * (c.depth : ℝ) + ts + u ≤ T :=
  setupMet_uniform_iff_of_noConstantGates c (noConstantGates_of_arity_pos hσ _) hout
    tq D ts u T htq hD

/-- Under uniform delays the ripple-carry setup certificate is exact, so
`T < tq + D * (2 n + 1) + ts + u` is a setup violation. -/
lemma rippleCarryAdder_setupMet_uniform_iff (n : ℕ) (hn : 1 ≤ n)
    (tq D ts u T : ℝ) (htq : 0 ≤ tq) (hD : 0 ≤ D) :
    SetupMet (rippleCarryAdder n) (fun _ => D) (fun _ => tq) ts u T ↔
      tq + D * ((2 * n + 1 : ℕ) : ℝ) + ts + u ≤ T := by
  have hσ : ∀ op, 0 < arithSignature.Arity op := fun _ => two_pos
  rw [setupMet_uniform_iff hσ _ (Nat.succ_pos n) _ _ _ _ _ htq hD, rippleCarryAdder_depth hn]

/-- Under uniform delays the carry-lookahead setup certificate is exact, so
`T < tq + D * (2 K + 3) + ts + u` is a setup violation. -/
lemma carryLookaheadAdder_setupMet_uniform_iff (n K : ℕ) (hK : 1 ≤ K) (hn : 2 ≤ n)
    (tq D ts u T : ℝ) (htq : 0 ≤ tq) (hD : 0 ≤ D) :
    SetupMet (CarryLookahead.carryLookaheadAdder n K) (fun _ => D) (fun _ => tq) ts u T ↔
      tq + D * ((2 * K + 3 : ℕ) : ℝ) + ts + u ≤ T := by
  have hσ : ∀ op, 0 < arithSignature.Arity op := fun _ => two_pos
  rw [setupMet_uniform_iff hσ _ (Nat.succ_pos n) _ _ _ _ _ htq hD,
    CarryLookahead.carryLookaheadAdder_depth hK hn]

end PhyslibExt.Electronics.AdderSetupCertificate
