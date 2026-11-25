/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Circuit.Arithmetic.CarryLookahead
public import CSLibExt.Computability.Circuit.UniformArrival

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

Under uniform gate delays, with every input arriving exactly at `tq`, the
certificate is exact for every circuit without constant gates
(`setupMet_uniform_iff_of_noConstantGates`, its signature-wide form
`setupMet_uniform_iff`, and the two adder `_uniform_iff` forms): a violated
certificate is a real setup violation of the model, whether or not the adder
computes the right sum. Both premises are needed. A constant gate settles at
its delay alone while counting one level of depth. Inputs that only settle by
`tq`, some strictly earlier, can meet setup below the certificate: if every
input arrives at `0`, setup holds as soon as `D * depth + ts + u ≤ T`. The
underlying exact arrival times are generic circuit facts, proved in
`CSLibExt.Computability.Circuit.UniformArrival` and re-exported here.

Delays are premises of the model, not extracted silicon timing; unit depth is
not physical latency; hold timing, clock-domain crossing and glitches are out
of scope.

## ii. Key results

- `setupMet_of_depth`: the setup certificate for any circuit.
- `rippleCarryAdder_setupMet`, `carryLookaheadAdder_setupMet`,
  `carryLookaheadAdder_claLevels_setupMet`: the certificates for the two
  adders at their width hypotheses.
- `setupMet_uniform_iff_of_noConstantGates`: exactness under uniform delays
  and every input arriving exactly at `tq`, for a circuit whose gates all read
  at least one wire.
- `setupMet_uniform_iff`, `rippleCarryAdder_setupMet_uniform_iff`,
  `carryLookaheadAdder_setupMet_uniform_iff`: the same for a signature
  without constants, and for the two adders.
- `NoConstantGates`, `noConstantGates_of_arity_pos`,
  `outputArrivals_uniform_of_noConstantGates`, `outputArrivals_uniform`:
  re-exported from `Cslib.Circuits.Program` and `Cslib.Circuits.Circuit`.

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

/-! The generic circuit facts behind exactness live in
`CSLibExt.Computability.Circuit.UniformArrival`; their names are re-exported
here. -/

export Program (NoConstantGates noConstantGates_of_arity_pos)
export Circuit (outputArrivals_uniform_of_noConstantGates outputArrivals_uniform)

/-- **The certificate is exact under uniform delays.** For a circuit with at
least one output and no constant gate, uniform delay `D ≥ 0` and every input
arriving exactly at `tq ≥ 0`, setup holds iff `tq + D * depth + ts + u ≤ T`.
Inputs that only settle by `tq` can meet setup below the certificate. -/
lemma setupMet_uniform_iff_of_noConstantGates {σ : Signature.{v}}
    {inputCount outputCount : ℕ} (c : Circuit σ inputCount outputCount)
    (hc : NoConstantGates c.program) (hout : 0 < outputCount) (tq D ts u T : ℝ)
    (htq : 0 ≤ tq) (hD : 0 ≤ D) :
    SetupMet c (fun _ => D) (fun _ => tq) ts u T ↔
      tq + D * (c.depth : ℝ) + ts + u ≤ T := by
  constructor
  · intro h
    obtain ⟨o, ho⟩ := c.exists_outputDepths_eq_depth hout
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

/-- **The certificate is exact under uniform delays**, for a signature whose
operations all take an argument. For a circuit with at least one output,
uniform delay `D ≥ 0` and every input arriving exactly at `tq ≥ 0`, setup holds iff
`tq + D * depth + ts + u ≤ T`. For a signature that also offers constants,
use `setupMet_uniform_iff_of_noConstantGates`. -/
lemma setupMet_uniform_iff {σ : Signature.{v}} {inputCount outputCount : ℕ}
    (hσ : ∀ op, 0 < σ.Arity op) (c : Circuit σ inputCount outputCount)
    (hout : 0 < outputCount) (tq D ts u T : ℝ) (htq : 0 ≤ tq) (hD : 0 ≤ D) :
    SetupMet c (fun _ => D) (fun _ => tq) ts u T ↔
      tq + D * (c.depth : ℝ) + ts + u ≤ T :=
  setupMet_uniform_iff_of_noConstantGates c (noConstantGates_of_arity_pos hσ _) hout
    tq D ts u T htq hD

/-- Under uniform delays, with every input arriving exactly at `tq`, the
ripple-carry setup certificate is exact, so `T < tq + D * (2 n + 1) + ts + u`
is a setup violation. -/
lemma rippleCarryAdder_setupMet_uniform_iff (n : ℕ) (hn : 1 ≤ n)
    (tq D ts u T : ℝ) (htq : 0 ≤ tq) (hD : 0 ≤ D) :
    SetupMet (rippleCarryAdder n) (fun _ => D) (fun _ => tq) ts u T ↔
      tq + D * ((2 * n + 1 : ℕ) : ℝ) + ts + u ≤ T := by
  have hσ : ∀ op, 0 < arithSignature.Arity op := fun _ => two_pos
  rw [setupMet_uniform_iff hσ _ (Nat.succ_pos n) _ _ _ _ _ htq hD, rippleCarryAdder_depth hn]

/-- Under uniform delays, with every input arriving exactly at `tq`, the
carry-lookahead setup certificate is exact, so `T < tq + D * (2 K + 3) + ts + u`
is a setup violation. -/
lemma carryLookaheadAdder_setupMet_uniform_iff (n K : ℕ) (hK : 1 ≤ K) (hn : 2 ≤ n)
    (tq D ts u T : ℝ) (htq : 0 ≤ tq) (hD : 0 ≤ D) :
    SetupMet (CarryLookahead.carryLookaheadAdder n K) (fun _ => D) (fun _ => tq) ts u T ↔
      tq + D * ((2 * K + 3 : ℕ) : ℝ) + ts + u ≤ T := by
  have hσ : ∀ op, 0 < arithSignature.Arity op := fun _ => two_pos
  rw [setupMet_uniform_iff hσ _ (Nat.succ_pos n) _ _ _ _ _ htq hD,
    CarryLookahead.carryLookaheadAdder_depth hK hn]

end PhyslibExt.Electronics.AdderSetupCertificate
