/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Synchronous consensus with crash failures
-/
module

public import Mathlib.Data.Fintype.EquivFin

/-!
# Synchronous consensus with crash failures

A model of synchronous round-based message passing in which processes may crash, and the
consensus problem in it, after Aguilera and Toueg. The theorem that consensus tolerating `f`
crashes needs `f + 1` rounds when `n ≥ f + 2` is proved in
`CSLibExt.Computability.Distributed.CrashConsensusRounds`; this file proves its case `f = 0`
(one round is needed when there are two processes), which that proof uses.

## Model

* **Synchrony:** lock-step rounds `0, 1, …`. In round `r` every process sends one message to
  every process (itself included), receives the messages sent to it in that round, and updates
  its state.
* **Failures:** crash (stopping) failures. A crash pattern assigns to each faulty process `j` a
  round `ρ` and a set `D` of processes: `j` sends all its messages in the rounds before `ρ`, in
  round `ρ` only its messages to the processes of `D` are delivered, and after round `ρ` none
  is. A process with no crash is correct. Faulty processes are not required to decide.
* **Communication:** a complete network of reliable links; a receiver sees, for each sender,
  either its message or nothing (`none`), and knows the sender.
* **Protocols:** deterministic, with one state type for all processes; every process decides
  after a fixed number `T` of rounds.
* **Consensus** (Aguilera and Toueg, §1): agreement (no two correct processes decide
  differently) and validity (a value decided by a correct process is the input of some
  process). Termination is built in: every correct process decides at the end of round `T`.

## Main definitions

* `CrashProtocol G V σ M`, `CrashPattern G`, `CrashPattern.delivers`.
* `CrashProtocol.state`, `CrashProtocol.decision`, `CrashProtocol.Solves`.

## Main results

* `CrashProtocol.not_solves_zero`: with at least two processes and two values, no protocol
  solves consensus in zero rounds, even with no crash.

## References

* M. K. Aguilera, S. Toueg, *A simple bivalency proof that t-resilient consensus requires
  t + 1 rounds*, Information Processing Letters 71(3–4), 1999, 155–158: §1 (model and
  problem), Theorem 1.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Distributed.CrashConsensus

/-- **Synchronous protocol with crash failures.** A protocol for the processes `G` with inputs in
`V`, local states `σ` and messages `M`. Process `i` starts in state `init i x` from its input
`x`; in round `r` process `j` in state `s` sends `send r j s i` to process `i`, and process `i` in
state `s` moves to `recv r i s msg`, where `msg j` is the message it received from `j`, or `none`
if it received none; at the end process `i` decides `decide i s`. -/
structure CrashProtocol (G V σ M : Type*) where
  /-- The initial state of each process, given its input. -/
  init : G → V → σ
  /-- `send r j s i` is the message process `j`, in state `s`, sends to `i` in round `r`. -/
  send : ℕ → G → σ → G → M
  /-- `recv r i s msg` is the state of process `i` after round `r`, from its state `s` and the
  message `msg j` it received from each process `j` (`none` if it received none). -/
  recv : ℕ → G → σ → (G → Option M) → σ
  /-- `decide i s` is the value process `i` decides in its final state `s`. -/
  decide : G → σ → V

/-- **Crash pattern.** `π j = some (ρ, D)` when process `j` crashes in round `ρ`, its messages of
that round reaching exactly the processes of `D`; `π j = none` when `j` is correct. -/
abbrev CrashPattern (G : Type*) := G → Option (ℕ × Finset G)

namespace CrashPattern

variable {G : Type*} [DecidableEq G]

/-- **Message delivery under a crash pattern.** Whether the message of `j` to `i` in round `r` is
delivered: always if `j` is correct; if `j` crashes in round `ρ` with recipients `D`, exactly
when `r < ρ`, or `r = ρ` and `i ∈ D`. -/
def delivers (π : CrashPattern G) (r : ℕ) (j i : G) : Bool :=
  match π j with
  | none => true
  | some (ρ, D) => decide (r < ρ) || (decide (r = ρ) && decide (i ∈ D))

/-- **Faulty processes of a crash pattern.** The processes that crash. -/
def faulty [Fintype G] (π : CrashPattern G) : Finset G :=
  Finset.univ.filter fun j => (π j).isSome

/-- **A correct process delivers every message.** If `π j = none`, every message of `j` is
delivered. -/
theorem delivers_of_eq_none {π : CrashPattern G} {j : G} (h : π j = none) (r : ℕ) (i : G) :
    π.delivers r j i = true := by
  simp [delivers, h]

end CrashPattern

namespace CrashProtocol

variable {G V σ M : Type*} (Q : CrashProtocol G V σ M) [DecidableEq G]

/-- **Executions under crash failures.** `Q.state x π r i` is the state of process `i` after `r`
rounds of `Q` with inputs `x` and crash pattern `π`. -/
def state (x : G → V) (π : CrashPattern G) : ℕ → G → σ
  | 0, i => Q.init i (x i)
  | r + 1, i => Q.recv r i (state x π r i) fun j =>
      if π.delivers r j i then some (Q.send r j (state x π r j) i) else none

/-- **Decision under crash failures.** The value process `i` decides after `T` rounds. -/
def decision (x : G → V) (π : CrashPattern G) (T : ℕ) (i : G) : V :=
  Q.decide i (Q.state x π T i)

/-- **Solving consensus with crash failures.** `Q` solves consensus tolerating `f` crashes in
`T` rounds: for all inputs and every crash pattern with at most `f` faulty processes, no two
correct processes decide differently (agreement), and the value decided by a correct process
is the input of some process (validity). -/
def Solves [Fintype G] (f T : ℕ) : Prop :=
  ∀ (x : G → V) (π : CrashPattern G), π.faulty.card ≤ f →
    (∀ i j, π i = none → π j = none → Q.decision x π T i = Q.decision x π T j) ∧
      ∀ i, π i = none → ∃ j, x j = Q.decision x π T i

/-- **Consensus needs a round** (the case `f = 0` of the `f + 1` round lower bound of Aguilera
and Toueg, 1999, Theorem 1). With at least two processes and at least two values, no protocol
solves consensus in zero rounds, even when no process crashes: each process would decide a
function of its own input. -/
theorem not_solves_zero [Fintype G] [Nontrivial V] (hG : 2 ≤ Fintype.card G) (f : ℕ) :
    ¬ Q.Solves f 0 := by
  intro hQ
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card G)
  obtain ⟨v, w, hvw⟩ := exists_pair_ne V
  have hnone : (CrashPattern.faulty (fun _ => none : CrashPattern G)).card ≤ f := by
    simp [CrashPattern.faulty]
  -- With all inputs equal to `u`, process `k` decides `u`.
  have hconst : ∀ (u : V) (k : G), Q.decide k (Q.init k u) = u := by
    intro u k
    obtain ⟨l, hl⟩ := (hQ (fun _ => u) _ hnone).2 k rfl
    exact hl.symm
  -- With input `v` at `i` and `w` elsewhere, `i` and `j` disagree.
  have h := (hQ (fun k => if k = i then v else w) _ hnone).1 i j rfl rfl
  simp only [decision, state, ite_true, hij.symm, ite_false, hconst] at h
  exact hvw h

end CrashProtocol

end Cslib.Distributed.CrashConsensus
