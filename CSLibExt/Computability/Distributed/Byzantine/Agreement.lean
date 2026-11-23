/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Byzantine agreement: impossibility with at least a third of the processes faulty
-/
module

public import CSLibExt.Computability.Distributed.Byzantine.Impossibility

/-!
# No synchronous protocol reaches Byzantine agreement when `3 ≤ n ≤ 3 m`

Byzantine agreement in the sense of Fischer, Lynch and Merritt: each of `n` processes has an
input in `V`, the processes exchange messages for a fixed number `T` of synchronous rounds and
each then decides a value. At most `m` processes are faulty, and a faulty process may send
anything to anyone. A protocol reaches Byzantine agreement when, whatever the faulty processes
do,

* (agreement) all correct processes decide the same value, and
* (validity) if all correct processes have the same input, that input is the value decided.

When `3 ≤ n ≤ 3 m` and `V` has two distinct values this is impossible, for any protocol, any
state and message types and any number of rounds. This is the bound on the number of nodes in
Theorem 1 of Fischer, Lynch and Merritt, for the complete communication graph.

## Model

* **Synchrony:** lock-step rounds. In round `r` every process sends one message to every
  process (itself included) and then updates its state from the messages it received.
* **Failures:** Byzantine. A faulty process sends, in each round, an arbitrary message to each
  process, chosen independently for each recipient.
* **Communication:** a complete network of reliable point-to-point links; a receiver knows
  the sender of every message. There are no signatures.
* **Protocols:** deterministic, with one state type for all processes.

## Proof

By reduction to the commander version, `OralProtocol.not_solves_of_card_le_three_mul`, which is
proved by the hexagon argument of Fischer, Lynch and Merritt for three generals and the
simulation argument of Lamport, Shostak and Pease for more. From an agreement protocol `Q` and a
commander `c`, `toOral` builds the oral-message protocol whose first round lets the commander
send its order to every general, after which every general runs `Q` with the order it received
as its input. Agreement of `Q` gives IC1, and validity of `Q` gives IC2: a loyal commander sends
the same order to every loyal general.

Fischer, Lynch and Merritt prove the bound directly by the hexagon argument, in a more general
model (their Locality and Fault axioms) that includes asynchronous systems and arbitrary
communication graphs; their Theorem 1 also requires connectivity at least `2 m + 1`. This file
covers neither the connectivity bound nor models other than synchronous rounds. Its hypothesis
`3 ≤ n` follows their standing assumption that graphs have at least three nodes; the case of two
processes is proved separately by an elementary argument (`not_solves_of_card_eq_two`), so the
bound holds for `2 ≤ n ≤ 3 m`. With one process it fails: deciding one's own input tolerates one
fault.

## Main definitions

* `AgreementProtocol G V σ M`: a synchronous protocol for the processes `G` with inputs in `V`,
  states `σ` and messages `M`.
* `AgreementProtocol.state`: the states of the processes in an execution with given inputs,
  set of faulty processes and messages of the faulty processes.
* `AgreementProtocol.Agreement`, `AgreementProtocol.Validity`, `AgreementProtocol.Solves`.
* `AgreementProtocol.toOral`: the commander protocol built from an agreement protocol, with
  `AgreementProtocol.orderOf` and `AgreementProtocol.msgOf` decoding its messages.

## Main results

* `AgreementProtocol.state_toOral`: the commander protocol simulates the agreement protocol,
  one round later.
* `AgreementProtocol.solves_toOral`: an agreement protocol tolerating `m` faults in `T` rounds
  yields an oral-message protocol solving the Byzantine generals problem with `m` traitors in
  `T + 1` rounds.
* `AgreementProtocol.not_solves_of_card_le_three_mul`: no agreement protocol for `n` processes
  tolerates `m` Byzantine faults when `3 ≤ n ≤ 3 m`.
* `AgreementProtocol.not_solves_three`: the case of three processes and one fault.
* `AgreementProtocol.not_solves_of_card_eq_two`, `AgreementProtocol.not_solves_of_two_le_card`:
  the case of two processes, and the bound for `2 ≤ n ≤ 3 m`.

## References

* M. J. Fischer, N. A. Lynch, M. Merritt, *Easy impossibility proofs for distributed consensus
  problems*, Distributed Computing 1(1), 1986, 26–39: §3 (Byzantine agreement, Theorem 1,
  §3.1 for the number of nodes).
* L. Lamport, R. Shostak, M. Pease, *The Byzantine Generals Problem*, ACM Transactions on
  Programming Languages and Systems 4(3), 1982, 382–401: §2 (impossibility results).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Distributed.Byzantine.AgreementBound

open Cslib.Distributed.Byzantine.Impossibility

/-- **Synchronous Byzantine agreement protocol.** A protocol for the processes `G` with inputs
in `V`, local states `σ` and messages `M`. Process `i` starts in state `init i x` from its input
`x`; in each round `r` every process `j` sends `send r j s i` to every process `i`, where `s` is
its state, and then moves to `recv r i s msg`, where `msg j` is the message it received from
`j`; at the end process `i` decides `decide i s`. -/
structure AgreementProtocol (G V σ M : Type*) where
  /-- The initial state of each process, given its input. -/
  init : G → V → σ
  /-- `send r j s i` is the message process `j`, in state `s`, sends to process `i` in round
  `r`. -/
  send : ℕ → G → σ → G → M
  /-- `recv r i s msg` is the state of process `i` after round `r`, from its state `s` and the
  message `msg j` it received from each process `j`. -/
  recv : ℕ → G → σ → (G → M) → σ
  /-- `decide i s` is the value process `i` decides in its final state `s`. -/
  decide : G → σ → V

namespace AgreementProtocol

variable {G V σ M : Type*} (Q : AgreementProtocol G V σ M) [DecidableEq G]

/-- **Executions of a Byzantine agreement protocol.** `Q.state x faulty adv r i` is the state
of process `i` after `r` rounds of `Q` with inputs `x` and faulty processes `faulty`, where a
faulty process `j` sends `adv r j i` to process `i` in round `r`. Correct processes follow the
protocol. -/
def state (x : G → V) (faulty : Finset G) (adv : ℕ → G → G → M) : ℕ → G → σ
  | 0, i => Q.init i (x i)
  | r + 1, i => Q.recv r i (state x faulty adv r i) fun j =>
      if j ∈ faulty then adv r j i else Q.send r j (state x faulty adv r j) i

/-- **Decision of a process in Byzantine agreement.** The value process `i` decides after `T`
rounds. -/
def decision (x : G → V) (faulty : Finset G) (adv : ℕ → G → G → M) (T : ℕ) (i : G) : V :=
  Q.decide i (Q.state x faulty adv T i)

/-- **Agreement condition of Byzantine agreement.** After `T` rounds all correct processes
decide the same value. -/
def Agreement (x : G → V) (faulty : Finset G) (adv : ℕ → G → G → M) (T : ℕ) : Prop :=
  ∀ i j, i ∉ faulty → j ∉ faulty → Q.decision x faulty adv T i = Q.decision x faulty adv T j

/-- **Validity condition of Byzantine agreement.** If all correct processes have the same
input `v`, then after `T` rounds every correct process decides `v`. -/
def Validity (x : G → V) (faulty : Finset G) (adv : ℕ → G → G → M) (T : ℕ) : Prop :=
  ∀ v, (∀ i, i ∉ faulty → x i = v) → ∀ i, i ∉ faulty → Q.decision x faulty adv T i = v

/-- **Reaching Byzantine agreement.** `Q` reaches Byzantine agreement with at most `m` faulty
processes in `T` rounds: agreement and validity hold for all inputs, every set of at most `m`
faulty processes and every behaviour of the faulty processes. -/
def Solves (m T : ℕ) : Prop :=
  ∀ (x : G → V) (faulty : Finset G), faulty.card ≤ m → ∀ adv : ℕ → G → G → M,
    Q.Agreement x faulty adv T ∧ Q.Validity x faulty adv T

/-! ### Reduction to the Byzantine generals problem -/

/-- **Order carried by a first-round message.** The order a message of `toOral` carries, or
`d` if it carries none. -/
def orderOf (d : V) : Option V ⊕ M → V
  | .inl (some v) => v
  | _ => d

/-- **Protocol message carried by a later message.** The message of the agreement protocol
that a message of `toOral` carries, or `m₀` if it carries none. -/
def msgOf (m₀ : M) : Option V ⊕ M → M
  | .inr m => m
  | _ => m₀

/-- **Byzantine generals from Byzantine agreement.** The oral-message protocol with commander
`c` built from `Q`: in round `0` the commander sends its order to every general, and every
general takes the order it received from `c` as its input to `Q` (`d` if the message carries
no order); in round `r + 1` the generals run round `r` of `Q`. A general decides as in `Q`, or
`d` before the first round. The default message `m₀` replaces messages of the wrong kind,
which only traitors send. -/
def toOral (c : G) (d : V) (m₀ : M) :
    OralProtocol G V (Option V ⊕ σ) (Option V ⊕ M) where
  init _ := .inl none
  initCommander v := .inl (some v)
  send r j s i := match r, s with
    | 0, .inl o => .inl o
    | r + 1, .inr t => .inr (Q.send r j t i)
    | _, _ => .inl none
  recv r i s msg := match r, s with
    | 0, _ => .inr (Q.init i (orderOf d (msg c)))
    | r + 1, .inr t => .inr (Q.recv r i t fun j => msgOf m₀ (msg j))
    | _ + 1, .inl o => .inl o
  decide i s := match s with
    | .inr t => Q.decide i t
    | .inl _ => d

omit [DecidableEq G] in
/-- **Later messages of the commander protocol.** In a round `r + 1`, `toOral` sends the
message of round `r` of the agreement protocol. -/
theorem toOral_send_succ (c : G) (d : V) (m₀ : M) (r : ℕ) (j : G) (t : σ) (i : G) :
    (Q.toOral c d m₀).send (r + 1) j (.inr t) i = .inr (Q.send r j t i) := rfl

omit [DecidableEq G] in
/-- **Later rounds of the commander protocol.** In a round `r + 1`, `toOral` runs round `r` of
the agreement protocol. -/
theorem toOral_recv_succ (c : G) (d : V) (m₀ : M) (r : ℕ) (i : G) (t : σ)
    (msg : G → Option V ⊕ M) :
    (Q.toOral c d m₀).recv (r + 1) i (.inr t) msg =
      .inr (Q.recv r i t fun j => msgOf m₀ (msg j)) := rfl

/-- **The commander protocol simulates the agreement protocol.** After round `r + 1` of
`Q.toOral c d m₀` with order `v` and traitors `traitors`, every loyal general `i` holds its state
after round `r` of `Q` with input the order it received from the commander, the same faulty
processes, and faulty messages read off the traitors' messages. -/
theorem state_toOral (c : G) (d : V) (m₀ : M) (v : V) (traitors : Finset G)
    (adv : ℕ → G → G → Option V ⊕ M) (r : ℕ) (i : G) (hi : i ∉ traitors) :
    (Q.toOral c d m₀).state c v traitors adv (r + 1) i =
      .inr (Q.state (fun i => orderOf d ((Q.toOral c d m₀).inbox c v traitors adv 0 i c))
        traitors (fun r j i => msgOf m₀ (adv (r + 1) j i)) r i) := by
  induction r generalizing i with
  | zero => rfl
  | succ r ih =>
      rw [OralProtocol.state_succ, ih i hi, toOral_recv_succ, state]
      congr 2
      funext j
      by_cases hj : j ∈ traitors
      · simp [OralProtocol.inbox, hj]
      · simp only [OralProtocol.inbox, hj, ite_false, ih j hj, toOral_send_succ, msgOf]

/-- **Byzantine agreement yields the Byzantine generals problem.** If `Q` reaches Byzantine
agreement with at most `m` faulty processes in `T` rounds, then `Q.toOral c d m₀` solves the
Byzantine generals problem with commander `c` and at most `m` traitors in `T + 1` rounds. -/
theorem solves_toOral {m T : ℕ} (hQ : Q.Solves m T) (c : G) (d : V) (m₀ : M) :
    (Q.toOral c d m₀).Solves c m (T + 1) := by
  intro v traitors ht adv
  set x := fun i => orderOf d ((Q.toOral c d m₀).inbox c v traitors adv 0 i c)
  obtain ⟨hA, hV⟩ := hQ x traitors ht (fun r j i => msgOf m₀ (adv (r + 1) j i))
  have hdec : ∀ i, i ∉ traitors → (Q.toOral c d m₀).decision c v traitors adv (T + 1) i =
      Q.decision x traitors (fun r j i => msgOf m₀ (adv (r + 1) j i)) T i := by
    intro i hi
    simp only [OralProtocol.decision, state_toOral Q c d m₀ v traitors adv T i hi]
    rfl
  refine ⟨fun i j _ _ hi hj => ?_, fun hc i _ hi => ?_⟩
  · rw [hdec i hi, hdec j hj]
    exact hA i j hi hj
  · rw [hdec i hi]
    refine hV v (fun k _ => ?_) i hi
    simp [x, OralProtocol.inbox, hc, OralProtocol.state_zero, OralProtocol.initState_self,
      toOral, orderOf]

/-- **No synchronous protocol reaches Byzantine agreement when `3 ≤ n ≤ 3 m`** (Fischer,
Lynch and Merritt, *Easy impossibility proofs for distributed consensus problems*, 1986,
Theorem 1, bound on the number of nodes, for the complete graph). If there are at least two
values and `n` processes with `3 ≤ n ≤ 3 m`, then no deterministic synchronous protocol reaches
Byzantine agreement with at most `m` faulty processes, in any number of rounds. -/
theorem not_solves_of_card_le_three_mul [Fintype G] [Nontrivial V] {m : ℕ}
    (h3 : 3 ≤ Fintype.card G) (hm : Fintype.card G ≤ 3 * m) (T : ℕ) : ¬ Q.Solves m T := by
  intro hQ
  obtain ⟨c⟩ : Nonempty G := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨d, -⟩ := exists_pair_ne V
  exact (Q.toOral c d (Q.send 0 c (Q.init c d) c)).not_solves_of_card_le_three_mul c h3 hm
    (T + 1) (Q.solves_toOral hQ c d _)

/-- **No synchronous protocol for three processes reaches Byzantine agreement with one fault**
(Fischer, Lynch and Merritt, 1986, §3.1, the case `n = 3`, `m = 1`). -/
theorem not_solves_three [Nontrivial V] (Q : AgreementProtocol (Fin 3) V σ M) (T : ℕ) :
    ¬ Q.Solves 1 T :=
  Q.not_solves_of_card_le_three_mul (by simp) (by simp) T

/-! ### Two processes -/

/-- With two processes `i` and `j`, the execution in which `j` is faulty and replays to `i` what
`j` sends in an execution with no fault looks, to `i`, exactly like that execution. -/
private theorem state_replay {i j : G} (hG : ∀ k, k = i ∨ k = j) (x : G → V)
    (adv : ℕ → G → G → M) (r : ℕ) :
    Q.state x {j} (fun r l k => Q.send r l (Q.state x ∅ adv r l) k) r i =
      Q.state x ∅ adv r i := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp only [state]
      rw [ih]
      congr 1
      funext l
      rcases hG l with rfl | rfl
      · by_cases hl : l = j
        · subst hl; simp
        · simp [Finset.mem_singleton, hl, ih]
      · simp

/-- **No synchronous protocol for two processes reaches Byzantine agreement with one fault.** If
there are exactly two processes and at least two values, no deterministic synchronous protocol
reaches Byzantine agreement with at most `m ≥ 1` faulty processes, in any number of rounds. With
inputs `v ≠ w`, each process must decide its own input when the other is faulty and replays its
correct behaviour, and it cannot tell that run from the run with no fault, where the two would
then disagree. (This elementary case is outside the standing assumption of Fischer, Lynch and
Merritt that graphs have at least three nodes.) -/
theorem not_solves_of_card_eq_two [Fintype G] [Nontrivial V] {m : ℕ} (hG : Fintype.card G = 2)
    (hm : 1 ≤ m) (T : ℕ) : ¬ Q.Solves m T := by
  intro hQ
  obtain ⟨i, j, hij, hcov⟩ : ∃ i j : G, i ≠ j ∧ ∀ k, k = i ∨ k = j := by
    obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card G)
    refine ⟨i, j, hij, fun k => ?_⟩
    by_contra h
    push Not at h
    have : ({i, j, k} : Finset G).card ≤ 2 := hG ▸ Finset.card_le_univ _
    rw [Finset.card_insert_of_notMem (by simp [hij, Ne.symm h.1]),
      Finset.card_pair (Ne.symm h.2)] at this
    omega
  obtain ⟨v, w, hvw⟩ := exists_pair_ne V
  let x : G → V := fun k => if k = i then v else w
  let m₀ : M := Q.send 0 i (Q.init i v) i
  let adv : ℕ → G → G → M := fun _ _ _ => m₀
  -- In the run with no fault each process decides its own input.
  have hdec : ∀ {i' j'}, i' ≠ j' → (∀ k, k = i' ∨ k = j') →
      Q.decision x ∅ adv T i' = x i' := by
    intro i' j' hne hcov'
    have hV := (hQ x {j'} (by simpa using hm)
      (fun r l k => Q.send r l (Q.state x ∅ adv r l) k)).2 (x i') (fun k hk => by
        rcases hcov' k with rfl | rfl
        · rfl
        · simp at hk) i' (by simpa using hne)
    simpa [decision, state_replay Q hcov'] using hV
  have hi := hdec hij hcov
  have hj := hdec (Ne.symm hij) (fun k => (hcov k).symm)
  have hA := (hQ x ∅ (by simp) adv).1 i j (by simp) (by simp)
  rw [hi, hj] at hA
  exact hvw (by simpa [x, Ne.symm hij] using hA)

/-- **No synchronous protocol reaches Byzantine agreement when `2 ≤ n ≤ 3 m`.** This combines
`not_solves_of_card_le_three_mul` (the bound of Fischer, Lynch and Merritt, for `n ≥ 3`) with the
case of two processes. -/
theorem not_solves_of_two_le_card [Fintype G] [Nontrivial V] {m : ℕ}
    (h2 : 2 ≤ Fintype.card G) (hm : Fintype.card G ≤ 3 * m) (T : ℕ) : ¬ Q.Solves m T := by
  rcases Nat.lt_or_ge (Fintype.card G) 3 with h | h
  · exact Q.not_solves_of_card_eq_two (by omega) (by omega) T
  · exact Q.not_solves_of_card_le_three_mul h hm T

end AgreementProtocol

end Cslib.Distributed.Byzantine.AgreementBound
