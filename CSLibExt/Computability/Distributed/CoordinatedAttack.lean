/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Nontrivial.Defs
public import Mathlib.Data.Nat.Notation

/-!
# Impossibility of coordinated attack

A model of synchronous round-based message passing over unreliable links, and the theorem that
no deterministic protocol solves the coordinated attack problem in it (Aspnes, Chapter 8).

## Model

* **Processes:** the elements of a type `G` with at least two elements, not necessarily
  finite.
* **Synchrony:** lock-step rounds `0, 1, …`. In round `r` every process may send one message to
  every process (itself included), receives those of the round's messages to it that are
  delivered, and updates its state.
* **Unreliable links:** a loss pattern `Δ : ℕ → G → G → Bool` says whether the message that `j`
  sends to `i` in round `r`, if any, is delivered (`Δ r j i = true`) or lost. Every pattern is
  allowed, so the messages delivered in a round can be any subset, possibly empty, of those sent
  in it. A receiver sees, for each sender, its message or nothing, so it cannot tell a lost
  message from one that was never sent.
* **Protocols:** deterministic, with one state type for all processes (`LossyProtocol`). Every
  process decides from its state after a fixed number `T` of rounds, so termination within a
  bounded number of rounds is built in; a process that decides earlier can keep its decision in
  its state.
* **Coordinated attack** (`LossyProtocol.SolvesCoordinatedAttack`): in every execution all
  processes decide the same value (agreement), and if all inputs are `v` and no message is lost,
  every process decides `v` (validity). Inputs and decisions lie in a type `V` with at least two
  elements; in the source they are `0` (retreat) and `1` (attack).

## Main definitions

* `LossyProtocol G V σ M`, `LossyProtocol.stateAfter`, `LossyProtocol.SolvesCoordinatedAttack`.

## Main results

* `LossyProtocol.not_solvesCoordinatedAttack`: no protocol solves coordinated attack, in any
  number of rounds.
* `LossyProtocol.stateAfter_congr`, `LossyProtocol.stateAfter_eq_of_isolated_after`,
  `LossyProtocol.stateAfter_eq_of_isolated`: what a process computes depends only on its input
  and the messages delivered to it.

## Proof

The chain of indistinguishable executions of Aspnes, §8.2, with the messages of a round removed
in two batches rather than one at a time, so that no finiteness is needed. Fix two processes
`p ≠ q`. Let `upTo r` deliver every message of the rounds before `r` and none after.

* Going from `upTo (r + 1)` to `upTo r`, first lose the round-`r` messages to every process but
  `p`, then those to `p`. Since no later message is delivered, the first step does not change
  the final state of `p` and the second does not change that of `q`; by agreement, the common
  decision does not change. So the execution with no loss decides as the one with no delivery.
* With no delivery, a process's final state depends only on its input. Changing the inputs of
  every process but `p` from `a` to `b`, then that of `p`, does not change the common decision.

So the execution with all inputs `a` and no loss, which decides `a` by validity, decides as the
one with all inputs `b` and no loss, which decides `b`.

## References

* J. Aspnes, *Notes on Theory of Distributed Systems*, arXiv:2001.04235, Chapter 8: §8.1
  (formal description) and §8.2 (impossibility proof).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Distributed.CoordinatedAttack

/-- **Synchronous protocol over lossy links.** A deterministic protocol for the processes `G`
with inputs and decisions in `V`, local states `σ` and messages `M`. Process `i` starts in state
`init i x` from its input `x`. In round `r`, process `j` in state `s` sends `send r j s i` to
process `i`, `none` meaning no message, and process `i` in state `s` moves to `recv r i s msg`,
where `msg j` is the message it received from `j`, or `none` if it received none. At the end,
process `i` in state `s` decides `output i s`. -/
structure LossyProtocol (G V σ M : Type*) where
  /-- The initial state of each process, given its input. -/
  init : G → V → σ
  /-- `send r j s i` is the message process `j`, in state `s`, sends to `i` in round `r`, or
  `none` if it sends none. -/
  send : ℕ → G → σ → G → Option M
  /-- `recv r i s msg` is the state of process `i` after round `r`, from its state `s` and the
  message `msg j` it received from each process `j` (`none` if it received none). -/
  recv : ℕ → G → σ → (G → Option M) → σ
  /-- `output i s` is the value process `i` decides in its final state `s`. -/
  output : G → σ → V

namespace LossyProtocol

variable {G V σ M : Type*} (Q : LossyProtocol G V σ M)

/-- **Execution with message loss.** `Q.stateAfter x Δ r i` is the state of process `i` after `r`
rounds of `Q` with inputs `x` and loss pattern `Δ`: the message that `j` sends to `i` in round
`t`, if any, is delivered when `Δ t j i = true` and lost otherwise. -/
def stateAfter (x : G → V) (Δ : ℕ → G → G → Bool) : ℕ → G → σ
  | 0, i => Q.init i (x i)
  | r + 1, i => Q.recv r i (stateAfter x Δ r i) fun j =>
      if Δ r j i then Q.send r j (stateAfter x Δ r j) i else none

/-- **Solving coordinated attack in `T` rounds.** Every process decides from its state after
`T` rounds, with agreement (for all inputs `x` and every loss pattern `Δ`, all processes decide
the same value) and validity (if all inputs are `v` and no message is lost, every process decides
`v`). -/
def SolvesCoordinatedAttack (T : ℕ) : Prop :=
  (∀ (x : G → V) (Δ : ℕ → G → G → Bool) (i j : G),
      Q.output i (Q.stateAfter x Δ T i) = Q.output j (Q.stateAfter x Δ T j)) ∧
    ∀ (v : V) (i : G), Q.output i (Q.stateAfter (fun _ => v) (fun _ _ _ => true) T i) = v

theorem stateAfter_congr (x : G → V) {Δ Δ' : ℕ → G → G → Bool} {k : ℕ}
    (h : ∀ t < k, Δ t = Δ' t) : ∀ t ≤ k, Q.stateAfter x Δ t = Q.stateAfter x Δ' t := by
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih =>
      funext i
      simp only [stateAfter]
      rw [ih (by omega), h t (by omega)]

theorem stateAfter_eq_of_isolated_after (x : G → V) {Δ Δ' : ℕ → G → G → Bool} {k : G} {r : ℕ}
    (hbefore : ∀ t < r, Δ t = Δ' t) (hround : ∀ j, Δ r j k = Δ' r j k)
    (hafter : ∀ t, r < t → ∀ j, Δ t j k = false ∧ Δ' t j k = false) (t : ℕ) :
    Q.stateAfter x Δ t k = Q.stateAfter x Δ' t k := by
  have hle := Q.stateAfter_congr x hbefore
  induction t with
  | zero => exact congrFun (hle 0 (Nat.zero_le r)) k
  | succ t ih =>
      rcases Nat.lt_or_ge t r with htr | htr
      · exact congrFun (hle (t + 1) htr) k
      rcases Nat.eq_or_lt_of_le htr with rfl | htr
      · simp only [stateAfter]
        rw [hle _ (Nat.le_refl _)]
        simp only [hround]
      · have h₁ : ∀ j, Δ t j k = false := fun j => (hafter t htr j).1
        have h₂ : ∀ j, Δ' t j k = false := fun j => (hafter t htr j).2
        simp [stateAfter, h₁, h₂, ih]

theorem stateAfter_eq_of_isolated {x x' : G → V} {Δ : ℕ → G → G → Bool} {k : G}
    (hx : x k = x' k) (hΔ : ∀ t j, Δ t j k = false) (t : ℕ) :
    Q.stateAfter x Δ t k = Q.stateAfter x' Δ t k := by
  induction t with
  | zero => simp [stateAfter, hx]
  | succ t ih => simp [stateAfter, hΔ, ih]

/-- **Impossibility of coordinated attack** (Aspnes, Notes on Theory of Distributed Systems,
§8.2). With at least two processes and at least two values, no deterministic protocol over
lossy links solves coordinated attack in any number `T` of rounds: some execution violates
agreement, or some execution with equal inputs and no loss violates validity. -/
theorem not_solvesCoordinatedAttack [Nontrivial G] [Nontrivial V] (T : ℕ) :
    ¬ Q.SolvesCoordinatedAttack T := by
  rintro ⟨hagree, hvalid⟩
  classical
  obtain ⟨p, q, hpq⟩ := exists_pair_ne G
  obtain ⟨a, b, hab⟩ := exists_pair_ne V
  -- The common decision of an execution, read off at `p` or, by agreement, at `q`.
  let out (x : G → V) (Δ : ℕ → G → G → Bool) : V := Q.output p (Q.stateAfter x Δ T p)
  have hout_q : ∀ x Δ, out x Δ = Q.output q (Q.stateAfter x Δ T q) := fun x Δ => hagree x Δ p q
  -- Deliver every message of the rounds before `r` and none after.
  let upTo (r : ℕ) : ℕ → G → G → Bool := fun t _ _ => decide (t < r)
  -- Losing the messages of round `r`, first those to every process but `p`, then those to `p`.
  have hstep : ∀ x r, out x (upTo (r + 1)) = out x (upTo r) := by
    intro x r
    let mid : ℕ → G → G → Bool := fun t _ i => decide (t < r) || (decide (t = r) && decide (i = p))
    have h₁ : out x (upTo (r + 1)) = out x mid := by
      simp only [out]
      rw [Q.stateAfter_eq_of_isolated_after x (Δ := upTo (r + 1)) (Δ' := mid) (k := p) (r := r)
        (fun t ht => by funext j i; simp [upTo, mid, ht, Nat.lt_succ_of_lt ht])
        (fun j => by simp [upTo, mid])
        (fun t ht j => by
          have h₁ : ¬ t < r + 1 := by omega
          have h₂ : ¬ t < r := by omega
          have h₃ : t ≠ r := by omega
          simp [upTo, mid, h₁, h₂, h₃]) T]
    have h₂ : out x mid = out x (upTo r) := by
      rw [hout_q, hout_q]
      rw [Q.stateAfter_eq_of_isolated_after x (Δ := mid) (Δ' := upTo r) (k := q) (r := r)
        (fun t ht => by funext j i; simp [upTo, mid, ht])
        (fun j => by simp [upTo, mid, hpq.symm])
        (fun t ht j => by
          have h₁ : ¬ t < r := by omega
          have h₂ : t ≠ r := by omega
          simp [upTo, mid, h₁, h₂]) T]
    rw [h₁, h₂]
  -- The execution with no loss decides as the one with no delivery.
  have hsilent : ∀ x, out x (fun _ _ _ => true) = out x (upTo 0) := by
    intro x
    have hT : out x (fun _ _ _ => true) = out x (upTo T) := by
      simp only [out]
      rw [Q.stateAfter_congr x (Δ := fun _ _ _ => true) (Δ' := upTo T) (k := T)
        (fun t ht => by funext j i; simp [upTo, ht]) T (Nat.le_refl T)]
    have hdown : ∀ r, out x (upTo r) = out x (upTo 0) := by
      intro r
      induction r with
      | zero => rfl
      | succ r ih => rw [hstep, ih]
    rw [hT, hdown]
  -- With no delivery, the inputs can be changed one batch at a time.
  have hnone : ∀ t j k, upTo 0 t j k = false := fun t j k => by simp [upTo]
  have hinputs : out (fun _ => a) (upTo 0) = out (fun _ => b) (upTo 0) := by
    let xm : G → V := fun k => if k = p then a else b
    have h₁ : out (fun _ => a) (upTo 0) = out xm (upTo 0) := by
      simp only [out]
      rw [Q.stateAfter_eq_of_isolated (x' := xm) (by simp [xm]) (fun t j => hnone t j p) T]
    have h₂ : out xm (upTo 0) = out (fun _ => b) (upTo 0) := by
      rw [hout_q, hout_q]
      rw [Q.stateAfter_eq_of_isolated (x' := fun _ => b) (by simp [xm, hpq.symm])
        (fun t j => hnone t j q) T]
    rw [h₁, h₂]
  apply hab
  calc a = out (fun _ => a) (fun _ _ _ => true) := (hvalid a p).symm
    _ = out (fun _ => a) (upTo 0) := hsilent _
    _ = out (fun _ => b) (upTo 0) := hinputs
    _ = out (fun _ => b) (fun _ _ _ => true) := (hsilent _).symm
    _ = b := hvalid b p

end LossyProtocol

end Cslib.Distributed.CoordinatedAttack
