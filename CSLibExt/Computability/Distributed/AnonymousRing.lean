/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic

/-!
# No deterministic leader election on an anonymous synchronous ring

Angluin's symmetry argument (D. Angluin, *Local and global properties in networks of
processors*, Proceedings of the 12th Annual ACM Symposium on Theory of Computing (STOC), 1980):
identical deterministic processes started in identical states on a ring can never break their
symmetry, so none of them can be singled out as the leader. N. Lynch, *Distributed Algorithms*
(Morgan Kaufmann, 1996), Chapter 3, gives this impossibility for synchronous rings, the setting
formalized here.

## Model

`n` processes sit on a ring indexed by `ZMod n`; process `i` has the neighbors `i - 1` (left)
and `i + 1` (right). In each synchronous round every process replaces its local state by
`δ (left state, own state, right state)`, for one deterministic transition `δ` shared by all
processes (`ringStep`); `ringState δ s₀ k` is the configuration after `k` rounds from `s₀`.
The shared `δ` together with a constant initial configuration is the anonymity assumption:
identical code, identical initial states, no identifiers. A round of a synchronous
message-passing ring algorithm has this form, because the messages a process receives are
functions of its neighbors' states, so its next state is a function of the three states.
Processes tell their left and right neighbors apart consistently around the ring, which can
only help an election algorithm.

## Main results

* `ringState_const`: from a constant initial configuration, all processes are in the same state
  after any number of rounds.
* `no_leader_election`: hence, on a ring of at least two processes, for every predicate `L` on
  local states ("I am the leader") and every round, `L` never holds at exactly one process.
-/

@[expose] public section

namespace Cslib.Distributed.AnonymousRing

/-- One synchronous round on an anonymous ring of `n` processes
indexed by `ZMod n`: every process runs the same deterministic
transition `δ (left, self, right)` on its neighbors' states. -/
def ringStep {S : Type*} (δ : S → S → S → S) {n : ℕ}
    (s : ZMod n → S) (i : ZMod n) : S :=
  δ (s (i - 1)) (s i) (s (i + 1))

/-- The state after `k` synchronous rounds from initial state
`s₀`. -/
def ringState {S : Type*} (δ : S → S → S → S) {n : ℕ}
    (s₀ : ZMod n → S) : ℕ → ZMod n → S
  | 0 => s₀
  | k + 1 => ringStep δ (ringState δ s₀ k)

/-- Angluin's symmetry argument: if all processes start in the
same state (anonymity: identical code and initial state), then
after any number of synchronous rounds all processes are still
in the same state. -/
theorem ringState_const {S : Type*} (δ : S → S → S → S) {n : ℕ}
    (s₀ : ZMod n → S) (h0 : ∀ i j, s₀ i = s₀ j)
    (k : ℕ) (i j : ZMod n) :
    ringState δ s₀ k i = ringState δ s₀ k j := by
  revert i j
  induction k with
  | zero => exact h0
  | succ k ih =>
    intro i j
    simp only [ringState, ringStep]
    rw [ih (i - 1) (j - 1), ih i j, ih (i + 1) (j + 1)]

/-- Hence deterministic leader election is impossible on an
anonymous ring with at least two processes: if a leader is
determined by a process's local state (`L` reads "I am the
leader" off the state), then at every round either every
process claims leadership or none does; never exactly one. -/
theorem no_leader_election {S : Type*} (δ : S → S → S → S)
    {n : ℕ} (hn : 2 ≤ n) (L : S → Bool)
    (s₀ : ZMod n → S) (h0 : ∀ i j, s₀ i = s₀ j) (k : ℕ) :
    ¬ ∃! i : ZMod n, L (ringState δ s₀ k i) = true := by
  have : NeZero n := ⟨by omega⟩
  rintro ⟨i₀, hi₀, huniq⟩
  have hcard : 1 < Fintype.card (ZMod n) := by
    rw [ZMod.card n]
    exact hn
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card hcard i₀
  have hstate : ringState δ s₀ k j = ringState δ s₀ k i₀ :=
    ringState_const δ s₀ h0 k j i₀
  have hjtrue : L (ringState δ s₀ k j) = true := by
    rw [hstate]
    exact hi₀
  have heq : j = i₀ := huniq j hjtrue
  exact hj heq

end Cslib.Distributed.AnonymousRing
