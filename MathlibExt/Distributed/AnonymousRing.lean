/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic

@[expose] public section


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
    [NeZero n] (s₀ : ZMod n → S) (h0 : ∀ i j, s₀ i = s₀ j)
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
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (L : S → Bool)
    (s₀ : ZMod n → S) (h0 : ∀ i j, s₀ i = s₀ j) (k : ℕ) :
    ¬ ∃! i : ZMod n, L (ringState δ s₀ k i) = true := by
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
