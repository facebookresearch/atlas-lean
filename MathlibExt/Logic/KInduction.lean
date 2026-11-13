/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic

variable {S : Type*}

@[expose] public section

namespace MetaMathlibExt

/-- `k`-induction soundness for a transition system `step`
with initial states `init` and bad states `bad`, over
infinite paths: if no bad state occurs among the first `k`
states of any path from an initial state (base), and any
`k` consecutive bad-free states along a path are followed by
a bad-free state (step), then no path from an initial state
ever reaches a bad state. -/
theorem k_induction_sound {step : S → S → Prop}
    {init bad : S → Prop} {k : ℕ}
    (hbase : ∀ p : ℕ → S, init (p 0) →
      (∀ i, step (p i) (p (i + 1))) → ∀ i, i < k → ¬ bad (p i))
    (hstep : ∀ p : ℕ → S, (∀ i, i < k → ¬ bad (p i)) →
      (∀ i, step (p i) (p (i + 1))) → ¬ bad (p k)) :
    ∀ p : ℕ → S, init (p 0) → (∀ i, step (p i) (p (i + 1))) →
      ∀ i, ¬ bad (p i) := by
  intro p hinit hpath i
  have hall : ∀ n i, i < n → ¬ bad (p i) := by
    intro n
    induction n with
    | zero =>
      intro i hi
      exact absurd hi (Nat.not_lt_zero i)
    | succ n ih =>
      intro i hi
      by_cases hlt : i < k
      · exact hbase p hinit hpath i hlt
      · have hle : k ≤ i := Nat.le_of_not_lt hlt
        have hqsteps : ∀ j, step (p (i - k + j)) (p (i - k + (j + 1))) := by
          intro j
          have heq : i - k + (j + 1) = (i - k + j) + 1 := by omega
          rw [heq]
          exact hpath (i - k + j)
        have hqbase : ∀ j, j < k → ¬ bad (p (i - k + j)) := by
          intro j hj
          apply ih
          omega
        have hqk : ¬ bad (p (i - k + k)) :=
          hstep (fun j => p (i - k + j)) hqbase hqsteps
        have heq : i - k + k = i := Nat.sub_add_cancel hle
        rw [heq] at hqk
        exact hqk
  exact hall (i + 1) i (Nat.lt_succ_self i)

/-- Corollary: every state on a path from an initial state is
safe, in state form. -/
theorem safe_of_k_induction {step : S → S → Prop}
    {init bad : S → Prop} {k : ℕ}
    (hbase : ∀ p : ℕ → S, init (p 0) →
      (∀ i, step (p i) (p (i + 1))) → ∀ i, i < k → ¬ bad (p i))
    (hstep : ∀ p : ℕ → S, (∀ i, i < k → ¬ bad (p i)) →
      (∀ i, step (p i) (p (i + 1))) → ¬ bad (p k))
    {s : S} (hreach : ∃ p : ℕ → S, init (p 0) ∧
      (∀ i, step (p i) (p (i + 1))) ∧ ∃ i, p i = s) :
    ¬ bad s := by
  obtain ⟨p, hinit, hpath, i, hi⟩ := hreach
  rw [← hi]
  exact k_induction_sound hbase hstep p hinit hpath i

end MetaMathlibExt
