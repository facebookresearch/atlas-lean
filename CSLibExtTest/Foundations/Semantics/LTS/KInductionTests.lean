/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Foundations.Semantics.LTS.KInduction
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.NormNum

@[expose] public section

set_option autoImplicit false

namespace Cslib.LTS.KInductionTests

/-! ### A reachable deadlock -/

/-- `0 → 1 → 2`, where `2` has no successor, plus the edge `10 → 11`, which
is unreachable from `0`. -/
def deadlock : LTS ℕ Unit :=
  ⟨fun s _ t => (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 2) ∨ (s = 10 ∧ t = 11)⟩

/-- `2` is deadlocked. -/
example : deadlock.IsTerminal 2 := by
  intro _ t h
  rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega

/-- `2` is reachable from `0`. -/
theorem deadlock_canReach_two : deadlock.CanReach 0 2 :=
  ⟨[(), ()],
    .stepL (Or.inl ⟨rfl, rfl⟩) (.stepL (Or.inr (Or.inl ⟨rfl, rfl⟩)) .refl)⟩

/-- No infinite run starts at `0`, so no statement about infinite runs
constrains the deadlocked state `2`. -/
example : ¬ ∃ ss : ℕ → ℕ, ss 0 = 0 ∧ deadlock.OmegaRun ss := by
  rintro ⟨ss, h0, hrun⟩
  obtain ⟨_, h1⟩ := hrun 0
  obtain ⟨_, h2⟩ := hrun 1
  obtain ⟨_, h3⟩ := hrun 2
  simp only [deadlock, Nat.reduceAdd] at h1 h2 h3
  omega

/-- `· ≠ 11` is not `1`-inductive: the run prefix `10, 11` breaks the step
case for `k = 1`. -/
example : ¬ ∀ ss : ℕ → ℕ, deadlock.FiniteRun ss 1 →
    (∀ i, i < 1 → ss i ≠ 11) → ss 1 ≠ 11 := by
  intro h
  refine h (· + 10) (fun i hi => ⟨(), Or.inr (Or.inr ?_)⟩) (fun i hi => ?_) rfl
  · obtain rfl : i = 0 := by omega
    exact ⟨rfl, rfl⟩
  · obtain rfl : i = 0 := by omega
    exact (by decide : (10 : ℕ) ≠ 11)

/-- Base case of `2`-induction for `· ≠ 11` from `0`: run prefixes of length
`0` and `1`. -/
theorem deadlock_base : ∀ (ss : ℕ → ℕ) (n : ℕ), ss 0 = 0 →
    deadlock.FiniteRun ss n → n < 2 → ss n ≠ 11 := by
  intro ss n h0 hrun hn
  obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
  · omega
  · obtain ⟨_, h⟩ := hrun 0 (by omega)
    simp only [deadlock, Nat.reduceAdd] at h
    omega

/-- Step case of `2`-induction for `· ≠ 11`: two consecutive states other than
`11` are never followed by `11`. -/
theorem deadlock_step : ∀ ss : ℕ → ℕ, deadlock.FiniteRun ss 2 →
    (∀ i, i < 2 → ss i ≠ 11) → ss 2 ≠ 11 := by
  intro ss hrun hsafe
  obtain ⟨_, h01⟩ := hrun 0 (by omega)
  obtain ⟨_, h12⟩ := hrun 1 (by omega)
  have h0 := hsafe 0 (by omega)
  have h1 := hsafe 1 (by omega)
  simp only [deadlock, Nat.reduceAdd] at h01 h12
  omega

/-- `2`-induction proves `· ≠ 11` at every state reachable from `0`, the
deadlocked state `2` included. -/
theorem deadlock_ne_eleven {s : ℕ} (hs : deadlock.CanReach 0 s) : s ≠ 11 :=
  k_induction_canReach (init := (· = 0)) (P := (· ≠ 11)) deadlock_base
    deadlock_step rfl hs

/-- The invariant at the deadlocked state, through `k_induction_canReach`. -/
example : (2 : ℕ) ≠ 11 := deadlock_ne_eleven deadlock_canReach_two

/-- The finite-run form: every run prefix from `0` ends in a state other than
`11`. -/
example {ss : ℕ → ℕ} {n : ℕ} (h0 : ss 0 = 0) (hrun : deadlock.FiniteRun ss n) :
    ss n ≠ 11 :=
  k_induction_finiteRun (init := (· = 0)) (P := (· ≠ 11)) deadlock_base
    deadlock_step h0 hrun

/-! ### A bad initial state without transitions -/

/-- One state and no transitions. -/
def stuck : LTS PUnit Unit := ⟨fun _ _ _ => False⟩

/-- The `k = 1` base case fails at the only state, which is initial and bad,
even though no transition leaves it. The infinite-path hypotheses of
`k_induction_sound` hold vacuously here, since `stuck` has no infinite path. -/
example : ¬ ∀ (ss : ℕ → PUnit) (n : ℕ), True → stuck.FiniteRun ss n →
    n < 1 → False :=
  fun h => h (fun _ => PUnit.unit) 0 trivial finiteRun_zero Nat.one_pos

/-! ### The infinite-path statements -/

/-- Boundary check: for the constant transition system on
`ℕ` (stay in place) with bad states `Odd`, `k = 1` induction
applies from the initial state `0`. -/
example : ∀ p : ℕ → ℕ, p 0 = 0 → (∀ i, p (i + 1) = p i) →
    ∀ i, ¬ Odd (p i) := by
  intro p h0 hstep
  apply k_induction_sound (step := fun a b : ℕ => b = a)
    (init := fun s => s = 0) (bad := fun s => Odd s) (k := 1) _ _ p h0
    (fun i => hstep i)
  · intro q hq _ j hj
    have hj0 : j = 0 := by omega
    subst hj0
    simp [hq]
  · intro q hq hqstep
    have h00 : ¬ Odd (q 0) := hq 0 (by norm_num)
    have h1 : q 1 = q 0 := hqstep 0
    rwa [h1]

/-- State form: `4` lies on the path `0, 2, 4, …` of the system `n → n + 2`,
so `1`-induction shows that it is not odd. -/
example : ¬ Odd 4 :=
  safe_of_k_induction (step := fun a b : ℕ => b = a + 2)
    (init := fun s => s = 0) (bad := fun s => Odd s) (k := 1)
    (fun p h0 _ i hi => by
      obtain rfl : i = 0 := by omega
      simp [h0])
    (fun p hp hpath => by
      have h0 : ¬ Odd (p 0) := hp 0 (by norm_num)
      rw [show p 1 = p 0 + 2 from hpath 0]
      intro h
      exact h0 (by simpa [Nat.odd_add] using h))
    ⟨fun i => 2 * i, rfl,
      fun i => show 2 * (i + 1) = 2 * i + 2 by omega, 2, rfl⟩

end Cslib.LTS.KInductionTests
