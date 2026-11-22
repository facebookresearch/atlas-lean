/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Foundations.Relation.RelatesInSteps
public import Mathlib.Data.Fintype.Defs

/-!
# Savitch's midpoint recursion for bounded reachability

`reachIn R k x y` decides whether `y` is reachable from `x` in at most `2 ^ k` steps of a
decidable relation `R` on a finite configuration type, by the midpoint recursion behind
Savitch's theorem: a walk of at most `2 ^ (k + 1)` steps exists iff some midpoint splits it into
two walks of at most `2 ^ k` steps each.

Walks are CSLib's canonical exact-step relation `Relation.RelatesInSteps`. The midpoint search
is the `Decidable (∃ z, _)` instance for finite types, an existential scan over the
configurations that stops at the first witness. This file proves only that the recursion
decides bounded reachability extensionally; it makes no space-complexity claim.

## Main results

* `Cslib.Complexity.Savitch.reachIn_sound`: acceptance yields a walk of at most `2 ^ k` steps.
* `Cslib.Complexity.Savitch.reachIn_complete`: a walk of at most `2 ^ k` steps yields
  acceptance.
* `Cslib.Complexity.Savitch.reachIn_iff_relatesWithinSteps`: acceptance holds iff
  `Relation.RelatesWithinSteps R x y (2 ^ k)`.
-/

@[expose] public section

namespace Cslib.Complexity.Savitch

/-- Splitting: a chain of `n` steps of `R` from `x` to `y` passes, after any `j ≤ n` steps,
through some `z` that `x` reaches in `j` steps and that reaches `y` in `n - j` steps. -/
theorem relatesInSteps_split {α : Type*} {R : α → α → Prop} {x y : α} {n : ℕ}
    (h : Relation.RelatesInSteps R x y n) (j : ℕ) (hj : j ≤ n) :
    ∃ z, Relation.RelatesInSteps R x z j ∧ Relation.RelatesInSteps R z y (n - j) := by
  revert j hj
  induction h with
  | refl =>
      intro j hj
      obtain rfl : j = 0 := by omega
      exact ⟨x, .refl x, .refl x⟩
  | tail t' t'' n h₁ h₂ ih =>
      intro j hj
      by_cases heq : j = n + 1
      · subst heq
        refine ⟨t'', .tail _ _ _ _ h₁ h₂, ?_⟩
        rw [Nat.sub_self]
        exact .refl t''
      · obtain ⟨w, p1, p2⟩ := ih j (by omega)
        refine ⟨w, p1, ?_⟩
        have e : n + 1 - j = (n - j) + 1 := by omega
        rw [e]
        exact .tail _ _ _ _ p2 h₂

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Bounded reachability by midpoint recursion: `reachIn R k x y` decides whether `y` is
reachable from `x` in at most `2 ^ k` steps of `R`. At level `k + 1` it accepts iff some midpoint
`z` is reachable from `x`, and reaches `y`, within `2 ^ k` steps each; the midpoint search is
the existential scan given by `Decidable (∃ z, _)` on the finite type `C`. This is an
extensional decision procedure; no space bound is claimed. -/
def reachIn (R : C → C → Prop) [DecidableRel R] : ℕ → C → C → Bool
  | 0, x, y => decide (x = y ∨ R x y)
  | k + 1, x, y => decide (∃ z, reachIn R k x z = true ∧ reachIn R k z y = true)

/-- Soundness: if the Savitch predicate accepts, a path of length
at most `2 ^ k` exists. -/
theorem reachIn_sound {R : C → C → Prop} [DecidableRel R]
    (k : ℕ) (x y : C) (h : reachIn R k x y = true) :
    ∃ n ≤ 2 ^ k, Relation.RelatesInSteps R x y n := by
  induction k generalizing x y with
  | zero =>
      simp only [reachIn] at h
      obtain rfl | hR := of_decide_eq_true h
      · exact ⟨0, Nat.zero_le _, .refl x⟩
      · exact ⟨1, by simp, .single hR⟩
  | succ k ih =>
      simp only [reachIn] at h
      obtain ⟨z, h1, h2⟩ := of_decide_eq_true h
      obtain ⟨n1, hn1, p1⟩ := ih x z h1
      obtain ⟨n2, hn2, p2⟩ := ih z y h2
      have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
      exact ⟨n1 + n2, by omega, p1.trans p2⟩

/-- Completeness: if a path of length at most `2 ^ k` exists,
the Savitch predicate accepts. -/
theorem reachIn_complete {R : C → C → Prop} [DecidableRel R]
    (k : ℕ) {x y : C} {n : ℕ} (hn : n ≤ 2 ^ k)
    (hpath : Relation.RelatesInSteps R x y n) :
    reachIn R k x y = true := by
  induction k generalizing x y n with
  | zero =>
      simp only [reachIn]
      apply decide_eq_true
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (by simpa using hn) with rfl | rfl
      · exact Or.inl hpath.zero
      · obtain ⟨t, ht, hR⟩ := hpath.succ
        obtain rfl := ht.zero
        exact Or.inr hR
  | succ k ih =>
      simp only [reachIn]
      apply decide_eq_true
      by_cases hle : n ≤ 2 ^ k
      · exact ⟨y, ih hle hpath, ih (Nat.zero_le _) (.refl y)⟩
      · have h2k : 2 ^ k ≤ n := by omega
        obtain ⟨z, p1, p2⟩ := relatesInSteps_split hpath (2 ^ k) h2k
        have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
        exact ⟨z, ih (le_refl _) p1, ih (by omega) p2⟩

/-- **Correctness in CSLib terms.** The Savitch predicate accepts exactly when `y` is reachable
from `x` within `2 ^ k` steps of `R`, in the sense of `Relation.RelatesWithinSteps`. -/
theorem reachIn_iff_relatesWithinSteps {R : C → C → Prop} [DecidableRel R] (k : ℕ) (x y : C) :
    reachIn R k x y = true ↔ Relation.RelatesWithinSteps R x y (2 ^ k) :=
  ⟨reachIn_sound k x y, fun ⟨_, hn, p⟩ => reachIn_complete k hn p⟩

end Cslib.Complexity.Savitch
