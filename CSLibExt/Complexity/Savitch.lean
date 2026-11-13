/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Foundations.Relation.RelatesInSteps
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card

/-!
# Savitch's midpoint recursion for bounded reachability

`reachIn R k x y` decides whether `y` is reachable from `x` in at most `2 ^ k` steps of a
decidable relation `R` on a finite configuration type, by the midpoint recursion behind
Savitch's theorem: a walk of at most `2 ^ (k + 1)` steps exists iff some midpoint splits it into
two walks of at most `2 ^ k` steps each.

This file proves only that the recursion decides bounded reachability extensionally. It makes
no space-complexity claim: the implementation collects the successful midpoints with
`Finset.filter` over `Finset.univ` and counts them with `Finset.card`, so an evaluation may hold
many configurations at once rather than one configuration per recursion frame.

Walks are `GPath R x y n`, which is equivalent to CSLib's canonical exact-step relation
`Relation.RelatesInSteps R x y n` (`gPath_iff_relatesInSteps`), and
`reachIn_iff_relatesWithinSteps` states correctness with `Relation.RelatesWithinSteps`.

## Main results

* `Cslib.Complexity.Savitch.reachIn_sound`: acceptance yields a walk of at most `2 ^ k` steps.
* `Cslib.Complexity.Savitch.reachIn_complete`: a walk of at most `2 ^ k` steps yields
  acceptance.
* `Cslib.Complexity.Savitch.reachIn_iff_relatesWithinSteps`: acceptance holds iff
  `Relation.RelatesWithinSteps R x y (2 ^ k)`.
* `Cslib.Complexity.Savitch.gPath_iff_relatesInSteps`: `GPath` agrees with
  `Relation.RelatesInSteps`.
-/

@[expose] public section

namespace Cslib.Complexity.Savitch

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Bounded reachability by midpoint recursion: `reachIn R k x y` decides whether `y` is
reachable from `x` in at most `2 ^ k` steps of `R`. At level `k + 1` it accepts iff some midpoint
`z` is reachable from `x`, and reaches `y`, within `2 ^ k` steps each. This is an extensional
decision procedure only: midpoints are collected with `Finset.filter` and counted with
`Finset.card`, and no space bound is claimed. -/
def reachIn (R : C → C → Prop) [DecidableRel R] : ℕ → C → C → Bool
  | 0, x, y => decide (x = y ∨ R x y)
  | k + 1, x, y =>
      (Finset.univ.filter (fun z => reachIn R k x z && reachIn R k z y)).card > 0

/-- A walk of exactly `n` steps of `R` from `x` to `y`, extended one step at a time at its end.
It is equivalent to CSLib's `Relation.RelatesInSteps R x y n` (`gPath_iff_relatesInSteps`). -/
inductive GPath (R : C → C → Prop) (x : C) : C → ℕ → Prop
  | refl : GPath R x x 0
  | step {y z : C} {n : ℕ} (h : R y z) (hpath : GPath R x y n) : GPath R x z (n + 1)

/-- Concatenation: a walk of `n` steps from `x` to `y` followed by a walk of `m` steps from `y`
to `z` is a walk of `n + m` steps from `x` to `z`. -/
theorem GPath.append {C : Type*} {R : C → C → Prop} {x y z : C} {n m : ℕ}
    (h1 : GPath R x y n) (h2 : GPath R y z m) : GPath R x z (n + m) := by
  revert x n h1
  induction h2 with
  | refl =>
      intro x n h1
      simpa using h1
  | step h hp ih =>
      intro x n h1
      exact GPath.step h (ih h1)

/-- Splitting: a walk of `n` steps from `x` to `y` passes, after any `j ≤ n` steps, through a
configuration `z` that `x` reaches in `j` steps and that reaches `y` in `n - j` steps. -/
theorem GPath.split {C : Type*} {R : C → C → Prop} {x y : C} {n : ℕ}
    (hpath : GPath R x y n) (j : ℕ) (hj : j ≤ n) :
    ∃ z, GPath R x z j ∧ GPath R z y (n - j) := by
  revert j hj
  induction hpath with
  | refl =>
      intro j hj
      have hj0 : j = 0 := by omega
      subst hj0
      exact ⟨x, GPath.refl, GPath.refl⟩
  | step h hp ih =>
      rename_i ymid yend len
      intro j hj
      by_cases heq : j = len + 1
      · subst heq
        refine ⟨_, GPath.step h hp, ?_⟩
        have e : len + 1 - (len + 1) = 0 := by omega
        rw [e]
        exact GPath.refl
      · have hj' : j ≤ len := by omega
        obtain ⟨w, p1, p2⟩ := ih _ hj'
        refine ⟨w, p1, ?_⟩
        have e : len + 1 - j = (len - j) + 1 := by omega
        rw [e]
        exact GPath.step h p2

/-- A `GPath` is a CSLib `Relation.RelatesInSteps` chain of the same length. -/
theorem GPath.toRelatesInSteps {C : Type*} {R : C → C → Prop} {x y : C} {n : ℕ}
    (h : GPath R x y n) : Relation.RelatesInSteps R x y n := by
  induction h with
  | refl => exact Relation.RelatesInSteps.refl x
  | step hR _ ih => exact Relation.RelatesInSteps.tail _ _ _ _ ih hR

/-- A CSLib `Relation.RelatesInSteps` chain is a `GPath` of the same length. -/
theorem GPath.ofRelatesInSteps {C : Type*} {R : C → C → Prop} {x y : C} {n : ℕ}
    (h : Relation.RelatesInSteps R x y n) : GPath R x y n := by
  induction h with
  | refl => exact GPath.refl
  | tail _ _ _ _ hR ih => exact GPath.step hR ih

/-- `GPath` agrees with CSLib's canonical exact-step relation `Relation.RelatesInSteps`. -/
theorem gPath_iff_relatesInSteps {C : Type*} {R : C → C → Prop} {x y : C} {n : ℕ} :
    GPath R x y n ↔ Relation.RelatesInSteps R x y n :=
  ⟨GPath.toRelatesInSteps, GPath.ofRelatesInSteps⟩

/-- Soundness: if the Savitch predicate accepts, a path of length
at most `2 ^ k` exists. -/
theorem reachIn_sound {R : C → C → Prop} [DecidableRel R]
    (k : ℕ) (x y : C) (h : reachIn R k x y = true) :
    ∃ n ≤ 2 ^ k, GPath R x y n := by
  induction k generalizing x y with
  | zero =>
      simp only [reachIn] at h
      obtain rfl | hR := of_decide_eq_true h
      · exact ⟨0, Nat.zero_le _, GPath.refl⟩
      · exact ⟨1, by simp, GPath.step hR GPath.refl⟩
  | succ k ih =>
      simp only [reachIn] at h
      have hpos := of_decide_eq_true h
      have hne := Finset.card_pos.mp hpos
      obtain ⟨z, hz⟩ := hne
      have hz' := Finset.mem_filter.mp hz
      have hand : (reachIn R k x z && reachIn R k z y) = true := hz'.2
      rw [Bool.and_eq_true] at hand
      obtain ⟨h1, h2⟩ := hand
      obtain ⟨n1, hn1, p1⟩ := ih x z h1
      obtain ⟨n2, hn2, p2⟩ := ih z y h2
      have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
      exact ⟨n1 + n2, by omega, GPath.append p1 p2⟩

/-- Completeness: if a path of length at most `2 ^ k` exists,
the Savitch predicate accepts. -/
theorem reachIn_complete {R : C → C → Prop} [DecidableRel R]
    (k : ℕ) {x y : C} {n : ℕ} (hn : n ≤ 2 ^ k)
    (hpath : GPath R x y n) :
    reachIn R k x y = true := by
  induction k generalizing x y n with
  | zero =>
      revert hn
      induction hpath with
      | refl =>
          intro hn
          simp only [reachIn]
          exact decide_eq_true_iff.mpr (Or.inl trivial)
      | step h hp ih =>
          rename_i ymid yend len
          intro hn
          simp only [pow_zero] at hn
          have hlen : len = 0 := by omega
          subst hlen
          revert h
          cases hp with
          | refl =>
              intro h
              simp only [reachIn]
              exact decide_eq_true_iff.mpr (Or.inr h)
  | succ k ih =>
      by_cases hle : n ≤ 2 ^ k
      · have h1 : reachIn R k x y = true := ih hle hpath
        have h2 : reachIn R k y y = true := ih (Nat.zero_le _) GPath.refl
        simp only [reachIn]
        have hand : (reachIn R k x y && reachIn R k y y) = true := by simp [h1, h2]
        have hmem : y ∈ Finset.univ.filter (fun z => reachIn R k x z && reachIn R k z y) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ y, hand⟩
        have hcard : (Finset.univ.filter (fun z => reachIn R k x z && reachIn R k z y)).card > 0 :=
          Finset.card_pos.mpr ⟨y, hmem⟩
        exact decide_eq_true_iff.mpr hcard
      · have h2k : 2 ^ k ≤ n := by omega
        obtain ⟨z, p1, p2⟩ := GPath.split hpath (2 ^ k) h2k
        have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
        have h1 : reachIn R k x z = true := ih (le_refl _) p1
        have h2 : reachIn R k z y = true := ih (by omega) p2
        simp only [reachIn]
        have hand : (reachIn R k x z && reachIn R k z y) = true := by simp [h1, h2]
        have hmem : z ∈ Finset.univ.filter (fun z => reachIn R k x z && reachIn R k z y) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ z, hand⟩
        have hcard : (Finset.univ.filter (fun z => reachIn R k x z && reachIn R k z y)).card > 0 :=
          Finset.card_pos.mpr ⟨z, hmem⟩
        exact decide_eq_true_iff.mpr hcard

/-- **Correctness in CSLib terms.** The Savitch predicate accepts exactly when `y` is reachable
from `x` within `2 ^ k` steps of `R`, in the sense of `Relation.RelatesWithinSteps`. -/
theorem reachIn_iff_relatesWithinSteps {R : C → C → Prop} [DecidableRel R] (k : ℕ) (x y : C) :
    reachIn R k x y = true ↔ Relation.RelatesWithinSteps R x y (2 ^ k) := by
  constructor
  · intro h
    obtain ⟨n, hn, p⟩ := reachIn_sound k x y h
    exact ⟨n, hn, p.toRelatesInSteps⟩
  · rintro ⟨n, hn, p⟩
    exact reachIn_complete k hn (GPath.ofRelatesInSteps p)

end Cslib.Complexity.Savitch
