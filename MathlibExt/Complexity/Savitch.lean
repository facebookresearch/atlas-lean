/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card

@[expose] public section


variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Bounded reachability in a configuration graph, Savitch
style: `reachIn R k x y` says `y` is reachable from `x` in at
most `2 ^ k` steps of the relation `R`, defined by the recursive
middle-point decomposition that gives the `O(s^2)` space bound
of Savitch's theorem: to check reachability in `2^(k+1)` steps,
guess a middle configuration and check both halves. -/
def reachIn (R : C → C → Prop) [DecidableRel R] : ℕ → C → C → Bool
  | 0, x, y => decide (x = y ∨ R x y)
  | k + 1, x, y =>
      (Finset.univ.filter (fun z => reachIn R k x z && reachIn R k z y)).card > 0

/-- A walk of length `n` from `x` to `y`: a list of intermediate
configurations stating consecutive steps. `GPath R xs x y` holds
for the list of vertices after `x`, ending at `y`. -/
inductive GPath (R : C → C → Prop) (x : C) : C → ℕ → Prop
  | refl : GPath R x x 0
  | step {y z : C} {n : ℕ} (h : R y z) (hpath : GPath R x y n) : GPath R x z (n + 1)

private theorem GPath.append {C : Type*} {R : C → C → Prop} {x y z : C} {n m : ℕ}
    (h1 : GPath R x y n) (h2 : GPath R y z m) : GPath R x z (n + m) := by
  revert x n h1
  induction h2 with
  | refl =>
      intro x n h1
      simpa using h1
  | step h hp ih =>
      intro x n h1
      exact GPath.step h (ih h1)

private theorem GPath.split {C : Type*} {R : C → C → Prop} {x y : C} {n : ℕ}
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
