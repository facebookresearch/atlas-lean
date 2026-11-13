/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Leonard Dinh
-/
module

public import MathlibExt.Dynamics.DelayedDifferenceEquation

@[expose] public section

namespace MathlibExtTest.Dynamics.DelayedDifferenceEquation

open MetaMathlibExt

-- Analysis 386: Solution of a Delayed Difference Equation

theorem constant_isDelayedDifferenceSolution
    {X : Type*}
    (c : X)
    (m : ℕ) :
    IsDelayedDifferenceSolution
      m
      (fun _ => c)
      (fun _ => c) := by
  intro n
  simp

-- Analysis 387: Lyapunov Stability of a Delayed Difference Solution

theorem zero_system_isStable
    (m : ℕ) :
    IsStableDelayedSolution
      m
      (fun _ : Fin (m + 1) → ℝ => 0)
      (fun _ : ℤ → ℝ => True)
      (fun _ : ℤ => 0) := by
  refine ⟨?_, trivial, ?_⟩
  · intro n
    rfl
  · intro ε hε
    refine ⟨ε, hε, ?_⟩
    intro x hx _ hclose n
    cases n with
    | zero =>
        simpa using hclose (0 : Fin (m + 1))
    | succ k =>
        have hxn :
            x (Int.ofNat (k + 1)) = 0 := by
          simpa using hx k
        rw [hxn]
        simpa using hε

-- Analysis 388: Asymptotic Stability of a Delayed Difference Solution

theorem zero_system_isAsymptoticallyStable
    (m : ℕ) :
    IsAsymptoticallyStableDelayedSolution
      m
      (fun _ : Fin (m + 1) → ℝ => 0)
      (fun _ : ℤ → ℝ => True)
      (fun _ : ℤ => 0) := by
  constructor
  · refine ⟨?_, trivial, ?_⟩
    · intro n
      rfl
    · intro ε hε
      refine ⟨ε, hε, ?_⟩
      intro x hx _ hclose n
      cases n with
      | zero =>
          simpa using hclose (0 : Fin (m + 1))
      | succ k =>
          have hxn :
              x (Int.ofNat (k + 1)) = 0 := by
            simpa using hx k
          change dist (x (Int.ofNat (k + 1))) 0 < ε
          rw [hxn]
          simpa using hε
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx _ _
    refine tendsto_atTop_of_eventually_const (i₀ := 1) ?_
    intro n hn
    have hn0 : n ≠ 0 := by
      omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hxn :
        x (Int.ofNat (k + 1)) = 0 := by
      simpa using hx k
    change dist (x (Int.ofNat (k + 1))) 0 = 0
    rw [hxn]
    exact dist_self 0

end MathlibExtTest.Dynamics.DelayedDifferenceEquation

end
