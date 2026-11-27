/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.CompletelyAdditiveHeight.FiniteFibers

/-! # Tests for height functions with prescribed values at the primes -/

open MetaMathlibExt

-- The value `f 0` is unconstrained: `f 0 = 0` is allowed, and the prime-index height
-- (`f i = i`) has exactly one prime at each positive height.
example (n : ℕ) (hn : 1 ≤ n) :
    {p : ℕ | p.Prime ∧
      additiveOfPrimeValues (fun p => Nat.count Nat.Prime p + 1) p = n}.ncard = 1 := by
  have h := (isHeightFunction_of_finite_fibers (fun i => i) (fun _ hi => hi)
    (fun t _ => (Set.finite_singleton t).subset fun _ hi => hi.2)).2 n hn
  rw [h, show {i : ℕ | 1 ≤ i ∧ i = n} = {n} by
    ext i; simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]; omega]
  exact Set.ncard_singleton n

-- A constant positive value at every positive index has an infinite fiber, so the
-- finiteness hypothesis rules it out.
example : ¬ ∀ t, 1 ≤ t → {i : ℕ | 1 ≤ i ∧ (fun _ => 1 : ℕ → ℕ) i = t}.Finite := by
  intro h
  refine (h 1 le_rfl).not_infinite ?_
  exact (Set.Ici_infinite 1).mono fun i hi => ⟨hi, rfl⟩
