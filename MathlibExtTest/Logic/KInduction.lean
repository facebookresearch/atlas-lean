/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Logic.KInduction
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.NormNum

@[expose] public section

/-- Boundary check: for the constant transition system on
`ℕ` (stay in place) with bad states `Odd`, `k = 1` induction
applies from the initial state `0`. -/
example : ∀ p : ℕ → ℕ, p 0 = 0 → (∀ i, p (i + 1) = p i) →
    ∀ i, ¬ Odd (p i) := by
  intro p h0 hstep
  apply MetaMathlibExt.k_induction_sound (step := fun a b : ℕ => b = a)
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
