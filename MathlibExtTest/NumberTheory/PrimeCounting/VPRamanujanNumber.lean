/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.VPRamanujanNumber

namespace MetaMathlibExt

example (x : ℝ) : primeCountingWithin ∅ x = 0 := by
  simp [primeCountingWithin]

example (P : Set ℕ) (v : ℝ) (m R : ℕ) :
    IsVPRamanujanNumber P v m R ↔
      P.Infinite ∧ P ⊆ {p : ℕ | p.Prime} ∧ 1 < v ∧
        Minimal (· ∈ {R' : ℕ | ∀ x : ℝ, (R' : ℝ) ≤ x →
          (m : ℤ) ≤ (primeCountingWithin P x : ℤ) -
            (primeCountingWithin P (x / v) : ℤ)}) R :=
  Iff.rfl

#print axioms primeCountingWithin
#print axioms IsVPRamanujanNumber

end MetaMathlibExt
