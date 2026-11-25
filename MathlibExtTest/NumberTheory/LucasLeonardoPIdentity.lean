/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LucasLeonardoPIdentity

/-!
# Tests for the Lucas–Leonardo identity
-/

open MetaMathlibExt MathlibExt.NumberTheory.LeonardoPWanted

-- The term at zero uses the value at the negative predecessor.
example (p : ℕ) (hp : 1 ≤ p) : lucasLeonardoP p 0 = ((p : ℤ) + 1) - p * (-p : ℤ) := by
  simpa [leonardoPKZ, leonardoPK_of_le p p 0 (Nat.zero_le _)] using
    lucasLeonardoP_eq_leonardoPK p 0 hp

-- For p = 2 the first recurrence step uses Leonardo numbers 4 and 1.
example : lucasLeonardoP 2 3 = 10 := by
  rw [lucasLeonardoP_eq_leonardoPK 2 3 (by decide)]
  decide
