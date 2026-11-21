/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.SiegelUnitPeakedExponent

@[expose] public section

-- `exactSource` consumer with the original binders.
example (N : ℕ) [NeZero N] (hN : 2 ≤ N) :
    ∃ (m : ZMod N → ZMod N → ℕ) (Ord : ZMod N → ZMod N → ℤ),
      (∀ x y : ZMod N, Ord x y =
        ∑ r : ZMod N, ∑ s : ZMod N, (m r s : ℤ) *
          (6 * (((r * x + s * y).val : ℕ) : ℤ) ^ 2
            - 6 * (N : ℤ) * (((r * x + s * y).val : ℕ) : ℤ) + (N : ℤ) ^ 2)) ∧
      m 0 0 = 0 ∧
      (∀ r s : ZMod N, m r (s + r) = m r s) ∧
      0 < Ord 1 0 ∧
      ∀ x y : ZMod N, (∃ a b : ZMod N, a * x + b * y = 1) →
        ¬ (y = 0 ∧ (x = 1 ∨ x = -1)) → ¬ (y = 1 ∨ y = -1) →
        Ord 1 0 < Ord x y :=
  ModularCurve.SiegelUnit.exists_peaked_exponent N hN

-- Boundary use at the smallest level: for `N = 2` the peaked exponent
-- exists, and the exceptional pair `(1, 0)` is a genuine peak: the
-- conclusion fails to demand strict increase there.
example :
    ∃ (m : ZMod 2 → ZMod 2 → ℕ) (Ord : ZMod 2 → ZMod 2 → ℤ),
      (∀ x y : ZMod 2, Ord x y =
        ∑ r : ZMod 2, ∑ s : ZMod 2, (m r s : ℤ) *
          (6 * (((r * x + s * y).val : ℕ) : ℤ) ^ 2
            - 6 * (2 : ℤ) * (((r * x + s * y).val : ℕ) : ℤ) + (2 : ℤ) ^ 2)) ∧
      m 0 0 = 0 ∧
      (∀ r s : ZMod 2, m r (s + r) = m r s) ∧
      0 < Ord 1 0 ∧
      ∀ x y : ZMod 2, (∃ a b : ZMod 2, a * x + b * y = 1) →
        ¬ (y = 0 ∧ (x = 1 ∨ x = -1)) → ¬ (y = 1 ∨ y = -1) →
        Ord 1 0 < Ord x y :=
  ModularCurve.SiegelUnit.exists_peaked_exponent 2 (by norm_num)
