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

-- Minimum level `N = 2`: the exponents exist and the order at `(1, 0)` is
-- positive. This level exercises no strict comparison: every primitive pair
-- of `ZMod 2` is excluded, either because `y = 1 = -1` or because the pair is
-- `(1, 0)` itself, as the next example checks.
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

-- At `N = 2` the comparison set is empty.
example : ∀ x y : ZMod 2, (∃ a b : ZMod 2, a * x + b * y = 1) →
    ¬ (y = 0 ∧ (x = 1 ∨ x = -1)) → ¬ (y = 1 ∨ y = -1) → False := by
  decide

-- Strict comparisons at level `N = 5`: the pairs `(2, 0)` and `(1, 2)` are
-- primitive and lie outside both exceptional families, so the order at
-- `(1, 0)` is strictly smaller than the order at each of them.
example :
    ∃ (m : ZMod 5 → ZMod 5 → ℕ) (Ord : ZMod 5 → ZMod 5 → ℤ),
      (∀ x y : ZMod 5, Ord x y =
        ∑ r : ZMod 5, ∑ s : ZMod 5, (m r s : ℤ) *
          (6 * (((r * x + s * y).val : ℕ) : ℤ) ^ 2
            - 6 * (5 : ℤ) * (((r * x + s * y).val : ℕ) : ℤ) + (5 : ℤ) ^ 2)) ∧
      m 0 0 = 0 ∧
      (∀ r s : ZMod 5, m r (s + r) = m r s) ∧
      0 < Ord 1 0 ∧ Ord 1 0 < Ord 2 0 ∧ Ord 1 0 < Ord 1 2 := by
  obtain ⟨m, Ord, hOrd, hm00, hinv, hpos, hpeak⟩ :=
    ModularCurve.SiegelUnit.exists_peaked_exponent 5 (by norm_num)
  exact ⟨m, Ord, hOrd, hm00, hinv, hpos,
    hpeak 2 0 ⟨3, 0, by decide⟩ (by decide) (by decide),
    hpeak 1 2 ⟨1, 0, by decide⟩ (by decide) (by decide)⟩
