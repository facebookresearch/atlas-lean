/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SierpinskiMersenne

open MathlibExt.NumberTheory.SierpinskiMersenneWanted

-- At zero shift, the same progression works at exponent zero and for every exponent.
example : ∃ a d : ℕ, 0 < d ∧ ∀ r n : ℕ, Nat.IsComposite ((a + r * d) * 2 ^ n + 1) := by
  obtain ⟨a, d, hd, h⟩ := exists_arithProg_sierpinski_add_mersenne (t := 0)
  refine ⟨a, d, hd, fun r n => ?_⟩
  simpa only [show mersenne 0 = 0 by rfl, Nat.add_zero] using h r 0 (Nat.le_refl 0) n

-- Both endpoint shifts use the *same* witnesses; this also samples a later term at exponent zero.
example : ∃ a d : ℕ, 0 < d ∧
    (∀ r n : ℕ, Nat.IsComposite ((a + r * d) * 2 ^ n + 1) ∧
      Nat.IsComposite ((a + r * d + 7) * 2 ^ n + 1)) ∧
    Nat.IsComposite (a + 2 * d + 1) ∧ Nat.IsComposite (a + 2 * d + 8) := by
  obtain ⟨a, d, hd, h⟩ := exists_arithProg_sierpinski_add_mersenne (t := 3)
  refine ⟨a, d, hd, fun r n => ⟨?_, h r 3 (Nat.le_refl 3) n⟩, ?_, ?_⟩
  · simpa only [show mersenne 0 = 0 by rfl, Nat.add_zero] using h r 0 (by decide) n
  · simpa only [show mersenne 0 = 0 by rfl, Nat.add_zero, pow_zero, mul_one] using
      h 2 0 (by decide) 0
  · simpa only [show mersenne 3 = 7 by rfl, pow_zero, mul_one, Nat.add_assoc] using
      h 2 3 (Nat.le_refl 3) 0
