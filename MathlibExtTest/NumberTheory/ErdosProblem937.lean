/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.ErdosProblem937

open MathlibExt.NumberTheory.ErdosProblem937Wanted

example : {p : ℕ × ℕ | IsCoprimePowerfulAP4 p.1 p.2}.Infinite := conjecture_holds

example (a : ℕ) : ¬ IsCoprimePowerfulAP4 a 0 := fun h => (Nat.lt_irrefl 0) h.1

-- The terms 1, 9, 17, 25 are pairwise coprime, but 17 is not powerful.
example : ¬ IsCoprimePowerfulAP4 1 8 := by
  rintro ⟨_, _, _, h, _⟩
  exact (by decide : ¬ 17 ^ 2 ∣ 17) (h.2 17 (by decide) (by decide))

-- The terms 36, 72, 108, 144 are all powerful but share prime factors.
example : ¬ IsCoprimePowerfulAP4 36 36 := by
  rintro ⟨_, _, _, _, _, h, _⟩
  exact (by decide : ¬ Nat.Coprime 36 72) h
