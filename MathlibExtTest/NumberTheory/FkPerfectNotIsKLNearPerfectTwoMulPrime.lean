/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FkPerfectNotIsKLNearPerfectTwoMulPrime
open MathlibExt.NumberTheory.FkPerfectWanted

namespace MathlibExtTest.NumberTheory.FkPerfect

-- Twice three is not `[k,ℓ]`-near-perfect.
example (k l : ℕ) (hl : 1 ≤ l) : ¬ IsKLNearPerfect k l 6 :=
  not_isKLNearPerfect_two_mul_prime (k := k) (l := l) (p := 3)
    (hl := hl) (hp := by decide) (hpo := ⟨1, rfl⟩)

example : ¬ IsKLNearPerfect 2 1 10 :=
  not_isKLNearPerfect_two_mul_prime (k := 2) (l := 1) (p := 5)
    (hl := by decide) (hp := by decide) (hpo := ⟨2, rfl⟩)

end MathlibExtTest.NumberTheory.FkPerfect
