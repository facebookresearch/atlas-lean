/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.MahlerPopkenComplexityMahlerPopkenComplexityTwoEqRecursionValue

namespace MathlibExtTest.NumberTheory.MahlerPopkenComplexityMahlerPopkenComplexityTwoEqRecursionValue

open MathlibExt.NumberTheory.MahlerPopkenComplexityWanted

-- The binary recursion at its lower endpoint.
example : mahlerPopkenComplexity 2 3 = mahlerPopkenRecursionValue 2 3 :=
  mahlerPopkenComplexity_two_eq_recursionValue 3 (by decide)

-- The recursion bounds the complexity of six by a factor pair.
example : mahlerPopkenComplexity 2 6 ≤
    mahlerPopkenComplexity 2 3 + mahlerPopkenComplexity 2 2 := by
  rw [mahlerPopkenComplexity_two_eq_recursionValue 6 (by decide)]
  exact Nat.sInf_le (Or.inl ⟨3, by decide, by decide, by decide, rfl⟩)

end MathlibExtTest.NumberTheory.MahlerPopkenComplexityMahlerPopkenComplexityTwoEqRecursionValue
