/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimitiveLambdaRoots.Supermultiplicativity

open MathlibExt.NumberTheory.PrimitiveLambdaRootsWanted

example (n : ℕ) (hn : 1 < n) (ho : Odd n) :
    primitiveLambdaRootCount (n * 2) = primitiveLambdaRootCount n * primitiveLambdaRootCount 2 :=
  (primitiveLambdaRootCount_mul_ge_and_eq_iff n 2 hn (by decide) ho.coprime_two_right).2.mpr
    (Or.inr ⟨rfl, ho⟩)

-- Both Carmichael exponents are two.
example : primitiveLambdaRootCount 3 * primitiveLambdaRootCount 4 <
    primitiveLambdaRootCount 12 := by
  obtain ⟨hle, heq⟩ := primitiveLambdaRootCount_mul_ge_and_eq_iff 3 4
    (by decide) (by decide) (by decide)
  exact lt_of_le_of_ne hle fun h ↦ (by simpa using heq.mp h.symm : False)

-- The exponents four and two have different 2-adic valuations.
example : primitiveLambdaRootCount 5 * primitiveLambdaRootCount 3 <
    primitiveLambdaRootCount 15 := by
  obtain ⟨hle, heq⟩ := primitiveLambdaRootCount_mul_ge_and_eq_iff 5 3
    (by decide) (by decide) (by decide)
  exact lt_of_le_of_ne hle fun h ↦ (by simpa using heq.mp h.symm : False)
