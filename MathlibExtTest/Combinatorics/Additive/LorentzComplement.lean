/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.Additive.LorentzComplement

open Filter
open scoped Pointwise

-- Check the full statement independently of the legacy `conjecture` definition.
example (A : Set ℕ) (hA : A.Infinite) :
    ∃ B : Set ℕ, B.HasDensity 0 ∧ ∀ᶠ n in atTop, n ∈ A + B :=
  MathlibExt.NumberTheory.ErdosProblem31Wanted.conjecture_holds A hA

-- The result applies to a sparse set that does not contain zero.
example :
    ∃ B : Set ℕ, B.HasDensity 0 ∧
      ∀ᶠ n in atTop, n ∈ Set.range (fun i : ℕ ↦ (2 : ℕ) ^ i) + B :=
  MathlibExt.NumberTheory.ErdosProblem31Wanted.conjecture_holds _
    (Set.infinite_range_of_injective (Nat.pow_right_injective le_rfl))
