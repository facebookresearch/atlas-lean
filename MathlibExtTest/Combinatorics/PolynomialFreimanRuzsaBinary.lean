/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.PolynomialFreimanRuzsaBinary

open MathlibExt.Combinatorics.PolynomialFreimanRuzsaBinaryWanted
open scoped Pointwise

-- An exponent strictly between zero and one still fails the uniform bound.
example : ¬ IsAsymptoticCosetCoverExponent (3 / 4) := by
  intro h
  have := basisVectorsLowerBound1_holds (3 / 4) h
  norm_num at this

-- A singleton admits a cover of size one by a translate of the zero subspace.
example {n : ℕ} (a : BinaryAmbientSpace n) :
    ∃ H : Submodule (ZMod 2) (BinaryAmbientSpace n),
      Nat.card H ≤ ({a} : Finset (BinaryAmbientSpace n)).card ∧
        CovByVAdd (BinaryAmbientSpace n) 1
          (({a} : Finset (BinaryAmbientSpace n)) : Set (BinaryAmbientSpace n)) H := by
  refine ⟨⊥, by simp, {a}, by simp, ?_⟩
  intro x hx
  have hxa : x = a := by simpa using hx
  subst x
  exact Set.mem_vadd.mpr ⟨a, by simp, 0, Submodule.zero_mem _, by simp⟩
