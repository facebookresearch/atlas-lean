/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.BottSamelsonFlagSchemes

/-!
# Tests for simple reflections and reduced words in type `A₂`
-/

open MathlibExt.AlgebraicGeometry.BottSamelsonFlagSchemes
open MathlibExt.AlgebraicGeometry.SchubertRankSchemes

/-- The two simple roots of `GL₃`. -/
private abbrev s₁ : SimpleRoot 3 := ⟨1, by decide⟩
private abbrev s₂ : SimpleRoot 3 := ⟨2, by decide⟩

/-- Simple roots give the adjacent transpositions. -/
example : simplePermutation s₁ = Equiv.swap 0 1 ∧ simplePermutation s₂ = Equiv.swap 1 2 := by
  decide

/-- The braid relation holds for the word permutations. -/
example : wordPermutation [s₁, s₂, s₁] = wordPermutation [s₂, s₁, s₂] := by decide

/-- The longest word evaluates to the reversal permutation. -/
example : wordPermutation [s₁, s₂, s₁] = Fin.revPerm := by decide

/-- `s₁ s₂ s₁` is reduced; `s₁ s₁` is not. -/
example : IsReducedWord [s₁, s₂, s₁] := by unfold IsReducedWord; decide

example : ¬ IsReducedWord [s₁, s₁] := by unfold IsReducedWord; decide
