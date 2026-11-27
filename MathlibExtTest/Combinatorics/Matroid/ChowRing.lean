/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Matroid.ChowRing

namespace ChowRingTest

open MathlibExt.Combinatorics.Matroid.Chow

variable {α : Type*} (M : Matroid α)

/-! Strictly submodular functions exist for every finite matroid, so the hypothesis of the hard
Lefschetz theorem and the Hodge–Riemann relations is satisfiable. -/

example [M.Finite] : ∃ c : Set α → ℝ, IsStrictlySubmodular M c :=
  ⟨_, isStrictlySubmodular_ncard_mul_ncard_diff M⟩

/-! The incomparability relations hold in the Chow ring. -/

example (F G : ProperFlat M) (h₁ : ¬ F.1 ⊆ G.1) (h₂ : ¬ G.1 ⊆ F.1) :
    x M F * x M G = 0 :=
  x_mul_x_eq_zero_of_incomparable M h₁ h₂

/-! The class `α_M` does not depend on the chosen element. -/

example {i j : α} (hi : i ∈ M.E) (hj : j ∈ M.E) : alphaClass M i = alphaClass M j :=
  alphaClass_eq M hi hj

/-! For a finite matroid, `β_M` does not depend on the chosen element either. -/

example [M.Finite] {i j : α} (hi : i ∈ M.E) (hj : j ∈ M.E) : betaClass M i = betaClass M j :=
  betaClass_eq M hi hj

/-! Generators have degree one, and so do their sums. -/

example (F G : ProperFlat M) : x M F + x M G ∈ gradedPiece M 1 :=
  add_mem (x_mem_gradedPiece_one M F) (x_mem_gradedPiece_one M G)

/-! The Lefschetz class has degree one. -/

example (c : Set α → ℝ) : ellClass M c ∈ gradedPiece M 1 :=
  ellClass_mem_gradedPiece_one M c

/-! A function that is not strictly submodular: the zero function fails the strict inequality
on any incomparable pair. -/

example (I₁ I₂ : Set α) (h₁ : I₁ ⊆ M.E) (h₂ : I₂ ⊆ M.E) (h₁₂ : ¬ I₁ ⊆ I₂) (h₂₁ : ¬ I₂ ⊆ I₁) :
    ¬ IsStrictlySubmodular M (fun _ => 0) := by
  rintro ⟨-, -, h⟩
  simpa using h I₁ I₂ h₁ h₂ h₁₂ h₂₁

end ChowRingTest
