/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.PrismVerticals

/-! Public clients for vertical edges, natural sections, and boundary cases. -/

set_option autoImplicit false
noncomputable section

open CategoryTheory MonoidalCategory
open scoped Simplicial

universe u

namespace SSet

variable {A B C : SSet.{u}}

example (f : A ⟶ B) (F : B ⊗ Δ[1] ⟶ C)
    (hF : PrismOneVerticalsEquivalences F) :
    PrismOneVerticalsEquivalences ((f ▷ Δ[1]) ≫ F) :=
  prismOneVerticalsEquivalences_whiskerRight_comp f F hF

-- Degenerate prisms have equivalence verticals for arbitrary simplicial sets.
example (g : B ⟶ C) :
    PrismOneVerticalsEquivalences (CartesianMonoidalCategory.fst B Δ[1] ≫ g) :=
  prismOneVerticalsEquivalences_fst_comp g

example (f : A ⟶ B) (x : A _⦋0⦌) :
    (f ▷ Δ[1]).app _ (verticalOneSimplex x) =
      verticalOneSimplex (f.app _ x) :=
  whiskerRight_app_verticalOneSimplex f x

example (i : A ⟶ B) {m : ℕ} (k : Fin (m + 1)) :
    prismSectionAt A k ≫ (i ▷ Δ[m]) = i ≫ prismSectionAt B k :=
  prismSectionAt_comp_whiskerRight i k

example (X : SSet.{u}) {m : ℕ} (k : Fin (m + 1)) :
    prismSectionAt X k ≫ CartesianMonoidalCategory.fst X Δ[m] = 𝟙 X :=
  prismSectionAt_comp_fst X k

example {n : ℕ} (hn : 1 ≤ n) (x : Δ[n] _⦋0⦌) :
    Δ[n].σ 0 x ∈ (∂Δ[n]).obj _ :=
  sigma_zero_mem_boundary_of_one_le hn x

-- The zero boundary has no prescribed verticals in any product.
example {W : SSet.{u}} (F G : (∂Δ[0] : SSet.{u}) ⊗ W ⟶ C) : F = G :=
  eq_of_boundaryZero_tensor F G

end SSet

#print axioms SSet.prismOneVerticalsEquivalences_fst_comp
#print axioms SSet.prismOneVerticalsEquivalences_whiskerRight_comp
