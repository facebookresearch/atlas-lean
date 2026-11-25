/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.Matching.StableMatchingLattice
public import MathlibExt.GameTheory.Matching.StableMechanism

/-! # Tests for the men's join of stable matchings, on Roth's market -/

namespace MathlibExtTest.GameTheory.Matching.StableMatchingLattice

open MathlibExt.Combinatorics.Matching.GaleShapley
open MathlibExt.GameTheory.Matching.StableMechanism
open MathlibExt.GameTheory.Matching.StableMatchingLattice

theorem hx : IsStable rothMenPrefs rothWomenPrefs rothX := (roth_isStable_iff _).2 (Or.inl rfl)

theorem hy : IsStable rothMenPrefs rothWomenPrefs rothY := (roth_isStable_iff _).2 (Or.inr rfl)

/-- In Roth's market the men's join of `x` and `y`, in either order, is the men-preferred `x`:
a non-degenerate instance in which the two matchings differ. -/
example : ∀ m, menJoin rothWomenPrefs hx hy m = rothX m := by
  intro m; rw [menJoin_apply]; revert m; decide

example : ∀ m, menJoin rothWomenPrefs hy hx m = rothX m := by
  intro m; rw [menJoin_apply]; revert m; decide

/-- The join is stable, and it is one of the two stable matchings of Roth's market. -/
example : menJoin rothWomenPrefs hx hy = rothX ∨ menJoin rothWomenPrefs hx hy = rothY :=
  (roth_isStable_iff _).1 (isStable_menJoin rothWomenPrefs hx hy)

/-- Opposition of interests on Roth's market: women weakly prefer `y` to the join. -/
example (w : Fin 3) :
    ¬ (rothWomenPrefs w).lt ((menJoin rothWomenPrefs hx hy).symm w) (rothY.symm w) :=
  not_lt_menJoin_symm_right rothWomenPrefs hx hy w

#print axioms isStable_menJoin
#print axioms not_lt_menJoin_symm_left
#print axioms not_lt_menJoin_symm_right

end MathlibExtTest.GameTheory.Matching.StableMatchingLattice
