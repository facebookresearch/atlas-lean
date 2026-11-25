/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.NilpotentExtensionSplitAtPrimesKourovka12Problem93

open MathlibExt.GroupTheory.NilpotentExtensionSplitAtPrimesKourovka12Problem93Wanted

-- The generator of the integer lattice has no cube root.
example : ¬ IsPLocal 2 (Multiplicative ℤ) := by
  intro h
  obtain ⟨x, hx⟩ := (h 3 (by decide)).surjective (Multiplicative.ofAdd 1)
  have hx' : (3 : ℤ) * x.toAdd = 1 := congrArg Multiplicative.toAdd hx
  omega

-- Extract a projection witnessing local splitting and failure of integral splitting.
example : ∃ (G Q : Type) (_ : Group G) (_ : Group Q), Group.IsNilpotent G ∧
    Group.IsNilpotent Q ∧ Group.FG Q ∧ ∃ π : G →* Q, Function.Surjective π ∧
      (∀ p : ℕ, p.Prime → SplitsAtPrime p π) ∧ ¬ ∃ s : Q →* G, π.comp s = MonoidHom.id Q := by
  by_contra h
  apply nilpotentExtensionSplitsIfSplitsAtPrimes_refuted
  intro N G Q instN instG instQ _ hG hQ hfg i π _ hπ _ hlocal
  by_contra hn
  exact h ⟨G, Q, instG, instQ, hG, hQ, hfg, π, hπ, hlocal, hn⟩
