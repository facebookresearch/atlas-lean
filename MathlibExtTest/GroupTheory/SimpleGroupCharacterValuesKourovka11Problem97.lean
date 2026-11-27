/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.SimpleGroupCharacterValuesKourovka11Problem97
import MathlibExt.GroupTheory.BurnsidePaqb.CharacterOrthogonality

open MathlibExt.GroupTheory.SimpleGroupCharacterValuesKourovka11Problem97Wanted

-- Applying the refutation yields one common set of character values for arbitrarily large groups.
example :
    ∃ S : Set ℂ, S.Finite ∧ ∀ N : ℕ,
      ∃ (G : Type) (_ : Group G), Finite G ∧ IsSimpleGroup G ∧
        (∃ a b : G, a * b ≠ b * a) ∧ (∃ g : G, irrCharValues g = S) ∧ N < Nat.card G := by
  have h := finitelyManySimpleGivenCharacterValues_refuted
  unfold finitelyManySimpleGivenCharacterValues at h
  push Not at h
  exact h

-- The set of character values at an element of a finite group is never empty: the trivial
-- representation on `ℂ` is simple and its character takes the value `1` everywhere.
example {G : Type} [Group G] [Finite G] (g : G) : (1 : ℂ) ∈ irrCharValues g := by
  have := Fintype.ofFinite G
  exact ⟨FDRep.of (Representation.trivial ℂ G ℂ),
    BurnsidePaqb.simple_fdrep_of_irreducible G _, BurnsidePaqb.Irr.charFun_triv G g⟩
