/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RepresentationTheory.CharacterInnerProduct

/-!
# Tests for the character inner product, multiplicities and group averaging

Generic tests on the trivial representation, which needs no chemistry: its character
has norm one, its multiplicity in itself is one, and its intertwining rank agrees with
the multiplicity. The `Ci`/`C2` tests in
`PhyslibExtTest/Chemistry/Symmetry/GroupRepresentations.lean` exercise the same API
through the vector and quadratic representations.
-/

@[expose] public section

namespace MathlibExtTest.RepresentationTheory.CharacterInnerProduct

open CharacterTheory Representation

/-- The trivial character has norm one. -/
example {G : Type*} [Group G] [Fintype G] :
    charInner (trivial ℂ G ℂ).character (trivial ℂ G ℂ).character = 1 :=
  charInner_character_self (trivial ℂ G ℂ)

/-- The trivial representation occurs in itself exactly once. -/
example {G : Type*} [Group G] [Fintype G] :
    irrepMultiplicity (trivial ℂ G ℂ) (trivial ℂ G ℂ) = 1 := by
  rw [irrepMultiplicity_of_isIrreducible, ite_eq_left ⟨Representation.Equiv.refl _⟩]

/-- For an irreducible representation the intertwining rank is the multiplicity. -/
example {G : Type*} [Group G] [Fintype G] :
    intertwiningRank (trivial ℂ G ℂ) (trivial ℂ G ℂ) = 1 := by
  change irrepMultiplicity (trivial ℂ G ℂ) (trivial ℂ G ℂ) = 1
  rw [irrepMultiplicity_of_isIrreducible, ite_eq_left ⟨Representation.Equiv.refl _⟩]

/-- The reduction formula for the trivial representation: its multiplicity in itself is
the character inner product of its character with itself. -/
example {G : Type*} [Group G] [Fintype G] :
    (irrepMultiplicity (trivial ℂ G ℂ) (trivial ℂ G ℂ) : ℂ) =
      charInner (trivial ℂ G ℂ).character (trivial ℂ G ℂ).character :=
  irrepMultiplicity_eq_charInner _ _

end MathlibExtTest.RepresentationTheory.CharacterInnerProduct

/-! ### Axioms of the new declarations -/

#print axioms CharacterTheory.intertwiningRank
#print axioms CharacterTheory.irrepMultiplicity
#print axioms CharacterTheory.intertwiningRank_eq_charInner
#print axioms CharacterTheory.irrepMultiplicity_eq_charInner
#print axioms CharacterTheory.irrepMultiplicity_of_isIrreducible
