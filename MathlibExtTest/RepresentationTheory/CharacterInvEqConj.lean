/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RepresentationTheory.CharacterInvEqConj
import Mathlib.Tactic

namespace MathlibExtTest.RepresentationTheory.CharacterInvEqConj

open CharacterTheory

universe u

/-- Applying `char_inv_eq_conj` at `g⁻¹`: the character at `g` is the
conjugate of the character at `g⁻¹` (conjugation is its own inverse). -/
example {G : Type u} [Group G] [Fintype G]
    {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    ρ.character g = starRingEnd ℂ (ρ.character g⁻¹) := by
  simpa using char_inv_eq_conj ρ g⁻¹

/-- The dual version also holds at `g⁻¹`: the dual character at `g⁻¹` is the
conjugate of the dual character at `g`. -/
example {G : Type u} [Group G] [Fintype G]
    {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    ρ.dual.character g⁻¹ = starRingEnd ℂ (ρ.dual.character g) :=
  char_inv_eq_conj ρ.dual g

/-- The trivial representation on `ℂ` has character constantly `1`, so
`char_inv_eq_conj` says `1 = conj 1`. -/
example {G : Type} [Group G] [Fintype G] (g : G) :
    (Representation.trivial ℂ G ℂ).character g⁻¹ = 1 := by
  rw [char_inv_eq_conj]
  have hchar : (Representation.trivial ℂ G ℂ).character g = 1 := by
    have hρ : (Representation.trivial ℂ G ℂ) g = LinearMap.id := rfl
    rw [show (Representation.trivial ℂ G ℂ).character g =
        LinearMap.trace ℂ ℂ ((Representation.trivial ℂ G ℂ) g) from rfl,
      hρ, LinearMap.trace_id]
    simp
  rw [hchar]
  simp

/-- The trivial representation on `ℂ × ℂ` has character constantly `2`, so
its dual character is `conj 2 = 2`. -/
example {G : Type} [Group G] [Fintype G] (g : G) :
    (Representation.trivial ℂ G (ℂ × ℂ)).dual.character g = 2 := by
  rw [char_dual_eq_conj]
  have hchar : (Representation.trivial ℂ G (ℂ × ℂ)).character g = 2 := by
    have hρ : (Representation.trivial ℂ G (ℂ × ℂ)) g = LinearMap.id := rfl
    rw [show (Representation.trivial ℂ G (ℂ × ℂ)).character g =
        LinearMap.trace ℂ (ℂ × ℂ) ((Representation.trivial ℂ G (ℂ × ℂ)) g) from rfl,
      hρ, LinearMap.trace_id]
    simp
  rw [hchar]
  exact map_ofNat _ _

end MathlibExtTest.RepresentationTheory.CharacterInvEqConj
