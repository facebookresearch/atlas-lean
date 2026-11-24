/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
import MathlibExt.GroupTheory.Abelianization.PerfectKernel

/-! # Abelianizing the sign homomorphism on five letters -/

open Group

private abbrev signFive : Equiv.Perm (Fin 5) →* ℤˣ := Equiv.Perm.sign

/-- Sign has perfect kernel A₅, so its induced map is bijective. -/
example : Function.Bijective (Group.Abelianization.map signFive) := by
  have : IsPerfect signFive.ker := by
    change IsPerfect (Equiv.Perm.sign (α := Fin 5)).ker
    rw [← alternatingGroup_eq_sign_ker]
    exact isPerfect_def.mpr
      (commutator_alternatingGroup_eq_top (by simp))
  exact Group.Abelianization.map_bijective_of_surjective_of_isPerfect_ker
    signFive (Equiv.Perm.sign_surjective (Fin 5))

/-- The image of a transposition is nonidentity: the induced map is not the zero map. -/
example : Group.Abelianization.map signFive
    (Group.Abelianization.of (Equiv.swap (0 : Fin 5) 1)) ≠ 1 := by
  rw [Group.Abelianization.map_of, Equiv.Perm.sign_swap (by decide : (0 : Fin 5) ≠ 1)]
  intro h
  have h' : (-1 : ℤˣ) = 1 := (Group.Abelianization.equivOfComm (H := ℤˣ)).injective
    (by simpa using h)
  exact (by decide : (-1 : ℤˣ) ≠ 1) h'
