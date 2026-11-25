/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Module_FaithfullyFlat_exists_algebraMap_eq_of_tmul_one_eq_one_tmul.lean`
and
`P2M/Sol/S_Module_FaithfullyFlat_exists_algebraMap_eq_of_tmul_one_eq_one_tmul.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import MathlibExt.RingTheory.Flat.FaithfullyFlat.Amitsur

import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

set_option autoImplicit false

open TensorProduct

universe u v w

/-- Consumer at the original binder universes. -/
private theorem exactSource
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] {b : B}
    (hb : b ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] b) :
    ∃ a : A, algebraMap A B a = b :=
  Module.FaithfullyFlat.exists_algebraMap_eq_of_tmul_one_eq_one_tmul hb

/-- Consumer in a higher universe, exercising universe polymorphism. -/
private theorem exactSource_higherUniverse
    {A : Type u} {B : Type (max v w)} [CommRing A] [CommRing B]
    [Algebra A B] [Module.FaithfullyFlat A B] {b : B}
    (hb : b ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] b) :
    ∃ a : A, algebraMap A B a = b :=
  Module.FaithfullyFlat.exists_algebraMap_eq_of_tmul_one_eq_one_tmul hb

/-- Elements coming from `A` always satisfy the tensor identity; the theorem gives the
converse when `B` is faithfully flat over `A`. -/
private theorem algebraMap_satisfies_identity
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (a : A) :
    algebraMap A B a ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] algebraMap A B a := by
  rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]

/-- The identity algebra satisfies the conclusion trivially. -/
private theorem self_example (b : ℤ) :
    ∃ a : ℤ, algebraMap ℤ ℤ a = b :=
  Module.FaithfullyFlat.exists_algebraMap_eq_of_tmul_one_eq_one_tmul
    (algebraMap_satisfies_identity b)

/-! ### Boundary: flatness alone does not suffice -/

/-- `ℚ` is flat over `ℤ`, being a localization of `ℤ`. -/
private theorem flat_int_rat : Module.Flat ℤ ℚ :=
  IsLocalization.flat ℚ (nonZeroDivisors ℤ)

/-- `ℚ` is not faithfully flat over `ℤ`: a faithfully flat algebra map is a local
homomorphism, and `2` becomes a unit in `ℚ` without being a unit in `ℤ`. -/
private theorem not_faithfullyFlat_int_rat : ¬ Module.FaithfullyFlat ℤ ℚ := by
  intro _
  have h2 : IsUnit (algebraMap ℤ ℚ 2) := by simp
  have h := IsUnit.of_map (algebraMap ℤ ℚ) 2 h2
  rw [Int.isUnit_iff] at h
  omega

/-- `1 / 2` satisfies the tensor identity in `ℚ ⊗[ℤ] ℚ`. -/
private theorem half_tmul_one_eq_one_tmul_half :
    (1 / 2 : ℚ) ⊗ₜ[ℤ] (1 : ℚ) = (1 : ℚ) ⊗ₜ[ℤ] (1 / 2 : ℚ) := by
  have h : (2 : ℤ) • (1 / 2 : ℚ) = 1 := by norm_num
  calc (1 / 2 : ℚ) ⊗ₜ[ℤ] (1 : ℚ) = (1 / 2 : ℚ) ⊗ₜ[ℤ] ((2 : ℤ) • (1 / 2 : ℚ)) := by rw [h]
    _ = ((2 : ℤ) • (1 / 2 : ℚ)) ⊗ₜ[ℤ] (1 / 2 : ℚ) := (smul_tmul _ _ _).symm
    _ = (1 : ℚ) ⊗ₜ[ℤ] (1 / 2 : ℚ) := by rw [h]

/-- `1 / 2` does not come from `ℤ`. -/
private theorem not_exists_algebraMap_eq_half : ¬ ∃ a : ℤ, algebraMap ℤ ℚ a = 1 / 2 := by
  rintro ⟨a, ha⟩
  rw [algebraMap_int_eq, eq_intCast] at ha
  have h : ((2 * a : ℤ) : ℚ) = ((1 : ℤ) : ℚ) := by
    push_cast
    rw [ha]
    norm_num
  have := Int.cast_injective h
  omega

/-- Faithful flatness cannot be weakened to flatness: for the flat algebra `ℤ → ℚ`, the
element `1 / 2` satisfies the tensor identity but does not come from `ℤ`. -/
private theorem not_forall_flat_exists_algebraMap_eq :
    ¬ ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B] {b : B},
      b ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] b → ∃ a : A, algebraMap A B a = b :=
  fun h => not_exists_algebraMap_eq_half
    (@h ℤ ℚ _ _ _ flat_int_rat _ half_tmul_one_eq_one_tmul_half)

/-- The theorem at `ℤ → ℚ`: faithful flatness would put `1 / 2` in the image of `ℤ`. -/
example (h : Module.FaithfullyFlat ℤ ℚ) : False :=
  not_exists_algebraMap_eq_half
    (Module.FaithfullyFlat.exists_algebraMap_eq_of_tmul_one_eq_one_tmul
      half_tmul_one_eq_one_tmul_half)
