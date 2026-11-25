/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Field.ZMod
import MathlibExt.NumberTheory.FunctionField.MonicMoebiusDivisors

/-! # Tests for the Möbius sum over monic divisors -/

open Polynomial UniqueFactorizationMonoid MetaMathlibExt

-- The unit polynomial has an empty Euler product.
example {F : Type*} [Field F] [Fintype F] :
    ∑ᶠ g ∈ {g : F[X] | g.Monic ∧ g ∣ 1},
      (moebius g : ℝ) / (Fintype.card F : ℝ) ^ g.natDegree = 1 := by
  have h : {p : F[X] | p.Monic ∧ Irreducible p ∧ p ∣ 1} = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr fun _ ⟨_, hp, hd⟩ ↦ hp.not_isUnit (isUnit_of_dvd_one hd)
  rw [monic_sum_moebius_div_norm monic_one, h, finprod_mem_empty]

-- Over the field with two elements, X² contributes just the Euler factor for X.
example :
    ∑ᶠ g ∈ {g : (ZMod 2)[X] | g.Monic ∧ g ∣ X ^ 2},
      (moebius g : ℝ) / 2 ^ g.natDegree = 1 / 2 := by
  have h : {p : (ZMod 2)[X] | p.Monic ∧ Irreducible p ∧ p ∣ X ^ 2} = {X} := by
    ext p
    constructor
    · rintro ⟨hm, hp, hd⟩
      exact eq_of_monic_of_associated hm monic_X
        ((hp.dvd_irreducible_iff_associated irreducible_X).mp (hp.prime.dvd_of_dvd_pow hd))
    · rintro (rfl : p = X)
      exact ⟨monic_X, irreducible_X, dvd_pow_self _ (by decide)⟩
  have heq := monic_sum_moebius_div_norm ((monic_X (R := ZMod 2)).pow 2)
  rw [h, finprod_mem_singleton] at heq
  norm_num [ZMod.card] at heq ⊢
  exact heq
