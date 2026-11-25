/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_NumberField_finrank_cyclotomicField_three_eq_one_of_forall_isUnramifiedAt.lean`
and
`P2M/Sol/S_NumberField_finrank_cyclotomicField_three_eq_one_of_forall_isUnramifiedAt.lean`
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
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Unramified.Locus

import Mathlib.NumberTheory.Cyclotomic.Discriminant
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Different

@[expose] public section

open scoped NumberField
open scoped Real

attribute [local instance] FractionRing.liftAlgebra

namespace NumberField

private lemma natAbs_discr_cyclotomicField_three :
    (NumberField.discr (CyclotomicField 3 ℚ)).natAbs = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  haveI : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  have h := IsCyclotomicExtension.Rat.discr_prime (p := 3) (K := CyclotomicField 3 ℚ)
  rw [h]
  decide

private lemma differentIdeal_eq_top_of_forall_isUnramifiedAt
    {F : Type*} [Field F] [NumberField F] [Algebra (CyclotomicField 3 ℚ) F]
    (h : ∀ (P : Ideal (𝓞 F)) (_ : P.IsMaximal),
      Algebra.IsUnramifiedAt (𝓞 (CyclotomicField 3 ℚ)) P) :
    differentIdeal (𝓞 (CyclotomicField 3 ℚ)) (𝓞 F) = ⊤ := by
  by_contra hne
  obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hne
  haveI : P.IsPrime := hPmax.isPrime
  exact not_dvd_differentIdeal_iff.mpr (h P hPmax) (Ideal.dvd_iff_le.mpr hle)

private theorem natAbs_discr_eq_three_pow_of_forall_isUnramifiedAt
    {F : Type*} [Field F] [NumberField F] [Algebra (CyclotomicField 3 ℚ) F]
    (h : ∀ (P : Ideal (𝓞 F)) (_ : P.IsMaximal),
      Algebra.IsUnramifiedAt (𝓞 (CyclotomicField 3 ℚ)) P) :
    (NumberField.discr F).natAbs = 3 ^ Module.finrank (CyclotomicField 3 ℚ) F := by
  have tower := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    (CyclotomicField 3 ℚ) (𝓞 (CyclotomicField 3 ℚ)) F (𝓞 F)
  rw [differentIdeal_eq_top_of_forall_isUnramifiedAt h, Ideal.absNorm_top, one_mul,
    natAbs_discr_cyclotomicField_three] at tower
  exact tower

private lemma finrank_rat_cyclotomicField_three :
    Module.finrank ℚ (CyclotomicField 3 ℚ) = 2 := by
  haveI : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  rw [IsCyclotomicExtension.finrank (n := 3) (CyclotomicField 3 ℚ)
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
  decide

private lemma finrank_rat_eq_two_mul
    {F : Type*} [Field F] [NumberField F] [Algebra (CyclotomicField 3 ℚ) F] :
    Module.finrank ℚ F = 2 * Module.finrank (CyclotomicField 3 ℚ) F := by
  haveI : IsScalarTower ℚ (CyclotomicField 3 ℚ) F :=
    IsScalarTower.of_algebraMap_eq' (by apply RingHom.ext_rat)
  rw [← Module.finrank_mul_finrank ℚ (CyclotomicField 3 ℚ) F,
    finrank_rat_cyclotomicField_three]

private lemma numeric_bound {m : ℕ} (hm : 2 ≤ m) :
    (3 : ℝ) ^ m < (4 / 9) * (3 * π / 4) ^ (2 * m) := by
  have hpi : (9 : ℝ) / 4 < 3 * π / 4 := by linarith [Real.pi_gt_three]
  have key : (3 : ℝ) ^ m < (4 / 9) * ((9 : ℝ) / 4) ^ (2 * m) := by
    have heq : (4 / 9 : ℝ) * ((9 : ℝ) / 4) ^ (2 * m) = (4 / 9) * (81 / 16) ^ m := by
      rw [pow_mul]; norm_num
    rw [heq]
    have h2716 : (9 / 4 : ℝ) < (27 / 16) ^ m :=
      calc (9 / 4 : ℝ) < (27 / 16) ^ 2 := by norm_num
        _ ≤ (27 / 16) ^ m := pow_le_pow_right₀ (by norm_num) hm
    have hmul : (9 / 4 : ℝ) * 3 ^ m < (81 / 16) ^ m := by
      have := mul_lt_mul_of_pos_right h2716 (show (0 : ℝ) < 3 ^ m by positivity)
      rwa [← mul_pow, show (27 / 16 : ℝ) * 3 = 81 / 16 by norm_num] at this
    linarith
  calc (3 : ℝ) ^ m
      < (4 / 9) * ((9 : ℝ) / 4) ^ (2 * m) := key
    _ ≤ (4 / 9) * (3 * π / 4) ^ (2 * m) := by
        have h94 : (0 : ℝ) ≤ 9 / 4 := by norm_num
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h94 hpi.le _) (by norm_num)

/-- An extension of `ℚ(ζ₃)` that is unramified at every maximal ideal of its
ring of integers is trivial: its degree over `ℚ(ζ₃)` is one.

Unramifiedness forces the different ideal to be trivial, so the absolute
discriminant of the extension is a power of `3`. Minkowski's discriminant
bound then rules out every degree at least two over `ℚ(ζ₃)`. -/
public theorem finrank_cyclotomicField_three_eq_one_of_forall_isUnramifiedAt
    {F : Type*} [Field F] [NumberField F] [Algebra (CyclotomicField 3 ℚ) F]
    (h : ∀ (P : Ideal (𝓞 F)) (_ : P.IsMaximal),
      Algebra.IsUnramifiedAt (𝓞 (CyclotomicField 3 ℚ)) P) :
    Module.finrank (CyclotomicField 3 ℚ) F = 1 := by
  have hn := finrank_rat_eq_two_mul (F := F)
  have hF_pos : 0 < Module.finrank ℚ F := Module.finrank_pos
  by_contra hne
  set m := Module.finrank (CyclotomicField 3 ℚ) F with hm_def
  have hm2 : 2 ≤ m := by omega
  have h1n : 1 < Module.finrank ℚ F := by omega
  have hmink : (4 / 9 : ℝ) * (3 * π / 4) ^ (2 * m) ≤ (3 : ℝ) ^ m := by
    have h0 := NumberField.abs_discr_ge h1n
    rw [hn] at h0
    have hdiscr := natAbs_discr_eq_three_pow_of_forall_isUnramifiedAt h
    rw [← hm_def] at hdiscr
    calc (4 / 9 : ℝ) * (3 * π / 4) ^ (2 * m)
        ≤ (↑|NumberField.discr F| : ℝ) := h0
      _ = ((NumberField.discr F).natAbs : ℝ) := (Nat.cast_natAbs _).symm
      _ = ((3 ^ m : ℕ) : ℝ) := by rw [hdiscr]
      _ = (3 : ℝ) ^ m := by push_cast; ring
  exact absurd hmink (not_le.mpr (numeric_bound hm2))

end NumberField
