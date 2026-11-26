/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.FLT.Regular
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.Tactic.NormNum.Basic

/-! # Tests for Fermat's Last Theorem for regular primes -/

@[expose] public section

open scoped NumberField

-- `exactSource` consumer with the original statement.
private theorem exactSource {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hreg : ¬ p ∣ NumberField.classNumber K) : FermatLastTheoremFor p :=
  MetaMathlibExt.fermatLastTheoremFor_of_regular hp hp2 K hreg

/-- The canonical `p`-th cyclotomic field is a `p`-th cyclotomic extension of `ℚ`, for the
`ℚ`-algebra structure that elaboration picks. -/
private theorem isCyclotomicExtension_cyclotomicField (p : ℕ) [NeZero p] :
    IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
  have : NeZero (p : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne p)⟩
  CyclotomicField.isCyclotomicExtension p ℚ

/-- The canonical cyclotomic-field form, with the class number written as the order of the
class group. -/
private theorem canonicalField {p : ℕ} [hp : Fact p.Prime]
    (hreg : p.Coprime (Fintype.card (ClassGroup (𝓞 (CyclotomicField p ℚ)))))
    (hodd : p ≠ 2) : FermatLastTheoremFor p :=
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have := isCyclotomicExtension_cyclotomicField p
  MetaMathlibExt.fermatLastTheoremFor_of_regular hp.out hodd (CyclotomicField p ℚ)
    ((Nat.Prime.coprime_iff_not_dvd hp.out).mp hreg)

/-- The statement with its binders unfolded, over the canonical field. -/
example {p : ℕ} [Fact p.Prime]
    (hreg : p.Coprime (Fintype.card (ClassGroup (𝓞 (CyclotomicField p ℚ)))))
    (hodd : p ≠ 2) (a b c : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a ^ p + b ^ p ≠ c ^ p :=
  canonicalField hreg hodd a b c ha hb hc

/-- The hypothesis can hold: the ring of integers of the third cyclotomic field is a principal
ideal domain, so its class number is `1`. -/
private theorem not_three_dvd_classNumber :
    ¬ 3 ∣ NumberField.classNumber (CyclotomicField 3 ℚ) := by
  have := isCyclotomicExtension_cyclotomicField 3
  rw [NumberField.classNumber_eq_one_iff.mpr (IsCyclotomicExtension.Rat.three_pid _)]
  norm_num

/-- The same for the fifth cyclotomic field. -/
private theorem not_five_dvd_classNumber :
    ¬ 5 ∣ NumberField.classNumber (CyclotomicField 5 ℚ) := by
  have := isCyclotomicExtension_cyclotomicField 5
  rw [NumberField.classNumber_eq_one_iff.mpr (IsCyclotomicExtension.Rat.five_pid _)]
  norm_num

/-- So the theorem applies to the exponents `3` and `5`. -/
example : FermatLastTheoremFor 3 :=
  have := isCyclotomicExtension_cyclotomicField 3
  MetaMathlibExt.fermatLastTheoremFor_of_regular Nat.prime_three (by norm_num)
    (CyclotomicField 3 ℚ) not_three_dvd_classNumber

example : FermatLastTheoremFor 5 :=
  have := isCyclotomicExtension_cyclotomicField 5
  MetaMathlibExt.fermatLastTheoremFor_of_regular Nat.prime_five (by norm_num)
    (CyclotomicField 5 ℚ) not_five_dvd_classNumber

/-- Boundary: the exponent matters, since `3 ^ 2 + 4 ^ 2 = 5 ^ 2`. -/
example : ¬ FermatLastTheoremFor 2 := fun h => h 3 4 5 (by norm_num) (by norm_num)
  (by norm_num) (by norm_num)
