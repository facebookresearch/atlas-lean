/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.FLT.Regular
import Mathlib.Tactic.NormNum.Basic

/-! # Tests for Fermat's Last Theorem for regular primes -/

@[expose] public section

open scoped NumberField

-- `exactSource` consumer with the original statement.
private theorem exactSource {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hreg : ¬ p ∣ NumberField.classNumber K) : FermatLastTheoremFor p :=
  MetaMathlibExt.fermatLastTheoremFor_of_regular hp hp2 K hreg

/-- The canonical cyclotomic-field form. -/
example {p : ℕ} [Fact p.Prime]
    (hreg : p.Coprime (Fintype.card (ClassGroup (𝓞 (CyclotomicField p ℚ)))))
    (hodd : p ≠ 2) : FermatLastTheoremFor p :=
  flt_regular hreg hodd

/-- The statement with its binders unfolded, over the canonical field. -/
example {p : ℕ} [Fact p.Prime]
    (hreg : p.Coprime (Fintype.card (ClassGroup (𝓞 (CyclotomicField p ℚ)))))
    (hodd : p ≠ 2) (a b c : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a ^ p + b ^ p ≠ c ^ p :=
  flt_regular hreg hodd a b c ha hb hc

/-- Boundary: the exponent matters, since `3 ^ 2 + 4 ^ 2 = 5 ^ 2`. -/
example : ¬ FermatLastTheoremFor 2 := fun h => h 3 4 5 (by norm_num) (by norm_num)
  (by norm_num) (by norm_num)
