/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Sign.Defs
public import Mathlib.Data.Finset.Insert
import Mathlib.Basic.Sign.Basic

/-!
# Sign domain for abstract interpretation

The sign abstraction maps an integer to its sign in Mathlib's `SignType`,
via `SignType.sign`. The abstract operations `addSigns` and `mulSigns` map
the signs of two operands to a finite set of signs for their sum or product.
`sign_add_mem_addSigns` and `sign_mul_mem_mulSigns` prove both sound: the
sign of the concrete sum or product always lies in the abstract result.
Abstract multiplication is exact (`mulSigns_eq_singleton`), so its soundness
is Mathlib's `sign_mul`.

Packaging this domain as a Galois connection for the fixpoint framework of
`CSLibExt.Languages.AbstractInterpretation`, and using it to analyze a
concrete language, are not formalized here.
-/

@[expose] public section

namespace Cslib.AbstractInterpretation

/-- Abstract addition on signs: `addSigns s t` contains the sign of every sum
of an integer of sign `s` and an integer of sign `t`
(`sign_add_mem_addSigns`). A negative plus a positive integer can have any
sign. -/
def addSigns : SignType → SignType → Finset SignType
  | .neg, .neg => {.neg}
  | .neg, .zero => {.neg}
  | .neg, .pos => {.neg, .zero, .pos}
  | .zero, t => {t}
  | .pos, .neg => {.neg, .zero, .pos}
  | .pos, .zero => {.pos}
  | .pos, .pos => {.pos}

/-- Abstract multiplication on signs: `mulSigns s t` contains the sign of
every product of an integer of sign `s` and an integer of sign `t`
(`sign_mul_mem_mulSigns`). -/
def mulSigns : SignType → SignType → Finset SignType
  | .zero, _ => {.zero}
  | _, .zero => {.zero}
  | .neg, .neg => {.pos}
  | .neg, .pos => {.neg}
  | .pos, .neg => {.neg}
  | .pos, .pos => {.pos}

/-- Every integer is negative, zero, or positive, with the matching sign. -/
private theorem sign_cases (z : ℤ) :
    (z < 0 ∧ SignType.sign z = -1) ∨ (z = 0 ∧ SignType.sign z = 0) ∨
      (0 < z ∧ SignType.sign z = 1) := by
  rcases lt_trichotomy z 0 with h | h | h
  · exact Or.inl ⟨h, sign_neg h⟩
  · exact Or.inr (Or.inl ⟨h, by rw [h, sign_zero]⟩)
  · exact Or.inr (Or.inr ⟨h, sign_pos h⟩)

/-- Soundness of abstract addition: the sign of a sum lies in the abstract
sum of the signs of its operands. -/
theorem sign_add_mem_addSigns (a b : ℤ) :
    SignType.sign (a + b) ∈ addSigns (SignType.sign a) (SignType.sign b) := by
  rcases sign_cases a with ⟨ha, ha'⟩ | ⟨ha, ha'⟩ | ⟨ha, ha'⟩ <;>
    rcases sign_cases b with ⟨hb, hb'⟩ | ⟨hb, hb'⟩ | ⟨hb, hb'⟩ <;>
    rcases sign_cases (a + b) with ⟨hc, hc'⟩ | ⟨hc, hc'⟩ | ⟨hc, hc'⟩ <;>
    first
    | omega
    | (rw [ha', hb', hc']; decide)

/-- Abstract multiplication is exact: it returns the single sign given by
multiplication in `SignType`. -/
theorem mulSigns_eq_singleton (s t : SignType) : mulSigns s t = {s * t} := by
  cases s <;> cases t <;> rfl

/-- Soundness of abstract multiplication: the sign of a product lies in the
abstract product of the signs of its factors. -/
theorem sign_mul_mem_mulSigns (a b : ℤ) :
    SignType.sign (a * b) ∈ mulSigns (SignType.sign a) (SignType.sign b) := by
  rw [mulSigns_eq_singleton, sign_mul]
  exact Finset.mem_singleton_self _

end Cslib.AbstractInterpretation
