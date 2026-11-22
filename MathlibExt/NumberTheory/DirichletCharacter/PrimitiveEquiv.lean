/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.DirichletCharacter.PrimitiveUniqueness

@[expose] public section

/-!
# Dirichlet characters as primitive characters at divisor levels

Let `M(m)` be the set of Dirichlet characters of modulus `m` and `X(m)` the set of
primitive Dirichlet characters of modulus dividing `m`. Every character `χ` of
modulus `m` is induced by a unique primitive character, namely its canonical
primitive character `χ.primitiveCharacter` at level `χ.conductor`. This file
packages the chain of correspondences `M(m) ≃ X(m) ≃ Ĝ(m)`.

The uniqueness half of the correspondence is
`DirichletCharacter.primitiveCharacter_isPrimitive_and_unique` in
`MathlibExt/NumberTheory/DirichletCharacter/PrimitiveUniqueness.lean`
(Theorem 18.13 of the source below); the new content here is the packaged
equivalence, whose inverse direction needs the conductor computation that a
primitive character induces a character of the same conductor.

## Main results

* `DirichletCharacter.PrimitiveInducer`: a primitive Dirichlet character at a
  level dividing `m`, i.e. an element of `X(m)`.
* `DirichletCharacter.equivPrimitiveInducer`: the equivalence `M(m) ≃ X(m)`
  of Corollary 18.16.
* `DirichletCharacter.PrimitiveInducer.equivUnitHom`: the equivalence
  `X(m) ≃ Ĝ(m)` of the same corollary.

The second bijection composes induction to level `m` with Mathlib's
`MulChar.equivToUnitHom` to the character group of `(ZMod m)ˣ`.

ATLAS source: ATLAS `NumberTheoryI`, Section 18.2.1, Corollary 18.16.
The source formalization is `v1/Atlas/NumberTheoryI/code/Cor1816.lean`
(`DirichletCharacter.cor_18_16_M_equiv_X`), which proves the same equivalence
for the bespoke structure `PrimCharDvd`. The structure here is renamed to
Mathlib style, and its key conductor lemma is now Mathlib's
`DirichletCharacter.conductor_changeLevel` rather than the bespoke argument
in the source.
-/

namespace DirichletCharacter

variable {R : Type*} [CommMonoidWithZero R] {m : ℕ}

/-- A primitive Dirichlet character at a level dividing `m`: an element of the
set `X(m)` of Corollary 18.16. The bundled character `char` is primitive at
its own level, and `changeLevel level_dvd char` is the induced character of
modulus `m`. -/
structure PrimitiveInducer (R : Type*) [CommMonoidWithZero R] (m : ℕ) where
  level : ℕ
  level_dvd : level ∣ m
  char : DirichletCharacter R level
  isPrimitive : char.IsPrimitive

namespace PrimitiveInducer

/-- Two primitive inducers are equal when their levels agree and their
characters agree after casting along the level equality. -/
theorem ext {p q : PrimitiveInducer R m} (hlevel : p.level = q.level)
    (hchar : hlevel ▸ p.char = q.char) : p = q := by
  obtain ⟨d₁, hd₁, χ₁, hp₁⟩ := p
  obtain ⟨d₂, hd₂, χ₂, hp₂⟩ := q
  dsimp only at hlevel hchar
  subst hlevel
  simp only at hchar
  subst hchar
  rfl

/-- Casting a character along a level equality commutes with `changeLevel`:
the cast can be pushed inside, at the cost of casting the divisibility proof
(which is irrelevant by proof irrelevance). -/
private theorem changeLevel_cast_eq {d₁ d₂ : ℕ} (heq : d₁ = d₂)
    (hd₂ : d₂ ∣ m) (ψ : DirichletCharacter R d₁) :
    changeLevel hd₂ (heq ▸ ψ) = changeLevel (show d₁ ∣ m from heq ▸ hd₂) ψ := by
  subst heq
  rfl

end PrimitiveInducer

/-- Corollary 18.16: Dirichlet characters of modulus `m` are in bijection with
primitive Dirichlet characters of modulus dividing `m`. The forward map sends
`χ` to its primitive character at level `χ.conductor`; the inverse map induces
a primitive character up to level `m` via `changeLevel`. -/
noncomputable def equivPrimitiveInducer (m : ℕ) (hm : m ≠ 0) :
    DirichletCharacter R m ≃ PrimitiveInducer R m where
  toFun χ :=
    { level := χ.conductor
      level_dvd := χ.conductor_dvd_level
      char := χ.primitiveCharacter
      isPrimitive := χ.primitiveCharacter_isPrimitive }
  invFun p := changeLevel p.level_dvd p.char
  left_inv χ := changeLevel_primitiveCharacter χ
  right_inv p := by
    obtain ⟨d, hd, ψ, hprim⟩ := p
    have : NeZero m := ⟨hm⟩
    have hlevel : (changeLevel hd ψ).conductor = d :=
      (conductor_changeLevel ψ hd).trans hprim
    apply PrimitiveInducer.ext hlevel
    apply changeLevel_injective hd
    rw [PrimitiveInducer.changeLevel_cast_eq hlevel hd]
    exact changeLevel_primitiveCharacter (changeLevel hd ψ)

/-- The level of the primitive inducer of `χ` is its conductor. -/
theorem equivPrimitiveInducer_level (χ : DirichletCharacter R m) (hm : m ≠ 0) :
    (equivPrimitiveInducer m hm χ).level = χ.conductor :=
  rfl

/-- The character of the primitive inducer of `χ` is its primitive character. -/
theorem equivPrimitiveInducer_char (χ : DirichletCharacter R m) (hm : m ≠ 0) :
    ((equivPrimitiveInducer m hm χ).char : DirichletCharacter R χ.conductor) =
      χ.primitiveCharacter :=
  rfl

/-- The second bijection of Corollary 18.16: primitive characters at divisor
levels correspond to characters of the unit group modulo `m`. -/
noncomputable def PrimitiveInducer.equivUnitHom (m : ℕ) (hm : m ≠ 0) :
    PrimitiveInducer R m ≃ ((ZMod m)ˣ →* Rˣ) :=
  (equivPrimitiveInducer m hm).symm.trans MulChar.equivToUnitHom

/-- The unit-group character evaluates the primitive character induced to
level `m`. -/
@[simp] theorem PrimitiveInducer.equivUnitHom_apply
    (p : PrimitiveInducer R m) (hm : m ≠ 0) (u : (ZMod m)ˣ) :
    (PrimitiveInducer.equivUnitHom m hm p u : R) =
      changeLevel p.level_dvd p.char (u : ZMod m) :=
  MulChar.coe_equivToUnitHom _ _

end DirichletCharacter

end
