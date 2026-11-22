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

/-- **Primitive characters at divisor levels.** Let $R$ be a commutative monoid with zero and $m$
a natural number. A primitive inducer of modulus $m$ with values in $R$ consists of a natural
number $d$, its level, with $d \mid m$, together with a Dirichlet character $\psi$ of level $d$
with values in $R$ that is primitive, that is, whose conductor is $d$. These are the elements of
the set $X(m)$ of Corollary 18.16; changing the level of $\psi$ from $d$ to $m$ gives the induced
Dirichlet character of level $m$. -/
structure PrimitiveInducer (R : Type*) [CommMonoidWithZero R] (m : ℕ) where
  level : ℕ
  level_dvd : level ∣ m
  char : DirichletCharacter R level
  isPrimitive : char.IsPrimitive

namespace PrimitiveInducer

/-- **Equality of primitive characters at divisor levels.** Let $R$ be a commutative monoid with
zero and $m$ a natural number, and let $p$ and $q$ be primitive inducers of modulus $m$ with
values in $R$. If $p$ and $q$ have the same level, and the character of $p$, transported along
this equality of levels, equals the character of $q$, then $p = q$. -/
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

/-- **Dirichlet characters correspond to primitive characters at divisor levels.** Let $R$ be a
commutative monoid with zero and $m \ge 1$ a natural number. This is the bijection from Dirichlet
characters of level $m$ with values in $R$ to primitive inducers of modulus $m$ (primitive
Dirichlet characters with values in $R$ whose level divides $m$) that sends $\chi$ to the
primitive character associated to $\chi$, whose level is the conductor of $\chi$. Its inverse
sends a primitive character $\psi$ of level $d \mid m$ to the Dirichlet character of level $m$
obtained from $\psi$ by changing the level from $d$ to $m$.

Source: ATLAS NumberTheoryI, Section 18.2.1, Corollary 18.16 (first bijection). -/
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

/-- **Level of the primitive inducer attached to a character.** Let $R$ be a commutative monoid
with zero, let $m \ge 1$, and let $\chi$ be a Dirichlet character of level $m$ with values in $R$.
The level of the primitive inducer that the bijection between Dirichlet characters of level $m$
and primitive inducers of modulus $m$ assigns to $\chi$ is the conductor of $\chi$. -/
theorem equivPrimitiveInducer_level (χ : DirichletCharacter R m) (hm : m ≠ 0) :
    (equivPrimitiveInducer m hm χ).level = χ.conductor :=
  rfl

/-- **Character of the primitive inducer attached to a character.** Let $R$ be a commutative
monoid with zero, let $m \ge 1$, and let $\chi$ be a Dirichlet character of level $m$ with values
in $R$. The character of the primitive inducer that the bijection between Dirichlet characters of
level $m$ and primitive inducers of modulus $m$ assigns to $\chi$, a Dirichlet character whose
level is the conductor of $\chi$, is the primitive character associated to $\chi$. -/
theorem equivPrimitiveInducer_char (χ : DirichletCharacter R m) (hm : m ≠ 0) :
    ((equivPrimitiveInducer m hm χ).char : DirichletCharacter R χ.conductor) =
      χ.primitiveCharacter :=
  rfl

/-- **Primitive characters at divisor levels correspond to unit-group characters.** Let $R$ be a
commutative monoid with zero and $m \ge 1$ a natural number. This is the bijection from primitive
inducers of modulus $m$ with values in $R$ to monoid homomorphisms
$(\mathbb{Z}/m\mathbb{Z})^\times \to R^\times$ that sends a primitive character $\psi$ of level
$d \mid m$ to the homomorphism $u \mapsto \chi(u)$, where $\chi$ is the Dirichlet character of
level $m$ obtained from $\psi$ by changing the level from $d$ to $m$.

Source: ATLAS NumberTheoryI, Section 18.2.1, Corollary 18.16 (second bijection). -/
noncomputable def PrimitiveInducer.equivUnitHom (m : ℕ) (hm : m ≠ 0) :
    PrimitiveInducer R m ≃ ((ZMod m)ˣ →* Rˣ) :=
  (equivPrimitiveInducer m hm).symm.trans MulChar.equivToUnitHom

/-- **Values of the unit-group character of a primitive inducer.** Let $R$ be a commutative monoid
with zero, let $m \ge 1$, and let $p$ be a primitive inducer of modulus $m$ with values in $R$,
with level $d$ and character $\psi$. For every unit $u$ of $\mathbb{Z}/m\mathbb{Z}$, the value at
$u$ of the homomorphism $(\mathbb{Z}/m\mathbb{Z})^\times \to R^\times$ corresponding to $p$,
viewed as an element of $R$, equals the value at $u$ of the Dirichlet character of level $m$
obtained from $\psi$ by changing the level from $d$ to $m$. -/
@[simp] theorem PrimitiveInducer.equivUnitHom_apply
    (p : PrimitiveInducer R m) (hm : m ≠ 0) (u : (ZMod m)ˣ) :
    (PrimitiveInducer.equivUnitHom m hm p u : R) =
      changeLevel p.level_dvd p.char (u : ZMod m) :=
  MulChar.coe_equivToUnitHom _ _

end DirichletCharacter

end
