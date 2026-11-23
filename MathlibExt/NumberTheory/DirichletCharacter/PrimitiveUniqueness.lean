/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.DirichletCharacter.Basic

@[expose] public section

/-!
Uniqueness of the primitive Dirichlet character inducing a given character.

A primitive character at level `d` inducing `χ` at level `n` must live at
the conductor level, and transported to that level it coincides with the
canonical primitive character `χ.primitiveCharacter`.
-/

namespace DirichletCharacter

variable {R : Type*} [CommMonoidWithZero R] {n : ℕ} [NeZero n]

/-- **The level of a primitive inducer is the conductor.** Let $R$ be a commutative monoid with
zero, let $n \ge 1$ and $d$ be natural numbers with $d \mid n$, and let $\chi$ be a Dirichlet
character of level $n$ with values in $R$. If $\chi'$ is a primitive Dirichlet character of
level $d$ whose change of level to $n$ is $\chi$, then $d$ equals the conductor of $\chi$. -/
public theorem conductor_eq_of_isPrimitive_changeLevel {d : ℕ}
    {χ' : DirichletCharacter R d} (χ : DirichletCharacter R n)
    (hprim : χ'.IsPrimitive) (hd : d ∣ n)
    (h : changeLevel hd χ' = χ) : d = χ.conductor := by
  have hprim' : χ'.conductor = d := hprim
  have hcond := conductor_changeLevel χ' hd
  rw [h] at hcond
  exact hprim'.symm.trans hcond.symm

/-- **An inducer at the conductor level is the primitive character.** Let $R$ be a commutative
monoid with zero, let $n \ge 1$ and $d$ be natural numbers with $d \mid n$, and let $\chi$ be a
Dirichlet character of level $n$ with values in $R$ whose conductor is $d$. If $\chi'$ is a
Dirichlet character of level $d$ whose change of level to $n$ is $\chi$, then $\chi'$ is the
primitive character associated to $\chi$. -/
public theorem eq_primitiveCharacter_of_changeLevel_eq {d : ℕ}
    {χ' : DirichletCharacter R d} (χ : DirichletCharacter R n)
    (hlev : d = χ.conductor) (hd : d ∣ n)
    (h : changeLevel hd χ' = χ) :
    hlev ▸ χ' = χ.primitiveCharacter := by
  subst hlev
  have hcanon : changeLevel hd χ.primitiveCharacter = χ :=
    changeLevel_primitiveCharacter χ
  have heq : changeLevel hd χ' = changeLevel hd χ.primitiveCharacter := by
    rw [h, hcanon]
  exact changeLevel_injective hd heq

/-- **Existence and uniqueness of the primitive character inducing a Dirichlet character.** Let
$R$ be a commutative monoid with zero, let $n \ge 1$, and let $\chi$ be a Dirichlet character of
level $n$ with values in $R$. The primitive character associated to $\chi$, whose level is the
conductor of $\chi$, is primitive, and its change of level to $n$ is $\chi$. Moreover, if
$\chi'$ is a primitive Dirichlet character of some level $d$ with $d \mid n$ whose change of level
to $n$ is $\chi$, then $d$ is the conductor of $\chi$ and $\chi'$ is the primitive character
associated to $\chi$. -/
public theorem primitiveCharacter_isPrimitive_and_unique (χ : DirichletCharacter R n) :
    χ.primitiveCharacter.IsPrimitive ∧
      changeLevel (conductor_dvd_level χ) χ.primitiveCharacter = χ ∧
      ∀ (d : ℕ) (χ' : DirichletCharacter R d), χ'.IsPrimitive →
        ∀ (hd : d ∣ n), changeLevel hd χ' = χ →
          ∃ (hlev : d = χ.conductor), hlev ▸ χ' = χ.primitiveCharacter := by
  refine ⟨primitiveCharacter_isPrimitive χ, changeLevel_primitiveCharacter χ,
    fun d χ' hprim hd h => ?_⟩
  have hlev := conductor_eq_of_isPrimitive_changeLevel χ hprim hd h
  exact ⟨hlev, eq_primitiveCharacter_of_changeLevel_eq χ hlev hd h⟩

end DirichletCharacter

end
