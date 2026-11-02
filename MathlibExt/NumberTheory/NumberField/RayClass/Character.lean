/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.NumberField.RayClass.Group
import Mathlib.Analysis.Complex.Circle

/-!
# Ray class characters (N427 Definition 22.10)

A ray class character of a modulus `m` is a homomorphism from the
ray class group to the unit circle. We provide the trivial character,
the pullback to coprime fractional ideals, complex-valued evaluation,
and the extension by zero to all fractional ideals.
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors

namespace NumberField
namespace Modulus

variable {K : Type*} [Field K] [NumberField K]

variable {m : Modulus K}

/-- **Ray class character.** A ray class character of a modulus $m$ of a number field $K$ is a
group homomorphism from the ray class group of $m$ to the unit circle
$\{z \in \mathbb C : |z| = 1\}$. -/
abbrev RayClassCharacter (m : Modulus K) := RayClassGroup m →* Circle

/-- **Trivial character.** The trivial ray class character of a modulus $m$ of a number field $K$
is the ray class character sending every ray class of $m$ to $1$. -/
def trivialCharacter (m : Modulus K) : RayClassCharacter m := 1

@[simp]
theorem trivialCharacter_apply (m : Modulus K) (x : RayClassGroup m) :
    trivialCharacter m x = 1 :=
  rfl

@[simp]
theorem RayClassCharacter_apply_one (chi : RayClassCharacter m) :
    chi 1 = 1 :=
  map_one chi

@[simp]
theorem RayClassCharacter_apply_mul (chi : RayClassCharacter m)
    (a b : RayClassGroup m) :
    chi (a * b) = chi a * chi b :=
  map_mul chi a b

/-- **Pullback of a ray class character to ideals.** For a ray class character $\chi$ of a
modulus $m$ of a number field $K$, its pullback is the group homomorphism from the group of
nonzero fractional ideals of $K$ coprime to the finite part of $m$ to the unit circle sending
$\mathfrak a$ to $\chi([\mathfrak a])$, where $[\mathfrak a]$ is the ray class of $\mathfrak a$. -/
def pullback (chi : RayClassCharacter m) :
    coprimeFractionalIdeals m →* Circle :=
  chi.comp (rayClassMap m)

@[simp]
theorem pullback_apply (chi : RayClassCharacter m)
    (x : coprimeFractionalIdeals m) :
    pullback chi x = chi (rayClassMap m x) :=
  rfl

@[simp]
theorem pullback_one (chi : RayClassCharacter m) :
    pullback chi 1 = 1 :=
  map_one _

@[simp]
theorem pullback_mul (chi : RayClassCharacter m)
    (a b : coprimeFractionalIdeals m) :
    pullback chi (a * b) = pullback chi a * pullback chi b :=
  map_mul _ _ _

/-- **Pulled-back ray class characters are trivial on the ray group.** Let $\chi$ be a ray class
character of a modulus $m$ of a number field $K$. If a nonzero fractional ideal $\mathfrak a$ of
$K$ coprime to the finite part of $m$ lies in the ray group of $m$, then the pullback of $\chi$ to
the fractional ideals coprime to the finite part of $m$ takes the value $1$ at $\mathfrak a$. -/
theorem pullback_eq_one_of_mem_rayGroup (chi : RayClassCharacter m)
    (x : coprimeFractionalIdeals m) (h : x ∈ rayGroup m) :
    pullback chi x = 1 := by
  rw [pullback_apply, (rayClassMap_eq_one_iff m x).mpr h, map_one]

/-- **Complex value of a ray class character.** For a ray class character $\chi$ of a modulus $m$
and a ray class $x$ of $m$, the complex value of $\chi$ at $x$ is $\chi(x)$, a point of the unit
circle, regarded as a complex number. -/
def evalComplex (chi : RayClassCharacter m) (x : RayClassGroup m) : ℂ :=
  Circle.coeHom (chi x)

@[simp]
theorem evalComplex_one (chi : RayClassCharacter m) :
    evalComplex chi 1 = 1 := by
  simp only [evalComplex, map_one]

@[simp]
theorem evalComplex_mul (chi : RayClassCharacter m)
    (a b : RayClassGroup m) :
    evalComplex chi (a * b) = evalComplex chi a * evalComplex chi b := by
  simp only [evalComplex, map_mul]

/-- **Ray class characters take the complex value $1$ on the ray group.** Let $m$ be a modulus
of a number field $K$ and $\chi$ a ray class character of $m$. If a nonzero fractional ideal
$\mathfrak a$ of $K$ coprime to the finite part of $m$ lies in the ray group of $m$, then the value
of $\chi$ at the ray class of $\mathfrak a$, regarded as a complex number, is $1$. -/
theorem evalComplex_rayGroup (chi : RayClassCharacter m)
    (x : coprimeFractionalIdeals m) (h : x ∈ rayGroup m) :
    evalComplex chi (rayClassMap m x) = 1 := by
  rw [(rayClassMap_eq_one_iff m x).mpr h, evalComplex_one]

open Classical in
/-- **Extension by zero of a ray class character.** Let $\chi$ be a ray class character of a
modulus $m$ of a number field $K$. Its extension by zero assigns to a nonzero fractional ideal
$\mathfrak a$ of $K$ the complex number $\chi([\mathfrak a])$ if $\mathfrak a$ is coprime to the
finite part of $m$, where $[\mathfrak a]$ is the ray class of $\mathfrak a$, and the value $0$
otherwise. -/
noncomputable def extendByZero (chi : RayClassCharacter m)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℂ :=
  if h : I ∈ coprimeFractionalIdeals m then
    Circle.coeHom (chi (rayClassMap m ⟨I, h⟩))
  else
    0

open Classical in
@[simp]
theorem extendByZero_of_mem (chi : RayClassCharacter m)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (h : I ∈ coprimeFractionalIdeals m) :
    extendByZero chi I =
      Circle.coeHom (chi (rayClassMap m ⟨I, h⟩)) := by
  simp [extendByZero, h]

open Classical in
@[simp]
theorem extendByZero_of_not_mem (chi : RayClassCharacter m)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (h : I ∉ coprimeFractionalIdeals m) :
    extendByZero chi I = 0 := by
  simp [extendByZero, h]

end Modulus
end NumberField
