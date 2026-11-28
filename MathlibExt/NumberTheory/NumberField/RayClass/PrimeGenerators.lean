/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.NumberField.RayClass.RayGroup
import MathlibExt.RingTheory.DedekindDomain.FactorizationEquiv

/-!
# Prime generators for coprime fractional ideals (ATLAS NumberTheoryI:402, Stage A1)

This file is a partial prerequisite for canonical ATLAS item `NumberTheoryI:402`
(Proposition 21.1 of Sutherland, MIT 18.785 Lecture 21), not the full N402 theorem.
Its exact ATLAS source is
[`v1/Atlas/NumberTheoryI/code/RayClassFields.lean`, lines 210--333](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L210-L333)
at frozen revision `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`.

Scope note: the source states its results for global fields, while this file covers
the number-field-only case (`[Field K] [NumberField K]`).

## ATLAS source-to-API map

| Source lines | Source name | API in this file |
| --- | --- | --- |
| 210--215 | `primeAsUnitFracIdeal` | `NumberField.primeUnitFractionalIdeal` |
| 216--252 | `primeAsUnitFracIdeal_coprime` | `Modulus.mem_coprimeFractionalIdeals_primeUnit` |
| 253--257 | `primeCoprime` | `Modulus.primeCoprimeUnit` |
| 325--328 | `primeCoprime_val` | `Modulus.primeCoprimeUnit_val` |
| 329--333 | `primeAsUnitFracIdeal_val` | `primeUnitFractionalIdeal_val` |

The source's proof-only helper construction at lines 263--324 is replaced by the native
`FractionalIdeal.factorizationMulEquiv` (see
`FractionalIdeal.factorizationMulEquiv_primeUnitFractionalIdeal` below).

Deferred to later stages: `primesCoprime` (source lines 258--262), the
closure/generation theorem (source lines 334--379), the Artin maps, and
Proposition 21.1 itself.
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **A prime as an invertible fractional ideal.** For a number field $K$ with ring of integers
$\mathcal O_K$ and a height-one prime $\mathfrak p$ of $\mathcal O_K$, this is $\mathfrak p$
regarded as a fractional ideal of $K$; it is nonzero, hence a unit in the group of nonzero
fractional ideals of $K$. -/
noncomputable def primeUnitFractionalIdeal
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K)
    (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)

@[simp]
theorem primeUnitFractionalIdeal_val
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    ((primeUnitFractionalIdeal v : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) = (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) :=
  rfl

/-- **Factorization of a prime of a number field.** Let $K$ be a number field with ring of
integers $\mathcal O_K$ and let $\mathfrak p$ be a height-one prime of $\mathcal O_K$. The
factorization isomorphism sends $\mathfrak p$, regarded as an invertible fractional ideal of $K$,
to the function on height-one primes of $\mathcal O_K$ that is $1$ at $\mathfrak p$ and $0$
elsewhere. -/
theorem _root_.FractionalIdeal.factorizationMulEquiv_primeUnitFractionalIdeal
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Multiplicative.toAdd (FractionalIdeal.factorizationMulEquiv K
      (primeUnitFractionalIdeal v)) = Finsupp.single v 1 :=
  FractionalIdeal.factorizationMulEquiv_prime_self K v

namespace Modulus

variable (m : Modulus K) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

/-- **Primes not dividing the modulus are coprime to it.** Let $\mathfrak m$ be a modulus of a
number field $K$ and let $\mathfrak p$ be a height-one prime of the ring of integers
$\mathcal O_K$ that does not contain the finite part of $\mathfrak m$. Then $\mathfrak p$, viewed
as an invertible fractional ideal of $K$, lies in the group of fractional ideals coprime to
$\mathfrak m$: its exponent at every height-one prime containing the finite part of
$\mathfrak m$ is zero. -/
theorem mem_coprimeFractionalIdeals_primeUnit (hvm : ¬ m.finiteSupported v) :
    primeUnitFractionalIdeal v ∈ m.coprimeFractionalIdeals := by
  rw [m.mem_coprimeFractionalIdeals_iff]
  intro w hw
  have hne : w ≠ v := fun h => hvm (h ▸ hw)
  have hfac : Multiplicative.toAdd
      (FractionalIdeal.factorizationMulEquiv K (primeUnitFractionalIdeal v)) =
      Finsupp.single v 1 :=
    FractionalIdeal.factorizationMulEquiv_primeUnitFractionalIdeal v
  have hw0 : Multiplicative.toAdd
      (FractionalIdeal.factorizationMulEquiv K (primeUnitFractionalIdeal v)) w = 0 := by
    rw [hfac]
    exact Finsupp.single_eq_of_ne hne
  rwa [FractionalIdeal.factorizationMulEquiv_apply] at hw0

/-- **The prime as a coprime fractional ideal.** Let $\mathfrak m$ be a modulus of a number
field $K$ and let $\mathfrak p$ be a height-one prime of the ring of integers $\mathcal O_K$ that
does not contain the finite part of $\mathfrak m$. This is $\mathfrak p$, viewed as an invertible
fractional ideal of $K$, regarded as an element of the group of fractional ideals coprime to
$\mathfrak m$. -/
noncomputable def primeCoprimeUnit (hvm : ¬ m.finiteSupported v) :
    m.coprimeFractionalIdeals :=
  ⟨primeUnitFractionalIdeal v, mem_coprimeFractionalIdeals_primeUnit m v hvm⟩

@[simp]
theorem primeCoprimeUnit_val (hvm : ¬ m.finiteSupported v) :
    (m.primeCoprimeUnit v hvm : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
      primeUnitFractionalIdeal v := rfl

end Modulus

end NumberField
