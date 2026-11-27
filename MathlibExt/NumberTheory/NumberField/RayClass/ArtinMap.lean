/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.NumberField.RayClass.PrimeGeneration
import MathlibExt.NumberTheory.NumberField.RayClass.FrobeniusGenerators
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Artin map by descent (ATLAS NumberTheoryI:402, Stage B2)

This file is a partial prerequisite for canonical ATLAS item `NumberTheoryI:402`
(Proposition 21.1 of Sutherland, MIT 18.785 Lecture 21), not the full N402 theorem.
Its exact ATLAS source is one slice of
[`v1/Atlas/NumberTheoryI/code/RayClassFields.lean`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
at frozen revision `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`:
lines `489--542`.

## ATLAS source-to-API map

| Source lines | Source name | API in this file |
| --- | --- | --- |
| 489--507 | `artinMap_ker_condition` | `Modulus.freeGroupToCoprime_ker_le_freeGroupToGal_ker` |
| 509--535 | Artin map construction | Artin map API (see below) |
| 537--542 | `artinMap_at_prime_eq_frobenius` | `Modulus.artinMap_primeCoprimeUnit` |

Row 509--535 maps source declarations `artinMapExists` and `ArtinMap` to
`Modulus.artinMap` and `Modulus.artinMap_comp_freeGroupToCoprime`.

The source proves a redundant existential theorem (`artinMapExists`) and then
applies another classical choice (`ArtinMap`). This file collapses that layer:
`Modulus.artinMap` is defined directly with Mathlib's quotient universal
property `MonoidHom.liftOfSurjective`, and the factorization identity
`Modulus.artinMap_comp_freeGroupToCoprime` is the observable contract for the
internal right-inverse choice.

## Repaired public scope

The source works under a custom abelian-extension class and an unconditional
Frobenius choice. Here the Artin map requires `h : m.IsUnramifiedOutside L`,
repairing the ramified-prime choice, and `[IsAbelianGalois K L]`, the native
replacement for the custom class. Abelianity is used to kill the free-group
commutator in the Galois target.

This stage stops before choice independence at arbitrary primes, ray-group
kernel statements, any `IsRayClassField` structure, restriction compatibility,
and Proposition 21.1. Those are separate DAG nodes.
-/

@[expose] public noncomputable section

namespace NumberField

namespace Modulus

variable {K : Type*} [Field K] [NumberField K]
variable {L : Type*} [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
variable (m : Modulus K)

open scoped IsMulCommutative in
/-- **Kernel containment for the free-group Frobenius map.** Let $L/K$ be an abelian Galois
extension of number fields and $\mathfrak m$ a modulus of $K$ with finite part $\mathfrak m_0$,
such that every prime of $\mathcal O_K$ not dividing $\mathfrak m_0$ is unramified in $L$. Let
$F$ be the free group on the primes $\mathfrak p$ of $\mathcal O_K$ not dividing $\mathfrak m_0$.
Then the kernel of the homomorphism from $F$ to the group of fractional ideals of $K$ coprime to
$\mathfrak m_0$ sending each generator $\mathfrak p$ to the ideal $\mathfrak p$ is contained in
the kernel of the homomorphism $F \to \mathrm{Gal}(L/K)$ sending each generator $\mathfrak p$ to
the arithmetic Frobenius at a chosen prime of $\mathcal O_L$ above $\mathfrak p$.

The first kernel lies in the commutator subgroup of $F$, which the second map kills because
$\mathrm{Gal}(L/K)$ is abelian. -/
theorem freeGroupToCoprime_ker_le_freeGroupToGal_ker (h : m.IsUnramifiedOutside L) :
    MonoidHom.ker m.freeGroupToCoprime ≤
      MonoidHom.ker (m.freeGroupToGal (L := L) h) :=
  le_trans m.freeGroupToCoprime_ker_le_commutator
    (Abelianization.commutator_subset_ker _)

/-- **Artin map.** Let $L/K$ be an abelian Galois extension of number fields and $\mathfrak m$
a modulus of $K$ with finite part $\mathfrak m_0$, such that every prime of $\mathcal O_K$ not
dividing $\mathfrak m_0$ is unramified in $L$. Let $I^{\mathfrak m}$ be the group of fractional
ideals of $K$ coprime to $\mathfrak m_0$ and $F$ the free group on the primes $\mathfrak p$ of
$\mathcal O_K$ not dividing $\mathfrak m_0$. The homomorphism $F \to I^{\mathfrak m}$ sending
each generator $\mathfrak p$ to the ideal $\mathfrak p$ is surjective, and its kernel lies in the
kernel of the homomorphism $F \to \mathrm{Gal}(L/K)$ sending each generator $\mathfrak p$ to the
arithmetic Frobenius at a chosen prime of $\mathcal O_L$ above $\mathfrak p$. The Artin map is
the homomorphism $I^{\mathfrak m} \to \mathrm{Gal}(L/K)$ induced by the second map through the
first. -/
noncomputable def artinMap (h : m.IsUnramifiedOutside L) :
    m.coprimeFractionalIdeals →* (L ≃ₐ[K] L) :=
  (m.freeGroupToCoprime.liftOfSurjective m.freeGroupToCoprime_surjective)
    ⟨m.freeGroupToGal (L := L) h,
      m.freeGroupToCoprime_ker_le_freeGroupToGal_ker (L := L) h⟩

/-- **The Artin map factors the free-group Frobenius map.** Let $L/K$ be an abelian Galois
extension of number fields and $\mathfrak m$ a modulus of $K$ with finite part $\mathfrak m_0$,
such that every prime of $\mathcal O_K$ not dividing $\mathfrak m_0$ is unramified in $L$. Let
$F$ be the free group on the primes $\mathfrak p$ of $\mathcal O_K$ not dividing $\mathfrak m_0$,
and let $I^{\mathfrak m}$ be the group of fractional ideals of $K$ coprime to $\mathfrak m_0$.
Then the Artin map $I^{\mathfrak m} \to \mathrm{Gal}(L/K)$ composed with the homomorphism
$F \to I^{\mathfrak m}$ sending each generator $\mathfrak p$ to the ideal $\mathfrak p$ equals the
homomorphism $F \to \mathrm{Gal}(L/K)$ sending each generator $\mathfrak p$ to the arithmetic
Frobenius at a chosen prime of $\mathcal O_L$ above $\mathfrak p$. -/
@[simp]
theorem artinMap_comp_freeGroupToCoprime (h : m.IsUnramifiedOutside L) :
    (m.artinMap (L := L) h).comp m.freeGroupToCoprime =
      m.freeGroupToGal (L := L) h := by
  simp only [artinMap, MonoidHom.liftOfRightInverse_comp]

/-- **The Artin map at a prime.** Let $L/K$ be an abelian Galois extension of number fields and
$\mathfrak m$ a modulus of $K$ with finite part $\mathfrak m_0$, such that every prime of
$\mathcal O_K$ not dividing $\mathfrak m_0$ is unramified in $L$. For every prime $\mathfrak p$
of $\mathcal O_K$ not dividing $\mathfrak m_0$, the Artin map sends $\mathfrak p$, viewed as a
fractional ideal coprime to $\mathfrak m_0$, to the arithmetic Frobenius in $\mathrm{Gal}(L/K)$
at a chosen prime of $\mathcal O_L$ above $\mathfrak p$. -/
@[simp]
theorem artinMap_primeCoprimeUnit (h : m.IsUnramifiedOutside L)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (hvm : ¬ m.finiteSupported v) :
    m.artinMap (L := L) h (m.primeCoprimeUnit v hvm) =
      m.frobeniusAtCoprimePrime (L := L) h ⟨v, hvm⟩ := by
  have hgen : m.primeCoprimeUnit v hvm =
      m.freeGroupToCoprime (FreeGroup.of (⟨v, hvm⟩ : m.CoprimePrimes)) :=
    (m.freeGroupToCoprime_of ⟨v, hvm⟩).symm
  rw [hgen, ← MonoidHom.comp_apply, m.artinMap_comp_freeGroupToCoprime,
    m.freeGroupToGal_of]

end Modulus

end NumberField
