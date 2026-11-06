/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.NumberField.RayClass.PrimeGeneration
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Unramified Frobenius generators (ATLAS NumberTheoryI:402, Stage B1)

This file is a partial prerequisite for canonical ATLAS item `NumberTheoryI:402`
(Proposition 21.1 of Sutherland, MIT 18.785 Lecture 21), not the full N402 theorem.
Its exact ATLAS source is two slices of
[`v1/Atlas/NumberTheoryI/code/RayClassFields.lean`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
at frozen revision `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`:
lines `171--208` (the chosen prime above a base prime and its arithmetic
Frobenius) and lines `388--392` (the free-group lift to the Galois group).
The later slices at lines `548--553` and `781--785` are not ported here; they
are cited only as scope justification for the repaired unramified-domain
contract below.

## ATLAS source-to-API map

| Source lines | Source name | API in this file |
| --- | --- | --- |
| 171--204 | `choosePrimeOver` and instances | private `Modulus.chosenPrime` |
| 205--208 | `FrobeniusAutomorphism` | `Modulus.frobeniusAtCoprimePrime` |
| 388--392 | `freeGroupToGal` | `Modulus.freeGroupToGal` |
| 548--553, 781--785 | unramified-outside-modulus use sites | scope justification only, not ported |

## Repaired public scope

ATLAS exposes an unconditional chosen `FrobeniusAutomorphism` at every finite
prime. That is not an honest canonical Artin symbol at a ramified prime:
Mathlib's `arithFrobAt` there chooses an arbitrary lift modulo inertia. This
PR therefore deliberately strengthens/repairs the public contract for the
mathematically intended unramified domain. The later ATLAS evidence slices at
lines `548--553` and `781--785` (where the relevant extension is assumed
unramified outside the modulus) justify this scoping but contribute no B1
declarations ported verbatim. This file implements the repaired contract:

* `Modulus.IsUnramifiedOutside` makes the unramifiedness hypothesis explicit,
  using Mathlib's `Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal` for every
  height-one prime `v` outside the finite support of the modulus;
* `Modulus.frobeniusAtCoprimePrime` takes the unramifiedness witness, and its
  public specification `Modulus.frobeniusAtCoprimePrime_spec` exhibits a prime
  above `p` with finite residue field and `Algebra.IsUnramifiedAt` (proved from
  the witness), at which the chosen value satisfies `IsArithFrobAt`;
* the actual prime-over choice (`Ideal.primesOver`), its projections, and the
  finite-quotient plumbing stay private. The Galois-group finiteness, the
  ring-of-integers Galois action, and its fixed-ring fact are all synthesized
  from current Mathlib under the `IsGalois K L` hypothesis.

This stage stops before choice-independence, kernel comparison, quotient
descent, Artin maps, restriction compatibility, the ray-class-field structure,
and Proposition 21.1. Those are separate DAG nodes.
-/

@[expose] public noncomputable section

namespace NumberField
namespace Modulus

variable {K : Type*} [Field K] [NumberField K]
variable (m : Modulus K)

/-- **Extensions unramified outside a modulus.** Let $m$ be a modulus of a number field $K$.
An extension of number fields $L / K$ is unramified outside $m$ when every finite prime
$\mathfrak p$ of $K$ not dividing the finite part of $m$ is unramified in $\mathcal O_L$,
that is, every prime of $\mathcal O_L$ lying over $\mathfrak p$ is unramified over
$\mathcal O_K$. -/
def IsUnramifiedOutside (L : Type*) [Field L] [NumberField L] [Algebra K L] :
    Prop :=
  ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), ¬ m.finiteSupported v →
    Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal

/-- **Unramified outside a modulus implies unramified at coprime primes.** Let $m$ be a
modulus of a number field $K$ and let $L / K$ be an extension of number fields that is
unramified outside $m$. Then every finite prime $\mathfrak p$ of $K$ not dividing the finite
part of $m$ is unramified in $\mathcal O_L$. -/
theorem IsUnramifiedOutside.at_coprimePrime {L : Type*} [Field L] [NumberField L]
    [Algebra K L] (h : m.IsUnramifiedOutside L) (p : m.CoprimePrimes) :
    Algebra.IsUnramifiedIn (𝓞 L) p.val.asIdeal :=
  h p.val p.property

section Chosen

variable {L : Type*} [Field L] [NumberField L] [Algebra K L]

/-- Private chosen prime of `𝓞 L` above `p`, travelling as `Ideal.primesOver`
so that primality and lying-over evidence stay attached via Mathlib's
`Ideal.primesOver.isPrime` / `Ideal.primesOver.liesOver` instances. -/
private noncomputable def chosenPrime (p : m.CoprimePrimes) :
    Ideal.primesOver p.val.asIdeal (𝓞 L) :=
  Classical.choice (Ideal.nonempty_primesOver p.val.asIdeal)

/-- The chosen prime has finite residue field. Private plumbing shared by the
Frobenius definition and its specification. -/
private theorem chosenFinite (p : m.CoprimePrimes) :
    Finite (𝓞 L ⧸ (m.chosenPrime (L := L) p).1) :=
  Ring.HasFiniteQuotients.finiteQuotient
    (Ideal.ne_bot_of_mem_primesOver p.val.ne_bot
      (m.chosenPrime (L := L) p).property)

end Chosen

section Frobenius

variable {L : Type*} [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

/-- **Chosen Frobenius element at a coprime prime.** Let $m$ be a modulus of a number field
$K$, let $L / K$ be a Galois extension of number fields that is unramified outside $m$, and
let $\mathfrak p$ be a finite prime of $K$ not dividing the finite part of $m$. Fix a prime
$\mathfrak P$ of $\mathcal O_L$ lying over $\mathfrak p$. The chosen Frobenius element at
$\mathfrak p$ is a fixed element $\sigma \in \mathrm{Gal}(L/K)$ that is an arithmetic
Frobenius at $\mathfrak P$, that is, $\sigma(x) \equiv x^q \pmod{\mathfrak P}$ for all
$x \in \mathcal O_L$, where $q$ is the number of elements of $\mathcal O_K / \mathfrak p$.

The value may depend on the choice of $\mathfrak P$. -/
noncomputable def frobeniusAtCoprimePrime (_h : m.IsUnramifiedOutside L)
    (p : m.CoprimePrimes) : (L ≃ₐ[K] L) :=
  haveI := (m.chosenPrime (L := L) p).property.1
  haveI := m.chosenFinite (L := L) p
  arithFrobAt (𝓞 K) (L ≃ₐ[K] L) (m.chosenPrime (L := L) p).1

/-- **The chosen Frobenius is an arithmetic Frobenius at an unramified prime.** Let $m$ be
a modulus of a number field $K$, let $L / K$ be a Galois extension of number fields that is
unramified outside $m$, and let $\mathfrak p$ be a finite prime of $K$ not dividing the
finite part of $m$, with chosen Frobenius element $\sigma \in \mathrm{Gal}(L/K)$. Then there
is a prime $\mathfrak P$ of $\mathcal O_L$ lying over $\mathfrak p$ such that
$\mathcal O_L / \mathfrak P$ is finite, $\mathfrak P$ is unramified over $\mathcal O_K$, and
$\sigma(x) \equiv x^q \pmod{\mathfrak P}$ for all $x \in \mathcal O_L$, where $q$ is the
number of elements of $\mathcal O_K / \mathfrak p$. -/
theorem frobeniusAtCoprimePrime_spec (h : m.IsUnramifiedOutside L)
    (p : m.CoprimePrimes) :
    ∃ Q : Ideal.primesOver p.val.asIdeal (𝓞 L),
      Finite (𝓞 L ⧸ Q.1) ∧ Q.1.LiesOver p.val.asIdeal ∧
        Algebra.IsUnramifiedAt (𝓞 K) Q.1 ∧
        IsArithFrobAt (𝓞 K) (m.frobeniusAtCoprimePrime (L := L) h p) Q.1 := by
  let Q := m.chosenPrime (L := L) p
  let := m.chosenFinite (L := L) p
  refine ⟨Q, m.chosenFinite (L := L) p, Q.property.2,
    (h p.val p.property) Q.1 Q.property.1 Q.property.2, ?_⟩
  unfold frobeniusAtCoprimePrime
  exact IsArithFrobAt.arithFrobAt _ _ _

/-- **Frobenius homomorphism on the free group of coprime primes.** Let $m$ be a modulus
of a number field $K$ and let $L / K$ be a Galois extension of number fields that is
unramified outside $m$. The Frobenius homomorphism is the group homomorphism from the free
group on the finite primes of $K$ not dividing the finite part of $m$ to $\mathrm{Gal}(L/K)$
that sends each such prime $\mathfrak p$ to the chosen Frobenius element at $\mathfrak p$. -/
noncomputable def freeGroupToGal (h : m.IsUnramifiedOutside L) :
    FreeGroup m.CoprimePrimes →* (L ≃ₐ[K] L) :=
  FreeGroup.lift (fun p => m.frobeniusAtCoprimePrime (L := L) h p)

/-- **The Frobenius homomorphism on generators.** Let $m$ be a modulus of a number field
$K$ and let $L / K$ be a Galois extension of number fields that is unramified outside $m$.
For every finite prime $\mathfrak p$ of $K$ not dividing the finite part of $m$, the
Frobenius homomorphism from the free group on these primes to $\mathrm{Gal}(L/K)$ sends the
generator $\mathfrak p$ to the chosen Frobenius element at $\mathfrak p$. -/
@[simp]
theorem freeGroupToGal_of (h : m.IsUnramifiedOutside L) (p : m.CoprimePrimes) :
    m.freeGroupToGal (L := L) h (FreeGroup.of p) =
      m.frobeniusAtCoprimePrime (L := L) h p := by
  simp only [freeGroupToGal, FreeGroup.lift_apply_of]

end Frobenius

end Modulus

end NumberField
