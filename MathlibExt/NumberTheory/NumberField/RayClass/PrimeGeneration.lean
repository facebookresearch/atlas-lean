/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.NumberField.RayClass.PrimeGenerators
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Algebra.FreeAbelianGroup.Finsupp

/-!
# Prime generation for coprime fractional ideals (ATLAS NumberTheoryI:402, Stages A2+B0)

This file is a partial prerequisite for canonical ATLAS item `NumberTheoryI:402`
(Proposition 21.1 of Sutherland, MIT 18.785 Lecture 21), not the full N402 theorem.
Its exact ATLAS source is four slices of
[`v1/Atlas/NumberTheoryI/code/RayClassFields.lean`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean)
at frozen revision `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`:
lines `258--260`, `334--387`, `394--414`, and `429--487`.
The source's `freeGroupToGal` at lines `388--392` is deferred to a later stage.

Scope note: the frozen ATLAS declarations already assume `[NumberField K]`;
both the source and this file cover the number-field case
(`[Field K] [NumberField K]`).

## ATLAS source-to-API map

| Source lines | Source name | API in this file |
| --- | --- | --- |
| 258--260 | `primesCoprime` | `Modulus.coprimePrimeUnits` |
| 334--379 | `fracIdealsCoprime_closure_primes` | `Modulus.closure_coprimePrimeUnits_eq_top` |
| 380--382 | `CoprimePrimes` | `Modulus.CoprimePrimes` |
| 383--387 | `freeGroupToCoprime` | `Modulus.freeGroupToCoprime` |
| 394--405 | `primesCoprime_eq_range` | `Modulus.coprimePrimeUnits_eq_range` |
| 406--414 | `freeGroupToCoprime_surjective` | `Modulus.freeGroupToCoprime_surjective` |
| 416--427 | `fractionalIdeal_mulEquiv_finsupp_primeAsUnit` | Stage A1 API, see below |
| 429--487 | `freeGroupToCoprime_ker_le_commutator` | kernel theorems, see below |

The basis-vector source at lines 416--427 maps to
`FractionalIdeal.factorizationMulEquiv_primeUnitFractionalIdeal`.
The kernel source at lines 429--487 maps to
`Modulus.freeGroupToCoprime_ker_le_commutator` and
`Modulus.freeGroupToCoprime_ker`.

The source's proof-only count lemmas at lines 263--324 are not exported here;
their role is replaced by the native `FractionalIdeal.factorizationMulEquiv` API
via `NumberField.primeUnitFractionalIdeal` and `Modulus.primeCoprimeUnit`
(see `MathlibExt.NumberTheory.NumberField.RayClass.PrimeGenerators`).
The generator computation is recorded as `Modulus.freeGroupToCoprime_of`.
Likewise the prime basis-vector computation at source lines 416--427 is replaced
by `FractionalIdeal.factorizationMulEquiv_primeUnitFractionalIdeal`.

Deferred to later stages: Artin maps, Frobenius choices, and
Proposition 21.1 itself.
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

namespace Modulus

variable (m : Modulus K)

/-- **Primes coprime to a modulus.** Let $\mathfrak m$ be a modulus of a number field $K$. The
primes coprime to $\mathfrak m$ are the nonzero prime ideals $\mathfrak p$ of the ring of
integers $\mathcal O_K$ that do not contain the finite part of $\mathfrak m$, that is, that do
not divide it. They index the generators of a free group that maps to the group of
fractional ideals coprime to the finite part of $\mathfrak m$. -/
abbrev CoprimePrimes :=
  { v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) // ¬ m.finiteSupported v }

/-- **Prime coprime units.** Let $\mathfrak m$ be a modulus of a number field $K$, and let
$I_K^{\mathfrak m}$ be the group of invertible fractional ideals of $K$ coprime to the finite
part of $\mathfrak m$. The prime coprime units of $\mathfrak m$ are the elements of
$I_K^{\mathfrak m}$ of the form $\mathfrak p$, where $\mathfrak p$ is a nonzero prime ideal of
the ring of integers $\mathcal O_K$ that does not divide the finite part of $\mathfrak m$. -/
def coprimePrimeUnits : Set m.coprimeFractionalIdeals :=
  { I | ∃ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hvm : ¬ m.finiteSupported v), I = m.primeCoprimeUnit v hvm }

/-- **Membership in the prime coprime units.** Let $\mathfrak m$ be a modulus of a number field
$K$, and let $I_K^{\mathfrak m}$ be the group of invertible fractional ideals of $K$ coprime to
the finite part of $\mathfrak m$. An element $I$ of $I_K^{\mathfrak m}$ is a prime coprime unit
of $\mathfrak m$ if and only if $I = \mathfrak p$ for some nonzero prime ideal $\mathfrak p$ of
the ring of integers $\mathcal O_K$ that does not divide the finite part of $\mathfrak m$. -/
theorem mem_coprimePrimeUnits (I : m.coprimeFractionalIdeals) :
    I ∈ m.coprimePrimeUnits ↔
      ∃ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
        (hvm : ¬ m.finiteSupported v), I = m.primeCoprimeUnit v hvm :=
  Iff.rfl

/-- **The prime coprime units are the image of the coprime primes.** Let $\mathfrak m$ be a
modulus of a number field $K$, let $I_K^{\mathfrak m}$ be the group of invertible fractional
ideals of $K$ coprime to the finite part of $\mathfrak m$, and let $P$ be the set of nonzero
prime ideals of the ring of integers $\mathcal O_K$ that do not divide the finite part of
$\mathfrak m$. Then the set of prime coprime units of $\mathfrak m$ equals the range of the map
$P \to I_K^{\mathfrak m}$ sending each $\mathfrak p \in P$ to $\mathfrak p$ viewed as an element
of $I_K^{\mathfrak m}$.

Source: direct native counterpart of ATLAS `primesCoprime_eq_range`. -/
theorem coprimePrimeUnits_eq_range :
    m.coprimePrimeUnits =
      Set.range (fun p : m.CoprimePrimes => m.primeCoprimeUnit p.val p.property) := by
  ext I
  constructor
  · intro hI
    obtain ⟨v, hvm, rfl⟩ := (m.mem_coprimePrimeUnits _).mp hI
    exact ⟨⟨v, hvm⟩, rfl⟩
  · rintro ⟨⟨v, hvm⟩, rfl⟩
    exact (m.mem_coprimePrimeUnits _).mpr ⟨v, hvm, rfl⟩

/-- **The coprime primes generate the coprime ideals.** Let $\mathfrak m$ be a modulus of a
number field $K$, and let $I_K^{\mathfrak m}$ be the group of invertible fractional ideals
of $K$ coprime to the finite part of $\mathfrak m$. Then $I_K^{\mathfrak m}$ is generated,
as a group, by the nonzero prime ideals $\mathfrak p$ of the ring of integers
$\mathcal O_K$ that do not divide the finite part of $\mathfrak m$. -/
theorem closure_coprimePrimeUnits_eq_top :
    Subgroup.closure m.coprimePrimeUnits = ⊤ := by
  rw [eq_top_iff]
  intro x _
  set u : (FractionalIdeal (𝓞 K)⁰ K)ˣ := (x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) with hu
  set e : IsDedekindDomain.HeightOneSpectrum (𝓞 K) →₀ ℤ :=
    FractionalIdeal.unitsToFinsupp K u with he
  have hsupp : ∀ v ∈ e.support, ¬ m.finiteSupported v := by
    intro v hv hs
    have hx : FractionalIdeal.count K v (u : FractionalIdeal (𝓞 K)⁰ K) = 0 :=
      ((m.mem_coprimeFractionalIdeals_iff u).mp x.property) v hs
    have hev : FractionalIdeal.unitsToFinsupp K u v = 0 := by
      rw [FractionalIdeal.unitsToFinsupp_apply]
      exact hx
    exact (Finsupp.mem_support_iff.mp hv) hev
  have hrecon : FractionalIdeal.finsuppToUnits K e = u :=
    FractionalIdeal.toUnits_left_inv K u
  have hunits : (x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
      e.support.prod (fun v => primeUnitFractionalIdeal v ^ e v) := by
    apply Units.ext
    show ((x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) = _
    rw [← hu, ← hrecon, FractionalIdeal.finsuppToUnits_val]
    simp only [Finsupp.prod, Units.coe_prod, Units.val_zpow_eq_zpow_val,
      primeUnitFractionalIdeal_val]
  have hsub : x = e.support.attach.prod
      (fun ⟨v, hv⟩ => m.primeCoprimeUnit v (hsupp v hv) ^ e v) := by
    apply Subtype.ext
    change (x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
      m.coprimeFractionalIdeals.subtype (∏ y ∈ e.support.attach,
        m.primeCoprimeUnit y.val (hsupp y.val y.property) ^ e y.val)
    rw [map_prod]
    simp only [Subgroup.coe_subtype, Subgroup.coe_zpow, primeCoprimeUnit_val]
    exact hunits.trans (Finset.prod_attach _ _).symm
  rw [hsub]
  exact Subgroup.prod_mem _ (fun ⟨v, hv⟩ _ =>
    Subgroup.zpow_mem _ (Subgroup.subset_closure
      ((m.mem_coprimePrimeUnits _).mpr ⟨v, hsupp v hv, rfl⟩)) _)

/-- **The free group on the coprime primes maps to the coprime ideals.** Let $\mathfrak m$ be
a modulus of a number field $K$, let $P$ be the set of nonzero prime ideals of the ring of
integers $\mathcal O_K$ that do not divide the finite part of $\mathfrak m$, and let
$I_K^{\mathfrak m}$ be the group of invertible fractional ideals of $K$ coprime to the finite
part of $\mathfrak m$. This is the group homomorphism $F(P) \to I_K^{\mathfrak m}$ from the free
group on $P$ that sends each generator $\mathfrak p$ to $\mathfrak p$, viewed as an element of
$I_K^{\mathfrak m}$. -/
noncomputable def freeGroupToCoprime :
    FreeGroup m.CoprimePrimes →* m.coprimeFractionalIdeals :=
  FreeGroup.lift (fun p => m.primeCoprimeUnit p.val p.property)

/-- **The free-group map on generators.** Let $\mathfrak m$ be a modulus of a number field $K$,
let $P$ be the set of nonzero prime ideals of the ring of integers $\mathcal O_K$ that do not
divide the finite part of $\mathfrak m$, and let $I_K^{\mathfrak m}$ be the group of invertible
fractional ideals of $K$ coprime to the finite part of $\mathfrak m$. For every
$\mathfrak p \in P$, the homomorphism $F(P) \to I_K^{\mathfrak m}$ from the free group on $P$
sends the generator attached to $\mathfrak p$ to $\mathfrak p$, viewed as an element of
$I_K^{\mathfrak m}$. -/
@[simp]
theorem freeGroupToCoprime_of (p : m.CoprimePrimes) :
    m.freeGroupToCoprime (FreeGroup.of p) = m.primeCoprimeUnit p.val p.property := by
  simp only [freeGroupToCoprime, FreeGroup.lift_apply_of]

/-- **The free group on the coprime primes surjects onto the coprime ideals.** Let
$\mathfrak m$ be a modulus of a number field $K$, let $P$ be the set of nonzero prime ideals
of the ring of integers $\mathcal O_K$ that do not divide the finite part of $\mathfrak m$, and
let $I_K^{\mathfrak m}$ be the group of invertible fractional ideals of $K$ coprime to the
finite part of $\mathfrak m$. The homomorphism $F(P) \to I_K^{\mathfrak m}$ from the free group
on $P$ sending each generator $\mathfrak p$ to $\mathfrak p$ is surjective. -/
theorem freeGroupToCoprime_surjective :
    Function.Surjective m.freeGroupToCoprime := by
  unfold freeGroupToCoprime
  rw [FreeGroup.lift_surjective_iff_closure_range_eq_top,
    ← m.coprimePrimeUnits_eq_range, m.closure_coprimePrimeUnits_eq_top]

/-- **The kernel of the free-group map lies in the commutator subgroup.** Let $\mathfrak m$ be
a modulus of a number field $K$, let $P$ be the set of nonzero prime ideals of the ring of
integers $\mathcal O_K$ that do not divide the finite part of $\mathfrak m$, and let
$I_K^{\mathfrak m}$ be the group of invertible fractional ideals of $K$ coprime to the finite
part of $\mathfrak m$. The kernel of the homomorphism $F(P) \to I_K^{\mathfrak m}$ from the free
group on $P$ sending each generator $\mathfrak p$ to $\mathfrak p$ is contained in the
commutator subgroup $[F(P), F(P)]$.

Source: direct native counterpart of ATLAS `freeGroupToCoprime_ker_le_commutator` (source
lines 429--487). The prime basis-vector computation at source lines 416--427 is replaced by
`FractionalIdeal.factorizationMulEquiv_primeUnitFractionalIdeal`. The proof builds the ATLAS
retraction to the abelianization through `FractionalIdeal.factorizationMulEquiv`,
`Finsupp.comapDomain.addMonoidHom`, `Finsupp.toFreeAbelianGroup`, and `Abelianization.of`;
the retraction itself stays private to this proof. -/
theorem freeGroupToCoprime_ker_le_commutator :
    MonoidHom.ker m.freeGroupToCoprime ≤
      commutator (FreeGroup m.CoprimePrimes) := by
  set φ : (IsDedekindDomain.HeightOneSpectrum (𝓞 K) →₀ ℤ) →+
      Additive (Abelianization (FreeGroup m.CoprimePrimes)) :=
    (FreeAbelianGroup.lift (fun a : m.CoprimePrimes =>
      Additive.ofMul (Abelianization.of (FreeGroup.of a)))).comp
      (Finsupp.toFreeAbelianGroup.comp (Finsupp.comapDomain.addMonoidHom
        (Subtype.val_injective :
          Function.Injective (Subtype.val : m.CoprimePrimes →
            IsDedekindDomain.HeightOneSpectrum (𝓞 K))))) with hφ
  let r : m.coprimeFractionalIdeals →* Abelianization (FreeGroup m.CoprimePrimes) :=
    { toFun := fun I => Additive.toMul (φ (Multiplicative.toAdd
        (FractionalIdeal.factorizationMulEquiv K
          (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ))))
      map_one' := by
        simp only [show ((1 : m.coprimeFractionalIdeals) :
            (FractionalIdeal (𝓞 K)⁰ K)ˣ) = 1 from rfl,
          map_one, toAdd_one, map_zero, toMul_zero]
      map_mul' := fun a b => by
        simp only [show ((a * b : m.coprimeFractionalIdeals) :
            (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
            (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) * (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
          from rfl,
          map_mul, toAdd_mul, map_add, toMul_add] }
  have hretract : r.comp m.freeGroupToCoprime = Abelianization.of := by
    apply FreeGroup.ext_hom
    intro p
    simp only [MonoidHom.comp_apply, m.freeGroupToCoprime_of]
    change Additive.toMul (φ (Multiplicative.toAdd (FractionalIdeal.factorizationMulEquiv K
      ((m.primeCoprimeUnit p.val p.property) : (FractionalIdeal (𝓞 K)⁰ K)ˣ)))) = _
    rw [m.primeCoprimeUnit_val,
      FractionalIdeal.factorizationMulEquiv_primeUnitFractionalIdeal, hφ]
    simp only [AddMonoidHom.comp_apply, Finsupp.comapDomain.addMonoidHom_apply,
      Finsupp.comapDomain_single, Finsupp.toFreeAbelianGroup_single, one_smul,
      FreeAbelianGroup.lift_apply_of, toMul_ofMul]
  intro x hx
  rw [← Abelianization.ker_of, MonoidHom.mem_ker]
  rw [MonoidHom.mem_ker] at hx
  have hx2 : (r.comp m.freeGroupToCoprime) x = Abelianization.of x := by rw [hretract]
  simp only [MonoidHom.comp_apply] at hx2
  rw [hx, map_one] at hx2
  exact hx2.symm

/-- **The kernel of the free-group map is the commutator subgroup.** Let $\mathfrak m$ be a
modulus of a number field $K$, let $P$ be the set of nonzero prime ideals of the ring of
integers $\mathcal O_K$ that do not divide the finite part of $\mathfrak m$, and let
$I_K^{\mathfrak m}$ be the group of invertible fractional ideals of $K$ coprime to the finite
part of $\mathfrak m$. The kernel of the homomorphism $F(P) \to I_K^{\mathfrak m}$ from the free
group on $P$ sending each generator $\mathfrak p$ to $\mathfrak p$ equals the commutator
subgroup $[F(P), F(P)]$.

The commutator subgroup lies in the kernel because $I_K^{\mathfrak m}$ is abelian. -/
@[simp]
theorem freeGroupToCoprime_ker :
    MonoidHom.ker m.freeGroupToCoprime =
      commutator (FreeGroup m.CoprimePrimes) :=
  le_antisymm m.freeGroupToCoprime_ker_le_commutator
    (Abelianization.commutator_subset_ker m.freeGroupToCoprime)

end Modulus

end NumberField
