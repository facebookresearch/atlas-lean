/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Polynomial.Tower
public import Mathlib.RingTheory.Valuation.LocalSubring
public import MathlibExt.NumberTheory.HenselFactorization
public import MathlibExt.RingTheory.DiscreteValuationRing.FiniteExtensionComplete

@[expose] public section

/-!
## ATLAS source mapping for N218

ATLAS `Atlas/NumberTheoryI/code/LocalExtensions.lean`, source theorem
`integral_closure_isAdicComplete`, lines 1184--1259, maps to
`IsIntegralClosure.isAdicComplete_of_isAdicComplete` below. This is a supporting
bridge for N218, not the full N218 target.
-/

open scoped Polynomial

variable {A B : Type*} [CommRing A] [CommRing B]
variable [Algebra A B] [Algebra.IsIntegral A B]
variable (p : Ideal A) [p.IsMaximal] [IsAdicComplete p A]
variable (Q : Ideal B) [Q.IsMaximal]

/-- **Maximal ideals contract to the maximal ideal of a complete base.** Let $A$ and $B$ be
commutative rings with $B$ an $A$-algebra that is integral over $A$, and let $\mathfrak p$ be a
maximal ideal of $A$ such that $A$ is $\mathfrak p$-adically complete. Then every maximal ideal
$Q$ of $B$ has preimage $\mathfrak p$ under the structure map $A \to B$. -/
theorem Ideal.comap_eq_base_maximal_of_isAdicComplete_of_isIntegral
    : Q.comap (algebraMap A B) = p := by
  let _ : IsLocalRing A := isLocalRing_of_isAdicComplete_maximal p
  have hQ : (Q.comap (algebraMap A B)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap A B)
      (fun x => Algebra.IsIntegral.isIntegral x) Q
  exact (IsLocalRing.eq_maximalIdeal hQ).trans
    (IsLocalRing.eq_maximalIdeal (inferInstance : p.IsMaximal)).symm

/-- **Domains integral over a complete local domain are local.** Let $A$ be an integral domain
and $\mathfrak p$ a maximal ideal of $A$ such that $A$ is $\mathfrak p$-adically complete. If $B$
is an integral domain and an $A$-algebra that is integral over $A$, then $B$ is a local ring. -/
theorem isLocalRing_of_isIntegral_of_isAdicComplete_maximal
    (p : Ideal A) [p.IsMaximal] [IsAdicComplete p A]
    [IsDomain A] [IsDomain B] : IsLocalRing B := by
  let _ : IsLocalRing A := isLocalRing_of_isAdicComplete_maximal p
  obtain ⟨Q, hQ⟩ := Ideal.exists_maximal B
  refine IsLocalRing.of_unique_max_ideal ⟨Q, hQ, ?_⟩
  intro Q' hQ'
  let _ : Q.IsMaximal := hQ
  let _ : Q'.IsMaximal := hQ'
  by_contra hne
  have hnotle : ¬ Q' ≤ Q := fun hle ↦ hne (hQ'.eq_of_le hQ.ne_top hle)
  obtain ⟨b, hbQ', hbQ⟩ := SetLike.not_le_iff_exists.mp hnotle
  have hcomapQ :=
    Ideal.comap_eq_base_maximal_of_isAdicComplete_of_isIntegral p Q
  have hcomapQ' :=
    Ideal.comap_eq_base_maximal_of_isAdicComplete_of_isIntegral p Q'
  let _ : Q.LiesOver p := ⟨hcomapQ.symm⟩
  let _ : Q'.LiesOver p := ⟨hcomapQ'.symm⟩
  let _ : Field (A ⧸ p) := Ideal.Quotient.field p
  let f : A[X] := minpoly A b
  let fbar : (A ⧸ p)[X] := f.map (Ideal.Quotient.mk p)
  have hbint : IsIntegral A b := Algebra.IsIntegral.isIntegral b
  have hfmonic : f.Monic := minpoly.monic hbint
  have hfirr : Irreducible f := minpoly.irreducible hbint
  have hfbarMonic : fbar.Monic := hfmonic.map (Ideal.Quotient.mk p)
  have hfbar0 : fbar ≠ 0 := hfbarMonic.ne_zero
  have hroot (M : Ideal B) [M.IsPrime] [M.LiesOver p] :
      Polynomial.aeval (Ideal.Quotient.mk M b) fbar = 0 := by
    dsimp only [fbar, f]
    rw [← Ideal.Quotient.algebraMap_eq p,
      Polynomial.aeval_map_algebraMap]
    exact minpoly.aeval_algHom A (Ideal.Quotient.mkₐ A M) b
  have hrootQ' : fbar.IsRoot 0 := by
    have h := hroot Q'
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hbQ'] at h
    change Polynomial.aeval (0 : A ⧸ p) fbar = 0
    apply (Polynomial.aeval_algebraMap_eq_zero_iff_of_injective
      (FaithfulSMul.algebraMap_injective (A ⧸ p) (B ⧸ Q'))).mp
    simpa using h
  let d := fbar.rootMultiplicity 0
  have hd : 0 < d := (Polynomial.rootMultiplicity_pos hfbar0).2 hrootQ'
  obtain ⟨q, hfac, hXndvd⟩ :=
    Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd fbar hfbar0 0
  have hfac' : fbar = Polynomial.X ^ d * q := by
    simpa [d] using hfac
  have hXndvd' : ¬ (Polynomial.X : (A ⧸ p)[X]) ∣ q := by
    simpa using hXndvd
  have hXmonic : (Polynomial.X ^ d : (A ⧸ p)[X]).Monic :=
    Polynomial.monic_X.pow d
  have hqmonic : q.Monic :=
    hXmonic.of_mul_monic_left (hfac' ▸ hfbarMonic)
  have hcop : IsCoprime (Polynomial.X ^ d : (A ⧸ p)[X]) q :=
    (Polynomial.irreducible_X.coprime_pow_of_not_dvd d hXndvd').symm
  have hXnonunit : ¬ IsUnit (Polynomial.X ^ d : (A ⧸ p)[X]) := by
    rw [hXmonic.isUnit_iff]
    intro heq
    have heval := congrArg (Polynomial.eval 0) heq
    simp [hd.ne'] at heval
  have hqnonunit : ¬ IsUnit q := by
    intro hqunit
    have hqeq : q = 1 := hqmonic.isUnit_iff.mp hqunit
    have hrootQ := hroot Q
    have hbbar : Ideal.Quotient.mk Q b ≠ 0 :=
      Ideal.Quotient.eq_zero_iff_mem.not.mpr hbQ
    have hpw : Ideal.Quotient.mk Q b ^ d = 0 := by
      simpa [hfac', hqeq] using hrootQ
    exact (pow_ne_zero d hbbar) hpw
  obtain ⟨g, h, hgmonic, hhmonic, hgh, hgbar, hhbar⟩ :=
    Polynomial.exists_monic_coprime_factorization_of_isAdicComplete
      p f hfmonic (Polynomial.X ^ d) q hXmonic hqmonic hfac' hcop
  rcases hfirr.isUnit_or_isUnit hgh with hgunit | hhunit
  · have hgu : IsUnit (g.map (Ideal.Quotient.mk p)) :=
      hgunit.map (Polynomial.mapRingHom (Ideal.Quotient.mk p))
    rw [hgbar] at hgu
    exact hXnonunit hgu
  · have hhu : IsUnit (h.map (Ideal.Quotient.mk p)) :=
      hhunit.map (Polynomial.mapRingHom (Ideal.Quotient.mk p))
    rw [hhbar] at hhu
    exact hqnonunit hhu

namespace IsIntegralClosure

/-- **The integral closure of a complete DVR is local.** Let $A$ be a discrete valuation ring
that is complete with respect to its maximal ideal, $K$ its fraction field and $L$ a finite
separable extension of $K$. Then the integral closure of $A$ in $L$ is a local ring. -/
theorem isLocalRing_of_isAdicComplete
    (A K L B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [CommRing B] [IsDomain B] [Algebra A B] [Algebra B L]
    [IsScalarTower A B L] [IsIntegralClosure B A L]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] : IsLocalRing B := by
  let _ : Algebra.IsIntegral A B := isIntegral_algebra A L
  exact isLocalRing_of_isIntegral_of_isAdicComplete_maximal
    (IsLocalRing.maximalIdeal A)

/-- **The integral closure of a complete DVR is a DVR.** Let $A$ be a discrete valuation ring
that is complete with respect to its maximal ideal, $K$ its fraction field and $L$ a finite
separable extension of $K$. Then the integral closure of $A$ in $L$ is a discrete valuation
ring. -/
theorem isDiscreteValuationRing_of_isAdicComplete
    (A K L B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [CommRing B] [IsDomain B] [Algebra A B] [Algebra B L]
    [IsScalarTower A B L] [IsIntegralClosure B A L]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] : IsDiscreteValuationRing B := by
  let _ : Algebra.IsIntegral A B := isIntegral_algebra A L
  have hinj : Function.Injective (algebraMap A B) := by
    intro x y hxy
    apply FaithfulSMul.algebraMap_injective A K
    apply FaithfulSMul.algebraMap_injective K L
    calc
      algebraMap K L (algebraMap A K x) = algebraMap A L x :=
        (IsScalarTower.algebraMap_apply A K L x).symm
      _ = algebraMap B L (algebraMap A B x) :=
        IsScalarTower.algebraMap_apply A B L x
      _ = algebraMap B L (algebraMap A B y) := congrArg (algebraMap B L) hxy
      _ = algebraMap A L y := (IsScalarTower.algebraMap_apply A B L y).symm
      _ = algebraMap K L (algebraMap A K y) :=
        IsScalarTower.algebraMap_apply A K L y
  let _ : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  let _ : IsLocalRing B :=
    IsIntegralClosure.isLocalRing_of_isAdicComplete A K L B
  have hDedekind : IsDedekindDomain B := isDedekindDomain A K L B
  have hB : ¬IsField B := fun h ↦ IsDiscreteValuationRing.not_isField A
    ((Algebra.IsIntegral.isField_iff_isField
      (FaithfulSMul.algebraMap_injective A B)).mpr h)
  exact ((IsDiscreteValuationRing.TFAE B hB).out 3 1).mp hDedekind

/-- **The integral closure of a complete DVR is complete.** Let $A$ be a discrete valuation ring
that is complete with respect to its maximal ideal, $K$ its fraction field, $L$ a finite separable
extension of $K$, and $B$ the integral closure of $A$ in $L$. If $B$ is local (as it always is
here), then $B$ is complete with respect to its maximal ideal.

Source: ATLAS `Atlas/NumberTheoryI/code/LocalExtensions.lean`, `integral_closure_isAdicComplete`
(lines 1184--1259), obtained here from the general completeness theorem for finite local
extensions. -/
theorem isAdicComplete_of_isAdicComplete
    {A K L B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [CommRing B] [IsDomain B] [Algebra A B] [Algebra B L]
    [IsScalarTower A B L] [IsIntegralClosure B A L]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [IsLocalRing B] :
    IsAdicComplete (IsLocalRing.maximalIdeal B) B := by
  let _ : IsDiscreteValuationRing B :=
    IsIntegralClosure.isDiscreteValuationRing_of_isAdicComplete A K L B
  let _ : Module.Finite A B := IsIntegralClosure.finite A K L B
  let _ : FaithfulSMul A B :=
    FaithfulSMul.of_field_isFractionRing A B K L
  exact IsDiscreteValuationRing.isAdicComplete_of_finite_local_extension
    (A := A) (B := B)

/-- **Exactly one prime lies over the maximal ideal of a complete DVR.** Let $A$ be a discrete
valuation ring that is complete with respect to its maximal ideal $\mathfrak m$, $K$ its fraction
field, $L$ a finite separable extension of $K$, and $B$ the integral closure of $A$ in $L$. Then
there is exactly one prime ideal of $B$ whose preimage under $A \to B$ is $\mathfrak m$. -/
theorem existsUnique_primesOver_maximalIdeal_of_isAdicComplete
    (A K L B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [CommRing B] [IsDomain B] [Algebra A B] [Algebra B L]
    [IsScalarTower A B L] [IsIntegralClosure B A L]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    ∃! Q : Ideal B, Q ∈ (IsLocalRing.maximalIdeal A).primesOver B := by
  let _ : Algebra.IsIntegral A B := isIntegral_algebra A L
  have hinj : Function.Injective (algebraMap A B) := by
    intro x y hxy
    apply FaithfulSMul.algebraMap_injective A K
    apply FaithfulSMul.algebraMap_injective K L
    calc
      algebraMap K L (algebraMap A K x) = algebraMap A L x :=
        (IsScalarTower.algebraMap_apply A K L x).symm
      _ = algebraMap B L (algebraMap A B x) :=
        IsScalarTower.algebraMap_apply A B L x
      _ = algebraMap B L (algebraMap A B y) := congrArg (algebraMap B L) hxy
      _ = algebraMap A L y := (IsScalarTower.algebraMap_apply A B L y).symm
      _ = algebraMap K L (algebraMap A K y) :=
        IsScalarTower.algebraMap_apply A K L y
  let _ : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  let _ : IsLocalRing B :=
    IsIntegralClosure.isLocalRing_of_isAdicComplete A K L B
  let _ : IsLocalHom (algebraMap A B) := Algebra.IsIntegral.isLocalHom A B
  refine ⟨IsLocalRing.maximalIdeal B, ⟨inferInstance, ⟨?_⟩⟩, ?_⟩
  · exact (IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm
  intro Q hQ
  exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_of_mem_primesOver hQ)

end IsIntegralClosure

/-!
## Complete-DVR valuation rings and ATLAS N265

This section proves the integral-closure input used in ATLAS NumberTheoryI
N265, Theorem 13.5. At atlas-lean commit
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`, the exact specialized source is
[`v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean):

* [`adicCompletionIntegers_isIntegralClosure_aux`, lines 1661--1675](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean#L1661-L1675), asserts
  that the upstairs completion integer ring is the integral closure of the
  downstairs completion integer ring in the upstairs completion field; and
* [`adicCompletionIntegers_module_finite`, lines 1680--1714](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean#L1680-L1714), combines that
  fact with finite-dimensionality and separability of the completed field
  extension to obtain module finiteness.

`Valuation.integer_isIntegralClosure_of_isAdicComplete` isolates and proves
the source's general mechanism. Its `A` is the downstairs complete DVR, `K`
is its fraction field, `L/K` is the finite separable extension, and `v.integer`
is the candidate upstairs valuation ring. The local map
`A → v.integer`, scalar tower through `L`, and completeness of `A` supply the
compatibility and unique-prime input used to compare `v.integer` with
`integralClosure A L`. The conclusion `IsIntegralClosure v.integer A L` is
exactly the source integral-closure clause, generalized away from the concrete
adic-completion names.

`Valuation.module_finite_integer_of_isAdicComplete` then applies
`IsIntegralClosure.finite`, matching the source finiteness conclusion. For
N265, later code instantiates `A`, `K`, `L`, and `v.integer` with the two
finite-place completions and their integer rings and supplies the canonical
local/scalar-tower maps. This section does not construct those completion maps
or prove the final tensor-product equivalence.
-/

namespace Valuation

/-- **Valuation rings dominating a complete DVR are integral closures.** Let $A$ be a discrete
valuation ring that is complete with respect to its maximal ideal, $K$ its fraction field, and
$L$ a finite separable extension of $K$. Let $v$ be a valuation on $L$ with values in a linearly
ordered commutative group with zero, with valuation ring $\mathcal O_v = \{x \in L : v(x) \le 1\}$.
Suppose $\mathcal O_v$ is an $A$-algebra such that the composite $A \to \mathcal O_v \subseteq L$
is the structure map $A \to L$, and $A \to \mathcal O_v$ is a local homomorphism. Then
$\mathcal O_v$ is the integral closure of $A$ in $L$. -/
theorem integer_isIntegralClosure_of_isAdicComplete
    (A K L Gamma : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Algebra A K]
    [IsFractionRing A K] [Field L] [Algebra A L] [Algebra K L]
    [IsScalarTower A K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [LinearOrderedCommGroupWithZero Gamma]
    (v : Valuation L Gamma) [Algebra A ↥v.integer]
    [IsScalarTower A ↥v.integer L]
    [IsLocalHom (algebraMap A ↥v.integer)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    IsIntegralClosure ↥v.integer A L := by
  let _ : IsDiscreteValuationRing ↥(integralClosure A L) :=
    IsIntegralClosure.isDiscreteValuationRing_of_isAdicComplete A K L
    (integralClosure A L)
  let _ : IsFractionRing ↥v.integer L := (Valuation.integer.integers v).isFractionRing
  let _ : IsIntegrallyClosed ↥v.integer := (Valuation.integer.integers v).isIntegrallyClosed
  have hmem : ∀ x : ↥(integralClosure A L),
      algebraMap ↥(integralClosure A L) L x ∈ v.integer := by
    intro x
    have hx : IsIntegral A (x : L) := x.property
    have hx' : IsIntegral ↥v.integer (x : L) := hx.tower_top
    have hle := (Valuation.integer.integers v).mem_of_integral hx'
    simpa [Valuation.mem_integer_iff] using hle
  let f : ↥(integralClosure A L) →+* ↥v.integer :=
    (algebraMap ↥(integralClosure A L) L).codRestrict v.integer hmem
  have hfcomp : (algebraMap ↥v.integer L).comp f =
      algebraMap ↥(integralClosure A L) L := rfl
  have hAO : ∀ x : A, f (algebraMap A ↥(integralClosure A L) x) =
      algebraMap A ↥v.integer x := by
    intro x
    apply Subtype.ext
    change algebraMap (integralClosure A L) L (algebraMap A (integralClosure A L) x) =
      algebraMap v.integer L (algebraMap A v.integer x)
    exact (IsScalarTower.algebraMap_apply A (integralClosure A L) L x).symm.trans
      (IsScalarTower.algebraMap_apply A v.integer L x)
  let F : ↥(integralClosure A L) →ₐ[A] ↥v.integer := { f with commutes' := hAO }
  let _ : Algebra.IsIntegral A ↥(integralClosure A L) :=
    IsIntegralClosure.isIntegral_algebra A L
  have hinjAC : Function.Injective (algebraMap A ↥(integralClosure A L)) := by
    intro x y hxy
    have hL : algebraMap A L x = algebraMap A L y := by
      have h1 := congrArg (algebraMap ↥(integralClosure A L) L) hxy
      exact (IsScalarTower.algebraMap_apply A ↥(integralClosure A L) L x).trans
        (h1.trans (IsScalarTower.algebraMap_apply A ↥(integralClosure A L) L y).symm)
    have hKL : algebraMap K L (algebraMap A K x) =
        algebraMap K L (algebraMap A K y) := by
      exact (IsScalarTower.algebraMap_apply A K L x).symm.trans
        (hL.trans (IsScalarTower.algebraMap_apply A K L y))
    have hK := FaithfulSMul.algebraMap_injective K L hKL
    exact FaithfulSMul.algebraMap_injective A K hK
  let _ : FaithfulSMul A ↥(integralClosure A L) :=
    (faithfulSMul_iff_algebraMap_injective ..).mpr hinjAC
  let _ : IsLocalHom (algebraMap A ↥(integralClosure A L)) :=
    Algebra.IsIntegral.isLocalHom A _
  let Q : Ideal ↥(integralClosure A L) :=
    Ideal.comap f (IsLocalRing.maximalIdeal ↥v.integer)
  have hQcomap : Ideal.comap (algebraMap A ↥(integralClosure A L)) Q =
      IsLocalRing.maximalIdeal A := by
    have hff : f.comp (algebraMap A ↥(integralClosure A L)) =
        algebraMap A ↥v.integer := by
      apply RingHom.ext; intro x
      exact hAO x
    change Ideal.comap (algebraMap A ↥(integralClosure A L))
        (Ideal.comap f (IsLocalRing.maximalIdeal ↥v.integer)) = _
    rw [Ideal.comap_comap, hff]
    exact IsLocalRing.maximalIdeal_comap (algebraMap A ↥v.integer)
  have hQprime : Q.IsPrime := by
    change (Ideal.comap f (IsLocalRing.maximalIdeal ↥v.integer)).IsPrime
    exact (inferInstance : (IsLocalRing.maximalIdeal ↥v.integer).IsPrime).comap f
  obtain ⟨Q₀, hQ₀, huniq⟩ :=
    IsIntegralClosure.existsUnique_primesOver_maximalIdeal_of_isAdicComplete
      A K L (integralClosure A L)
  have hQmem : Q ∈ (IsLocalRing.maximalIdeal A).primesOver
      ↥(integralClosure A L) :=
    ⟨hQprime, ⟨hQcomap.symm⟩⟩
  have hCmem : IsLocalRing.maximalIdeal ↥(integralClosure A L) ∈
      (IsLocalRing.maximalIdeal A).primesOver ↥(integralClosure A L) :=
    ⟨inferInstance,
      ⟨(IsLocalRing.maximalIdeal_comap
        (algebraMap A ↥(integralClosure A L))).symm⟩⟩
  have hQeq : Q = IsLocalRing.maximalIdeal ↥(integralClosure A L) := by
    have h1 : Q = Q₀ := huniq _ hQmem
    have h2 : IsLocalRing.maximalIdeal ↥(integralClosure A L) = Q₀ :=
      huniq _ hCmem
    rw [h1, h2]
  have hf_local : IsLocalHom f :=
    ((IsLocalRing.local_hom_TFAE f).out 5 1).mp hQeq
  let _ : IsLocalHom f := hf_local
  let _ : IsFractionRing ↥(integralClosure A L) L :=
    integralClosure.isFractionRing_of_finite_extension (A := A) K L
  have hbij := bijective_rangeRestrict_comp_of_valuationRing f
    (algebraMap ↥v.integer L) hfcomp
  have hFsurj : Function.Surjective F := by
    show Function.Surjective F
    intro y
    obtain ⟨x, hx⟩ := hbij.2
      ⟨algebraMap ↥v.integer L y, y, rfl⟩
    have heq := congrArg Subtype.val hx
    change algebraMap v.integer L (f x) = algebraMap v.integer L y at heq
    exact ⟨x, (Valuation.integer.integers v).hom_inj heq⟩
  let _ : Algebra.IsIntegral A ↥v.integer :=
    Algebra.IsIntegral.of_surjective F hFsurj
  exact inferInstance

/-- **Valuation rings dominating a complete DVR are finite over it.** Let $A$ be a discrete
valuation ring that is complete with respect to its maximal ideal, $K$ its fraction field, and
$L$ a finite separable extension of $K$. Let $v$ be a valuation on $L$ with values in a linearly
ordered commutative group with zero, with valuation ring $\mathcal O_v = \{x \in L : v(x) \le 1\}$.
Suppose $\mathcal O_v$ is an $A$-algebra such that the composite $A \to \mathcal O_v \subseteq L$
is the structure map $A \to L$, and $A \to \mathcal O_v$ is a local homomorphism. Then
$\mathcal O_v$ is a finitely generated $A$-module. -/
theorem module_finite_integer_of_isAdicComplete
    (A K L Gamma : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Algebra A K]
    [IsFractionRing A K] [Field L] [Algebra A L] [Algebra K L]
    [IsScalarTower A K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [LinearOrderedCommGroupWithZero Gamma]
    (v : Valuation L Gamma) [Algebra A ↥v.integer]
    [IsScalarTower A ↥v.integer L]
    [IsLocalHom (algebraMap A ↥v.integer)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    Module.Finite A ↥v.integer := by
  let _ : IsIntegralClosure ↥v.integer A L :=
    integer_isIntegralClosure_of_isAdicComplete A K L Gamma v
  exact IsIntegralClosure.finite A K L ↥v.integer

end Valuation
