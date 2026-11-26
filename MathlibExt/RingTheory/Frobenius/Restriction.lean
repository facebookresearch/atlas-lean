/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Frobenius

/-!
ATLAS N402 source-to-API map: source declaration
[`v1/Atlas/NumberTheoryI/code/RayClassFields.lean`, lines 557--588](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L557-L588), maps to
`restrictNormalHom_isArithFrobAt` below. This is only Stage C1, restriction of an arithmetic
Frobenius to an intermediate Galois field, not the full N402 Artin theorem.

Stage C1b: source declaration
[`v1/Atlas/NumberTheoryI/code/RayClassFields.lean`, lines 678--712](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L678-L712)
(`prop_7_13_restrictNormalHom_arithFrobAt`), maps to `restrictNormalHom_eq_of_isArithFrobAt`
below: the restricted Frobenius equals the Frobenius at the contracted prime when the latter
is unramified. The native statement takes explicit primes `Q_L`, `Q_M` with
`[Q_M.LiesOver Q_L]`, replacing source lines 589--676 of chosen-prime plumbing (nonzeroness,
primality, residue finiteness, contraction identity); fraction-field extensionality replaces
that source plumbing to lift the `AlgHom` equality, so no local or global `FaithfulSMul`
instance is needed.
-/

@[expose] public section

variable {K L M : Type*} [Field K] [Field L] [Field M]
  [NumberField K] [NumberField L] [NumberField M]
  [Algebra K L] [Algebra K M] [Algebra L M]
  [IsScalarTower K L M]
  [IsGalois K L] [IsGalois K M]

theorem restrictNormalHom_isArithFrobAt
    (Q_M : Ideal (NumberField.RingOfIntegers M)) [Q_M.IsPrime]
    [Finite (NumberField.RingOfIntegers M ⧸ Q_M)]
    (σ : M ≃ₐ[K] M)
    (hσ : IsArithFrobAt (NumberField.RingOfIntegers K) σ Q_M) :
    IsArithFrobAt (NumberField.RingOfIntegers K) (AlgEquiv.restrictNormalHom L σ)
      (Ideal.comap (algebraMap (NumberField.RingOfIntegers L)
        (NumberField.RingOfIntegers M)) Q_M) := by
  intro y
  rw [Ideal.mem_comap, map_sub, map_pow]
  have hunder : (Q_M.comap (algebraMap (NumberField.RingOfIntegers L)
      (NumberField.RingOfIntegers M))).under (NumberField.RingOfIntegers K)
      = Q_M.under (NumberField.RingOfIntegers K) := by
    simp only [Ideal.under_def, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
  rw [hunder]
  have compat : (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M))
      ((MulSemiringAction.toAlgHom (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers L) (AlgEquiv.restrictNormalHom L σ)) y) =
      (MulSemiringAction.toAlgHom (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers M) σ)
        (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M) y) := by
    ext
    exact AlgEquiv.restrictNormal_commutes σ L ↑y
  rw [compat]
  exact hσ (algebraMap (NumberField.RingOfIntegers L)
    (NumberField.RingOfIntegers M) y)

/-- **Restricting a Frobenius element to an intermediate field.** Let $K \subseteq L \subseteq M$
be a tower of number fields with $L/K$ and $M/K$ Galois, and let $\mathcal{O}_K$,
$\mathcal{O}_L$ and $\mathcal{O}_M$ be their rings of integers. Let $Q_L$ be a prime of
$\mathcal{O}_L$ at which $\mathcal{O}_L$ is unramified over $\mathcal{O}_K$, let $Q_M$ be a
prime of $\mathcal{O}_M$ lying over $Q_L$ with $\mathcal{O}_M/Q_M$ finite, and let $q$ be the
number of elements of $\mathcal{O}_K/\mathfrak{p}$, where $\mathfrak{p}$ is the prime of
$\mathcal{O}_K$ below $Q_M$ (equivalently, below $Q_L$). If $\sigma_M \in \mathrm{Gal}(M/K)$
satisfies $\sigma_M(x) \equiv x^q \pmod{Q_M}$ for all $x \in \mathcal{O}_M$ and
$\sigma_L \in \mathrm{Gal}(L/K)$ satisfies $\sigma_L(y) \equiv y^q \pmod{Q_L}$ for all
$y \in \mathcal{O}_L$, then the restriction of $\sigma_M$ to $L$ equals $\sigma_L$.

Source: ATLAS Proposition 7.13, generalized from the chosen Frobenius elements at chosen primes
to arbitrary Frobenius elements at explicit primes. -/
theorem restrictNormalHom_eq_of_isArithFrobAt
    (Q_L : Ideal (NumberField.RingOfIntegers L)) [Q_L.IsPrime]
    (Q_M : Ideal (NumberField.RingOfIntegers M)) [Q_M.IsPrime] [Q_M.LiesOver Q_L]
    [Finite (NumberField.RingOfIntegers M ⧸ Q_M)]
    [Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) Q_L]
    (σ_M : M ≃ₐ[K] M) (σ_L : L ≃ₐ[K] L)
    (hM : IsArithFrobAt (NumberField.RingOfIntegers K) σ_M Q_M)
    (hL : IsArithFrobAt (NumberField.RingOfIntegers K) σ_L Q_L) :
    AlgEquiv.restrictNormalHom L σ_M = σ_L := by
  have hcomap : Q_M.comap (algebraMap (NumberField.RingOfIntegers L)
      (NumberField.RingOfIntegers M)) = Q_L := by
    have h : Q_L = Q_M.under (NumberField.RingOfIntegers L) :=
      Ideal.LiesOver.over
    rw [Ideal.under_def] at h
    exact h.symm
  have hRestrict : IsArithFrobAt (NumberField.RingOfIntegers K)
      (AlgEquiv.restrictNormalHom L σ_M) Q_L := by
    rw [← hcomap]
    exact restrictNormalHom_isArithFrobAt Q_M σ_M hM
  have hQ : Q_L.primeCompl ≤ nonZeroDivisors (NumberField.RingOfIntegers L) :=
    Ideal.primeCompl_le_nonZeroDivisors Q_L
  have hAlg : (MulSemiringAction.toAlgHom (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) (AlgEquiv.restrictNormalHom L σ_M)) =
      (MulSemiringAction.toAlgHom (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers L) σ_L) :=
    hRestrict.eq_of_isUnramifiedAt hL hQ
  apply AlgEquiv.coe_toAlgHom_injective
  apply AlgHom.coe_ringHom_injective
  apply IsFractionRing.ringHom_ext (A := NumberField.RingOfIntegers L)
  intro x
  have key : ∀ y : NumberField.RingOfIntegers L,
      ((AlgEquiv.restrictNormalHom L) σ_M) (y : L) = σ_L (y : L) :=
    fun y => congrArg Subtype.val (AlgHom.congr_fun hAlg y)
  simpa only [AlgHom.coe_toRingHom, AlgEquiv.toAlgHom_apply,
    ← NumberField.RingOfIntegers.coe_eq_algebraMap] using key x
