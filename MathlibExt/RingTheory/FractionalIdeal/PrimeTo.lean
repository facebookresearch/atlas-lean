/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.FractionalIdeal.Extended

/-!
# Fractional ideals prime to an ideal

A fractional ideal is prime to an ideal when it becomes the unit ideal after localization at
every prime containing that ideal. The invertible fractional ideals with this property form a
subgroup.
-/

open scoped nonZeroDivisors

@[expose] public noncomputable section

namespace FractionalIdeal

variable {A : Type*} [CommRing A] [IsDomain A]

omit [IsDomain A] in
/-- **Non-zero-divisors stay non-zero-divisors in a localization at a prime.** Let $A$ be a
commutative ring and $\mathfrak p$ a prime ideal of $A$. Every non-zero-divisor of $A$ maps to a
non-zero-divisor of the localization $A_{\mathfrak p}$. -/
theorem nonZeroDivisors_le_comap_algebraMap_atPrime
    (p : Ideal A) [p.IsPrime] :
    A⁰ ≤ Submonoid.comap (algebraMap A (Localization.AtPrime p))
      (Localization.AtPrime p)⁰ := by
  intro a ha
  rw [Submonoid.mem_comap]
  exact IsLocalization.map_nonZeroDivisors_le p.primeCompl
    (Localization.AtPrime p) ⟨a, ha, rfl⟩

/-- **Fractional ideals prime to an ideal.** Let $A$ be an integral domain with fraction field
$K$, let $I$ be a fractional ideal of $A$ in $K$ and let $J$ be an ideal of $A$. Then $I$ is prime
to $J$ if for every prime ideal $\mathfrak p$ of $A$ with $J \subseteq \mathfrak p$, the extension
$I A_{\mathfrak p}$ of $I$ to the localization $A_{\mathfrak p}$, a fractional ideal of
$A_{\mathfrak p}$ in $K$, is the unit fractional ideal $A_{\mathfrak p}$. -/
def IsPrimeTo (I : FractionalIdeal A⁰ (FractionRing A)) (J : Ideal A) : Prop :=
  ∀ (p : Ideal A) [p.IsPrime], J ≤ p →
    FractionalIdeal.extended (FractionRing A)
      (nonZeroDivisors_le_comap_algebraMap_atPrime p) I = 1

/-- **The unit fractional ideal is prime to every ideal.** Let $A$ be an integral domain with
fraction field $K$. For every ideal $J$ of $A$, the unit fractional ideal $A$ of $A$ in $K$ is
prime to $J$. -/
@[simp]
theorem isPrimeTo_one (J : Ideal A) :
    IsPrimeTo (1 : FractionalIdeal A⁰ (FractionRing A)) J := by
  intro p _ _
  exact FractionalIdeal.extended_one _ _

/-- **Products of fractional ideals prime to an ideal.** Let $A$ be an integral domain with
fraction field $K$ and let $J$ be an ideal of $A$. If fractional ideals $I$ and $I'$ of $A$ in $K$
are both prime to $J$, then their product $I I'$ is prime to $J$. -/
theorem IsPrimeTo.mul {I K : FractionalIdeal A⁰ (FractionRing A)}
    {J : Ideal A} (hI : I.IsPrimeTo J) (hK : K.IsPrimeTo J) :
    (I * K).IsPrimeTo J := by
  intro p _ hp
  rw [FractionalIdeal.extended_mul, hI p hp, hK p hp, one_mul]

/-- **Inverses of invertible fractional ideals prime to an ideal.** Let $A$ be an integral domain
with fraction field $K$ and let $J$ be an ideal of $A$. If an invertible fractional ideal $I$ of
$A$ in $K$ is prime to $J$, then its inverse $I^{-1}$ is prime to $J$. -/
theorem IsPrimeTo.inv_unit
    {u : (FractionalIdeal A⁰ (FractionRing A))ˣ} {J : Ideal A}
    (hu : (u : FractionalIdeal A⁰ (FractionRing A)).IsPrimeTo J) :
    ((u⁻¹ : (FractionalIdeal A⁰ (FractionRing A))ˣ) :
      FractionalIdeal A⁰ (FractionRing A)).IsPrimeTo J := by
  intro p _ hp
  have h1 : FractionalIdeal.extended (FractionRing A)
      (nonZeroDivisors_le_comap_algebraMap_atPrime p)
      (↑(u * u⁻¹) : FractionalIdeal A⁰ (FractionRing A)) = 1 := by
    simp [FractionalIdeal.extended_one]
  rw [Units.val_mul, FractionalIdeal.extended_mul, hu p hp, one_mul] at h1
  exact h1

/-- **Invertible fractional ideals prime to an ideal.** Let $A$ be an integral domain with fraction
field $K$ and let $J$ be an ideal of $A$. The invertible fractional ideals of $A$ in $K$ that are
prime to $J$ form a subgroup of the group of invertible fractional ideals of $A$ in $K$. -/
def unitsPrimeTo (J : Ideal A) :
    Subgroup (FractionalIdeal A⁰ (FractionRing A))ˣ where
  carrier := {u | (u : FractionalIdeal A⁰ (FractionRing A)).IsPrimeTo J}
  one_mem' := isPrimeTo_one J
  mul_mem' := fun ha hb => ha.mul hb
  inv_mem' := fun hu => hu.inv_unit

/-- **Membership in the subgroup of units prime to an ideal.** Let $A$ be an integral domain with
fraction field $K$ and let $J$ be an ideal of $A$. An invertible fractional ideal $I$ of $A$ in
$K$ lies in the subgroup of invertible fractional ideals prime to $J$ if and only if $I$ is prime
to $J$. -/
@[simp]
theorem mem_unitsPrimeTo_iff {J : Ideal A}
    {u : (FractionalIdeal A⁰ (FractionRing A))ˣ} :
    u ∈ unitsPrimeTo J ↔
      (u : FractionalIdeal A⁰ (FractionRing A)).IsPrimeTo J :=
  Iff.rfl

/-- **Prime to an ideal implies prime to every larger ideal.** Let $A$ be an integral domain with
fraction field $K$, let $I$ be a fractional ideal of $A$ in $K$ and let $J \subseteq J'$ be ideals
of $A$. If $I$ is prime to $J$, then $I$ is prime to $J'$. -/
theorem IsPrimeTo.mono {I : FractionalIdeal A⁰ (FractionRing A)}
    {J K : Ideal A} (hI : I.IsPrimeTo J) (hJK : J ≤ K) :
    I.IsPrimeTo K := by
  intro p _ hp
  exact hI p (hJK.trans hp)

/-- **Monotonicity of the subgroups of units prime to an ideal.** Let $A$ be an integral domain
with fraction field $K$ and let $J \subseteq J'$ be ideals of $A$. Then the subgroup of invertible
fractional ideals of $A$ in $K$ prime to $J$ is contained in the subgroup of invertible fractional
ideals of $A$ in $K$ prime to $J'$. -/
theorem unitsPrimeTo_mono {J K : Ideal A} (hJK : J ≤ K) :
    unitsPrimeTo J ≤ unitsPrimeTo K := by
  intro u hu
  exact hu.mono hJK

/-- **Every invertible fractional ideal is prime to the unit ideal.** Let $A$ be an integral domain
with fraction field $K$. The subgroup of invertible fractional ideals of $A$ in $K$ prime to the
unit ideal $A$ is the whole group of invertible fractional ideals of $A$ in $K$. -/
@[simp]
theorem unitsPrimeTo_top : unitsPrimeTo (⊤ : Ideal A) = ⊤ := by
  rw [eq_top_iff]
  intro u _
  rw [mem_unitsPrimeTo_iff]
  intro p hpPrime hp
  exact (hpPrime.ne_top (top_unique hp)).elim

end FractionalIdeal
