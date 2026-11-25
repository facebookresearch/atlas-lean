/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Valuation bridge for ramified DVR extensions

Exact valuation plumbing for the corrected ATLAS N261 Stage A bound.
The eventual different-exponent theorem (`e - 1 ≤ d ≤ e - 1 + v(e)` plus
tame equality) needs `emultiplicity` rather than Nat `multiplicity`,
because the correction term is infinite when `(e : B) = 0`. This file
supplies only that plumbing: the identification of ideal-theoretic
`emultiplicity` at the maximal ideal with `addVal` on a DVR, the
scaling of `addVal` along a torsion-free local DVR extension by the
current unprimed ramification index, and the residue-characteristic
criterion for `n : R` to be a unit. No different-exponent bound is
stated here.
-/

@[expose] public section

namespace IsDiscreteValuationRing

/-- **Multiplicity of the maximal ideal equals the additive valuation.** Let $R$ be a discrete
valuation ring with maximal ideal $\mathfrak{m}$ and normalized additive valuation
$v \colon R \to \mathbb{N} \cup \{\infty\}$. For every $x \in R$, the multiplicity of
$\mathfrak{m}$ in the principal ideal $(x)$, that is, the supremum in $\mathbb{N} \cup \{\infty\}$
of the $n \in \mathbb{N}$ such that $\mathfrak{m}^n$ divides $(x)$ as ideals, equals $v(x)$. -/
theorem emultiplicity_maximalIdeal_span_eq_addVal
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (x : R) :
    emultiplicity (IsLocalRing.maximalIdeal R) (Ideal.span {x}) = addVal R x := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  rw [hϖ.maximalIdeal_eq, Ideal.emultiplicity_span_eq_emultiplicity, addVal,
    multiplicity_addValuation_apply]
  exact emultiplicity_eq_of_associated_left
    (associated_of_irreducible R
      (Classical.choose_spec (exists_prime R)).irreducible hϖ)

end IsDiscreteValuationRing

namespace Ideal.IsDedekindDomain

/-- Multiplicity of `q` in a mapped prime ideal scales by the ramification
index. Port of the old generic prime-case proof to the current unprimed
`ramificationIdx` API. -/
private theorem emultiplicity_map_eq_ramificationIdx_mul_of_prime
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsDedekindDomain A] [IsDedekindDomain B] [FaithfulSMul A B]
    {p I : Ideal A} {q : Ideal B}
    (hp : Irreducible p) (hI : Prime I) (hq : Irreducible q)
    [q.LiesOver p] :
    emultiplicity q (I.map (algebraMap A B)) =
      (q.ramificationIdx A : ℕ∞) * emultiplicity p I := by
  have hI0 : I.map (algebraMap A B) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hI.ne_zero
  by_cases hpI : p = I
  · subst hpI
    simp [(FiniteMultiplicity.of_prime_left hp.prime hp.ne_zero).emultiplicity_self,
      ramificationIdx_eq_normalizedFactors_count p q hI0,
      UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hq hI0]
  · rw [emultiplicity_eq_zero_of_irreducible_ne hp hI.irreducible hpI, mul_zero]
    exact emultiplicity_map_eq_zero_of_ne hp hI hpI

/-- Multiplicity of `w` in a mapped arbitrary ideal scales by the ramification
index. Port of the old generic-ideal induction to the current unprimed
`ramificationIdx` API. Named `..._general` because the unprimed
`emultiplicity_map_eq_ramificationIdx_mul` name is taken by the deprecated
alias of the old primed statement. -/
private theorem emultiplicity_map_eq_ramificationIdx_mul_general
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsDedekindDomain A] [IsDedekindDomain B] [FaithfulSMul A B]
    {v : Ideal A} {w : Ideal B} {I : Ideal A}
    (hI : I ≠ ⊥) (hv : Irreducible v) (hw : Irreducible w)
    [w.LiesOver v] :
    emultiplicity w (I.map (algebraMap A B)) =
      (w.ramificationIdx A : ℕ∞) * emultiplicity v I := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => aesop
  | h₂ J hJ =>
      obtain rfl : J = ⊤ := by simpa using hJ
      simp_rw [Ideal.map_top,
        UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hw
          top_ne_bot,
        UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hv hI,
        ← Ideal.one_eq_top, UniqueFactorizationMonoid.normalizedFactors_one]
      simp
  | h₃ J r hJ hr ih =>
      rw [Ideal.map_mul, emultiplicity_mul hw.prime, emultiplicity_mul hv.prime,
        ih hJ, mul_add,
        emultiplicity_map_eq_ramificationIdx_mul_of_prime hv hr hw]

end Ideal.IsDedekindDomain

/-- **Additive valuations scale by the ramification index.** Let $A$ and $B$ be discrete
valuation rings, and let $B$ be an $A$-algebra that is torsion-free as an $A$-module and whose
structure map $\varphi \colon A \to B$ is a local homomorphism. Let $v_A$ and $v_B$ be the
normalized additive valuations of $A$ and $B$, with values in $\mathbb{N} \cup \{\infty\}$, and
let $e$ be the ramification index of the maximal ideal of $B$ over $A$. Then
$v_B(\varphi(x)) = e \cdot v_A(x)$ for every $x \in A$. -/
theorem IsDiscreteValuationRing.addVal_algebraMap_eq_ramificationIdx_mul
    {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Module.IsTorsionFree A B]
    [IsLocalHom (algebraMap A B)] (x : A) :
    addVal B (algebraMap A B x) =
      ((IsLocalRing.maximalIdeal B).ramificationIdx A : ℕ∞) * addVal A x := by
  have hp_bot : IsLocalRing.maximalIdeal A ≠ ⊥ := IsDiscreteValuationRing.not_a_field A
  have hq_bot : IsLocalRing.maximalIdeal B ≠ ⊥ := IsDiscreteValuationRing.not_a_field B
  have hAprime : (IsLocalRing.maximalIdeal A).IsPrime :=
    (IsLocalRing.maximalIdeal.isMaximal A).isPrime
  have hBprime : (IsLocalRing.maximalIdeal B).IsPrime :=
    (IsLocalRing.maximalIdeal.isMaximal B).isPrime
  have hp_irr : Irreducible (IsLocalRing.maximalIdeal A) :=
    (Ideal.prime_of_isPrime hp_bot hAprime).irreducible
  have hw_irr : Irreducible (IsLocalRing.maximalIdeal B) :=
    (Ideal.prime_of_isPrime hq_bot hBprime).irreducible
  let p := IsLocalRing.maximalIdeal A
  let q := IsLocalRing.maximalIdeal B
  have hp_map : p.map (algebraMap A B) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hp_bot
  have hq_dvd : q ∣ p.map (algebraMap A B) :=
    Ideal.dvd_iff_le.mpr <| Ideal.map_le_iff_le_comap.mpr (q.over_def p).le
  have he : q.ramificationIdx A ≠ 0 := by
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity p q hp_map]
    exact Nat.ne_of_gt
      ((dvd_iff_multiplicity_pos
        (FiniteMultiplicity.of_prime_left hw_irr.prime hp_map)).mpr hq_dvd)
  by_cases hx : x = 0
  · subst hx
    rw [map_zero, IsDiscreteValuationRing.addVal_zero,
      IsDiscreteValuationRing.addVal_zero]
    exact (ENat.mul_top (by exact_mod_cast he)).symm
  · have hspan : Ideal.span {x} ≠ ⊥ :=
      fun h => hx (Ideal.span_singleton_eq_bot.mp h)
    rw [← IsDiscreteValuationRing.emultiplicity_maximalIdeal_span_eq_addVal,
      ← IsDiscreteValuationRing.emultiplicity_maximalIdeal_span_eq_addVal,
      ← Set.image_singleton, ← Ideal.map_span]
    exact Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx_mul_general
      hspan hp_irr hw_irr

/-- **Natural numbers that are units in a local ring.** Let $R$ be a commutative local ring and
let $p$ be the characteristic of its residue field. For every natural number $n$, the image of
$n$ in $R$ is a unit if and only if $p$ does not divide $n$. -/
theorem IsLocalRing.isUnit_natCast_iff_ringChar_not_dvd
    {R : Type*} [CommRing R] [IsLocalRing R] (n : ℕ) :
    IsUnit (n : R) ↔ ¬ ringChar (IsLocalRing.ResidueField R) ∣ n := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast, ne_eq, ringChar.spec]
