/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

@[expose] public section

/-!
# The number of units of a Dedekind domain modulo an ideal

Let `S` be a Dedekind domain that is a finite free `ℤ`-module, such as the ring of integers of a
number field, so that `Ideal.absNorm I` is the number of elements of `S ⧸ I`. We count the units
of `S ⧸ I`:

* `Ideal.natCard_units_quotient_pow`: for a nonzero prime `P` and `k ≠ 0`,
  `#(S ⧸ P ^ k)ˣ = N(P) ^ k - N(P) ^ (k - 1)`;
* `Ideal.natCard_units_quotient_eq_prod`: for `I ≠ ⊥`, `#(S ⧸ I)ˣ` is the product of these
  numbers over the prime factors of `I`;
* `Ideal.natCard_units_quotient`: for `I ≠ ⊥`, `#(S ⧸ I)ˣ = N(I) ∏_{P ∣ I} (1 - 1 / N(P))`.

These are F. Keune, *Number Fields*, Radboud University Press (2023), Chapter 6, Exercise 1(ii)
(p. 141) and 1(iii) (p. 142), stated there for the ring of integers of a number field.
-/

namespace Ideal

open UniqueFactorizationMonoid

variable {S : Type*} [CommRing S] [IsDedekindDomain S] [Module.Free ℤ S] [Module.Finite ℤ S]

omit [Module.Finite ℤ S] in
private theorem natCard_quotient_eq_absNorm (I : Ideal S) : Nat.card (S ⧸ I) = absNorm I := by
  have : Infinite S := Module.Free.infinite ℤ S
  exact (absNorm_eq_natCard I).symm

private theorem finite_quotient_of_ne_bot {I : Ideal S} (hI : I ≠ ⊥) : Finite (S ⧸ I) :=
  finiteQuotientOfFreeOfNeBot I hI

private theorem absNorm_ne_zero_of_ne_bot {I : Ideal S} (hI : I ≠ ⊥) : absNorm I ≠ 0 := by
  have := finite_quotient_of_ne_bot hI
  rw [← natCard_quotient_eq_absNorm]
  exact Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩

/-- **Number of units modulo a power of a prime ideal.** Let $S$ be a Dedekind domain that is a
finite free $\mathbb{Z}$-module (for example the ring of integers $\mathcal{O}_K$ of a number
field $K$), and for an ideal $\mathfrak{b}$ let $N(\mathfrak{b}) = \#(S/\mathfrak{b})$ be its
absolute norm (`Ideal.absNorm`). If $\mathfrak{p}$ is a nonzero prime ideal of $S$ and $k \ge 1$,
then the unit group of $S/\mathfrak{p}^k$ has
$N(\mathfrak{p})^k - N(\mathfrak{p})^{k-1}$ elements (`Nat.card`; the ring $S/\mathfrak{p}^k$ is
finite).

Keune states this for $\mathcal{O}_K$ as $N(\mathfrak{p})^k (1 - 1/N(\mathfrak{p}))$ (F. Keune,
*Number Fields*, 2023, Chapter 6, Exercise 1(ii), p. 141); the two agree as
$N(\mathfrak{p}) \ge 1$. The ring is any Dedekind domain that is a finite free $\mathbb{Z}$-module,
the setting of Mathlib's `Ideal.absNorm`. -/
theorem natCard_units_quotient_pow {P : Ideal S} [hP : P.IsPrime] (hP0 : P ≠ ⊥) {k : ℕ}
    (hk : k ≠ 0) :
    Nat.card (S ⧸ P ^ k)ˣ = absNorm P ^ k - absNorm P ^ (k - 1) := by
  classical
  have : P.IsMaximal := hP.isMaximal hP0
  have hle : P ^ k ≤ P := pow_le_self hk
  have hPk : P ^ k ≠ ⊥ := pow_ne_zero k hP0
  have : Finite (S ⧸ P ^ k) := finite_quotient_of_ne_bot hPk
  let _ : Fintype (S ⧸ P ^ k) := Fintype.ofFinite _
  set f := Ideal.Quotient.factor hle with hf
  have hfs : Function.Surjective f := Ideal.Quotient.factor_surjective hle
  have key : ∀ x : S ⧸ P ^ k, IsUnit x ↔ ¬ f x = 0 := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.isUnit_mk_pow_iff_notMem P hk, hf, Ideal.Quotient.factor_mk,
      Ideal.Quotient.eq_zero_iff_mem]
  have hunits : Nat.card (S ⧸ P ^ k)ˣ = Nat.card {x : S ⧸ P ^ k // ¬ f x = 0} :=
    Nat.card_congr
      { toFun := fun u => ⟨u, (key u).1 u.isUnit⟩
        invFun := fun x => ((key x).2 x.2).unit
        left_inv := fun u => Units.ext rfl
        right_inv := fun x => rfl }
  set φ : (S ⧸ P ^ k) →+ (S ⧸ P) := f.toAddMonoidHom with hφ
  have hker : Nat.card {x : S ⧸ P ^ k // f x = 0} = Nat.card φ.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => (AddMonoidHom.mem_ker (f := φ)).symm)
  have hmul : Nat.card (S ⧸ P ^ k) = Nat.card (S ⧸ P) * Nat.card φ.ker := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective φ hfs).toEquiv]
  rw [natCard_quotient_eq_absNorm, natCard_quotient_eq_absNorm, map_pow] at hmul
  have hN : absNorm P ≠ 0 := absNorm_ne_zero_of_ne_bot hP0
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := Nat.exists_eq_succ_of_ne_zero hk
  have hcard : Nat.card φ.ker = absNorm P ^ j := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hN)
    rw [← hmul, pow_succ, mul_comm]
  rw [hunits, Nat.card_eq_fintype_card, Fintype.card_subtype_compl, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card, hker, hcard, natCard_quotient_eq_absNorm, map_pow,
    Nat.add_sub_cancel]

omit [Module.Finite ℤ S] in
/-- The absolute norm of a nonzero ideal is the product of the norms of the prime powers in its
factorisation, read off from the Chinese remainder theorem. -/
private theorem absNorm_eq_prod_factors {I : Ideal S} (hI : I ≠ ⊥) :
    absNorm I = ∏ P ∈ (factors I).toFinset, absNorm P ^ (factors I).count P := by
  classical
  rw [← natCard_quotient_eq_absNorm,
    Nat.card_congr (IsDedekindDomain.quotientEquivPiFactors hI).toEquiv, Nat.card_pi,
    ← Finset.prod_coe_sort (factors I).toFinset (fun P => absNorm P ^ (factors I).count P)]
  refine Finset.prod_congr rfl fun P _ => ?_
  rw [natCard_quotient_eq_absNorm, map_pow]

open scoped Classical in
/-- **Number of units modulo an ideal, as a product over its prime factors.** Let $S$ be a
Dedekind domain that is a finite free $\mathbb{Z}$-module (for example the ring of integers of a
number field) and let $I \neq 0$ be an ideal of $S$, with factorisation
$I = \prod_{\mathfrak{p}} \mathfrak{p}^{e_{\mathfrak{p}}}$ into prime ideals
(`UniqueFactorizationMonoid.normalizedFactors`, with multiplicities $e_{\mathfrak{p}}$). Then the
unit group of $S/I$ has
$$\prod_{\mathfrak{p} \mid I}
\bigl(N(\mathfrak{p})^{e_{\mathfrak{p}}} - N(\mathfrak{p})^{e_{\mathfrak{p}} - 1}\bigr)$$
elements, where $N$ is the absolute norm (`Ideal.absNorm`).

This is the Chinese remainder theorem reduction to prime powers of F. Keune, *Number Fields*,
2023, pp. 135–136, combined with `Ideal.natCard_units_quotient_pow` (Keune, Chapter 6,
Exercise 1(ii), p. 141). -/
theorem natCard_units_quotient_eq_prod {I : Ideal S} (hI : I ≠ ⊥) :
    Nat.card (S ⧸ I)ˣ = ∏ P ∈ (normalizedFactors I).toFinset,
      (absNorm P ^ (normalizedFactors I).count P -
        absNorm P ^ ((normalizedFactors I).count P - 1)) := by
  rw [← factors_eq_normalizedFactors,
    Nat.card_congr (Units.mapEquiv (IsDedekindDomain.quotientEquivPiFactors hI).toMulEquiv).toEquiv,
    Nat.card_congr MulEquiv.piUnits.toEquiv, Nat.card_pi,
    ← Finset.prod_coe_sort (factors I).toFinset
      (fun P => absNorm P ^ (factors I).count P - absNorm P ^ ((factors I).count P - 1))]
  refine Finset.prod_congr rfl fun P _ => ?_
  have hmem : (P : Ideal S) ∈ factors I := Multiset.mem_toFinset.mp P.2
  have hprime : Prime (P : Ideal S) := prime_of_factor _ hmem
  have : (P : Ideal S).IsPrime := isPrime_of_prime hprime
  exact natCard_units_quotient_pow hprime.ne_zero (Multiset.count_ne_zero.mpr hmem)

open scoped Classical in
/-- **Number of units of the ring of integers modulo an ideal.** Let $S$ be a Dedekind domain
that is a finite free $\mathbb{Z}$-module, for example the ring of integers $\mathcal{O}_K$ of a
number field $K$, and for an ideal $\mathfrak{b}$ let $N(\mathfrak{b}) = \#(S/\mathfrak{b})$ be
its absolute norm (`Ideal.absNorm`). If $\mathfrak{a} \neq 0$ is an ideal of $S$, then the unit
group of the finite ring $S/\mathfrak{a}$ has
$$\#\bigl((S/\mathfrak{a})^\times\bigr) = N(\mathfrak{a}) \prod_{\mathfrak{p} \mid \mathfrak{a}}
\left(1 - \frac{1}{N(\mathfrak{p})}\right)$$
elements, as an identity of rational numbers. The product runs over the finite set
`(normalizedFactors 𝔞).toFinset` of the distinct prime factors of $\mathfrak{a}$, which by
`Ideal.mem_normalizedFactors_iff` are exactly the prime ideals of $S$ containing $\mathfrak{a}$.

This is F. Keune, *Number Fields*, Radboud University Press (2023), Chapter 6, Exercise 1(iii)
(p. 142), stated there for $\mathcal{O}_K$; the ring here is any Dedekind domain that is a finite
free $\mathbb{Z}$-module, the setting of Mathlib's `Ideal.absNorm`. For $S = \mathbb{Z}$ and
$\mathfrak{a} = n\mathbb{Z}$ it is Euler's product formula for $\varphi(n)$. -/
theorem natCard_units_quotient {I : Ideal S} (hI : I ≠ ⊥) :
    (Nat.card (S ⧸ I)ˣ : ℚ) =
      absNorm I * ∏ P ∈ (normalizedFactors I).toFinset, (1 - 1 / (absNorm P : ℚ)) := by
  rw [natCard_units_quotient_eq_prod hI, absNorm_eq_prod_factors hI,
    factors_eq_normalizedFactors, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun P hP => ?_
  have hmem : P ∈ normalizedFactors I := Multiset.mem_toFinset.mp hP
  have hN : absNorm P ≠ 0 :=
    absNorm_ne_zero_of_ne_bot (prime_of_normalized_factor P hmem).ne_zero
  obtain ⟨j, hj⟩ : ∃ j, (normalizedFactors I).count P = j + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Multiset.count_ne_zero.mpr hmem)
  rw [hj, Nat.add_sub_cancel, Nat.cast_sub (Nat.pow_le_pow_right (Nat.pos_of_ne_zero hN)
    (Nat.le_add_right j 1))]
  have hNq : (absNorm P : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  push_cast
  rw [pow_succ]
  field_simp

end Ideal

end
