/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean` (Mathlib):
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/

module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.FractionalIdeal.Inverse
public import MathlibExt.NumberTheory.NumberField.OrderIdeals

@[expose] public section

/-!
# Invertible ideals of an order in a number field

For an order `O` of a number field `K` (`NumberField.IsOrder K O`) and its fractional ideals
`FractionalIdeal O⁰ K`, we prove:

* `FractionalIdeal.exists_notMem_one_of_ne_bot_of_dimensionLEOne`: in a Noetherian domain of
  dimension at most one, a nonzero proper ideal `I` has an element of `I⁻¹` outside `1`;
* `NumberField.IsOrder.exists_notMem_mul_mem`: for a nonzero ideal `𝔟 ≠ O` of an order, some
  `x ∈ K` with `x ∉ O` satisfies `x𝔟 ⊆ O`;
* `NumberField.IsOrder.isUnit_coeIdeal_iff_setOf_mul_mem_eq`: a nonzero prime `𝔭` of `O` is
  invertible as a fractional ideal if and only if `{x ∈ K | x𝔭 ⊆ 𝔭} = O`;
* `NumberField.IsOrder.prod_and_isUnit_of_sup_conductor_eq_top`: a nonzero ideal of `O` coprime
  to the conductor is a product of invertible prime ideals, and is invertible.

Sources: K. Conrad, *The conductor ideal of an order*, Lemma 3.2(2) and Theorem 3.4 (p. 5) and
Theorem 3.6 (p. 6); K. Conrad, *Ideal factorization*, Lemma 3.1 and the proof of Theorem 3.2
(pp. 4–5).

The first result is Mathlib's `FractionalIdeal.exists_notMem_one_of_ne_bot` with the hypothesis
`IsDedekindDomain A` replaced by `IsNoetherianRing A` and `Ring.DimensionLEOne A`; its proof,
and that of `PrimeSpectrum.exists_multiset_prod_cons_le_and_prod_not_le` which it uses, are
adapted from Mathlib, where they use only these two properties.
-/

open scoped nonZeroDivisors

section DimensionLEOne

variable {A K : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.DimensionLEOne A]
  [Field K] [Algebra A K] [IsFractionRing A K]

open FractionalIdeal Ideal

/-- Adapted from Mathlib's `PrimeSpectrum.exists_multiset_prod_cons_le_and_prod_not_le`, for a
Noetherian domain of dimension at most one. -/
private theorem exists_multiset_prod_cons_le_and_prod_not_le_of_dimensionLEOne
    (hNF : ¬IsField A) {I M : Ideal A} (hI0 : I ≠ ⊥) (hIM : I ≤ M) [hM : M.IsMaximal] :
    ∃ Z : Multiset (PrimeSpectrum A),
      (M ::ₘ Z.map PrimeSpectrum.asIdeal).prod ≤ I ∧
        ¬Multiset.prod (Z.map PrimeSpectrum.asIdeal) ≤ I := by
  obtain ⟨Z₀, hZ₀⟩ := PrimeSpectrum.exists_primeSpectrum_prod_le_and_ne_bot_of_domain hNF hI0
  obtain ⟨Z, ⟨hZI, hprodZ⟩, h_eraseZ⟩ :=
    wellFounded_lt.has_min
      {Z | (Z.map PrimeSpectrum.asIdeal).prod ≤ I ∧ (Z.map PrimeSpectrum.asIdeal).prod ≠ ⊥}
      ⟨Z₀, hZ₀.1, hZ₀.2⟩
  obtain ⟨_, hPZ', hPM⟩ := hM.isPrime.multiset_prod_le.mp (hZI.trans hIM)
  obtain ⟨P, hPZ, rfl⟩ := Multiset.mem_map.mp hPZ'
  classical
    have := Multiset.map_erase PrimeSpectrum.asIdeal (fun _ _ => PrimeSpectrum.ext) P Z
    obtain ⟨hP0, hZP0⟩ : P.asIdeal ≠ ⊥ ∧ ((Z.erase P).map PrimeSpectrum.asIdeal).prod ≠ ⊥ := by
      rwa [Ne, ← Multiset.cons_erase hPZ', Multiset.prod_cons, Ideal.mul_eq_bot, not_or, ←
        this] at hprodZ
    have hPM' := (P.isPrime.isMaximal hP0).eq_of_le hM.ne_top hPM
    subst hPM'
    refine ⟨Z.erase P, ?_, ?_⟩
    · convert hZI
      rw [this, Multiset.cons_erase hPZ']
    · refine fun h => h_eraseZ (Z.erase P) ⟨h, ?_⟩ (Multiset.erase_lt.mpr hPZ)
      exact hZP0

/-- Adapted from Mathlib's `FractionalIdeal.not_inv_le_one_of_ne_bot`, for a Noetherian domain
of dimension at most one. -/
private theorem not_inv_le_one_of_ne_bot_of_dimensionLEOne {I : Ideal A} (hI0 : I ≠ ⊥)
    (hI1 : I ≠ ⊤) : ¬(I⁻¹ : FractionalIdeal A⁰ K) ≤ 1 := by
  have hNF : ¬IsField A := fun h ↦ letI := h.toField; (eq_bot_or_eq_top I).elim hI0 hI1
  wlog hM : I.IsMaximal generalizing I
  · rcases I.exists_le_maximal hI1 with ⟨M, hmax, hIM⟩
    have hMbot : M ≠ ⊥ := (M.bot_lt_of_maximal hNF).ne'
    refine mt (le_trans <| inv_anti_mono ?_ ?_) (this hMbot hmax.ne_top hmax) <;>
      simpa only [coeIdeal_ne_zero, coeIdeal_le_coeIdeal]
  have hI0 : ⊥ < I := I.bot_lt_of_maximal hNF
  obtain ⟨⟨a, haI⟩, ha0⟩ := Submodule.nonzero_mem_of_bot_lt hI0
  replace ha0 : a ≠ 0 := Subtype.coe_injective.ne ha0
  let J : Ideal A := Ideal.span {a}
  have hJ0 : J ≠ ⊥ := mt Ideal.span_singleton_eq_bot.mp ha0
  have hJI : J ≤ I := I.span_singleton_le_iff_mem.2 haI
  obtain ⟨Z, hle, hnle⟩ :=
    exists_multiset_prod_cons_le_and_prod_not_le_of_dimensionLEOne hNF hJ0 hJI
  obtain ⟨b, hbZ, hbJ⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  have hnz_fa : algebraMap A K a ≠ 0 :=
    mt ((injective_iff_map_eq_zero _).mp (IsFractionRing.injective A K) a) ha0
  refine Set.not_subset.2 ⟨algebraMap A K b * (algebraMap A K a)⁻¹, (mem_inv_iff ?_).mpr ?_, ?_⟩
  · exact coeIdeal_ne_zero.mpr hI0.ne'
  · rintro y₀ hy₀
    obtain ⟨y, h_Iy, rfl⟩ := (mem_coeIdeal _).mp hy₀
    rw [mul_comm, ← mul_assoc, ← map_mul]
    have h_yb : y * b ∈ J := by
      apply hle
      rw [Multiset.prod_cons]
      exact Submodule.smul_mem_smul h_Iy hbZ
    rw [Ideal.mem_span_singleton'] at h_yb
    rcases h_yb with ⟨c, hc⟩
    rw [← hc, map_mul, mul_assoc, mul_inv_cancel₀ hnz_fa, mul_one]
    apply coe_mem_one
  · refine mt (mem_one_iff _).mp ?_
    rintro ⟨x', h₂_abs⟩
    rw [← div_eq_mul_inv, eq_div_iff_mul_eq hnz_fa, ← map_mul] at h₂_abs
    have := Ideal.mem_span_singleton'.mpr ⟨x', IsFractionRing.injective A K h₂_abs⟩
    contradiction

/-- **A proper ideal has a strictly larger inverse.** Let $A$ be a Noetherian integral domain of
dimension at most one (every nonzero prime ideal is maximal) with field of fractions $K$, and let
$I$ be an ideal of $A$ with $I \neq 0$ and $I \neq A$. Then some $x \in K$ lies in the fractional
ideal $I^{-1} = \{x \in K : xI \subseteq A\}$ but not in $A$.

This is Mathlib's `FractionalIdeal.exists_notMem_one_of_ne_bot` with `IsDedekindDomain A`
weakened to `IsNoetherianRing A` and `Ring.DimensionLEOne A`, as K. Conrad,
*The conductor ideal of an order*, proof of Lemma 3.2(2) (p. 5), observes for orders; the
argument is Conrad, *Ideal factorization*, Lemma 3.1 and the proof of Theorem 3.2 (pp. 4–5). -/
theorem FractionalIdeal.exists_notMem_one_of_ne_bot_of_dimensionLEOne {I : Ideal A}
    (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) :
    ∃ x ∈ (I⁻¹ : FractionalIdeal A⁰ K), x ∉ (1 : FractionalIdeal A⁰ K) :=
  Set.not_subset.1 <| not_inv_le_one_of_ne_bot_of_dimensionLEOne hI0 hI1

end DimensionLEOne

namespace NumberField.IsOrder

variable {K : Type*} [Field K] [NumberField K] {O : Subalgebra ℤ K}

/-- **An order is a Noetherian ring.** Let $O$ be an order in a number field $K$. Then $O$ is a
Noetherian ring, being a finitely generated $\mathbb{Z}$-module. -/
theorem isNoetherianRing (hO : NumberField.IsOrder K O) : IsNoetherianRing O := by
  have := hO.moduleFinite
  exact isNoetherian_of_tower ℤ (isNoetherian_of_isNoetherianRing_of_finite ℤ O)

/-- **An order has dimension at most one.** Let $O$ be an order in a number field $K$. Then every
nonzero prime ideal of $O$ is maximal (`NumberField.IsOrder.isMaximal_of_isPrime`). -/
theorem dimensionLEOne (hO : NumberField.IsOrder K O) : Ring.DimensionLEOne O :=
  ⟨fun {p} hp0 hp => by
    have := hp
    exact hO.isMaximal_of_isPrime hp0⟩

/-- **A proper ideal of an order has a strictly larger colon.** Let $K$ be a number field, $O$
an order in $K$ (`NumberField.IsOrder`), and $\mathfrak{b}$ an ideal of $O$ with
$\mathfrak{b} \neq 0$ and $\mathfrak{b} \neq O$. Then some $x \in K$ with $x \notin O$
satisfies $x\mathfrak{b} \subseteq O$; that is,
$O \subsetneq \{x \in K : x\mathfrak{b} \subseteq O\}$.

This is K. Conrad, *The conductor ideal of an order*, Lemma 3.2(2) (p. 5), for the ideals of
$O$, with the argument of Conrad, *Ideal factorization*, Lemma 3.1 and the proof of Theorem 3.2
(pp. 4–5), which uses only that $O$ is a Noetherian domain in which nonzero primes are maximal
(`FractionalIdeal.exists_notMem_one_of_ne_bot_of_dimensionLEOne`). -/
theorem exists_notMem_mul_mem (hO : NumberField.IsOrder K O) {b : Ideal O} (hb0 : b ≠ ⊥)
    (hb1 : b ≠ ⊤) : ∃ x : K, x ∉ O ∧ ∀ y ∈ b, x * (y : K) ∈ O := by
  have := hO.isFractionRing
  have := hO.isNoetherianRing
  have := hO.dimensionLEOne
  obtain ⟨x, hxinv, hx1⟩ :=
    FractionalIdeal.exists_notMem_one_of_ne_bot_of_dimensionLEOne (K := K) hb0 hb1
  rw [FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.mpr hb0)] at hxinv
  refine ⟨x, fun hxO => hx1 ((FractionalIdeal.mem_one_iff _).mpr ⟨⟨x, hxO⟩, rfl⟩),
    fun y hy => ?_⟩
  obtain ⟨z, hz⟩ := (FractionalIdeal.mem_one_iff _).mp
    (hxinv (y : K) ((FractionalIdeal.mem_coeIdeal _).mpr ⟨y, hy, rfl⟩))
  rw [← hz]
  exact z.2

omit [NumberField K] in
/-- The condition $x\mathfrak{b} \subseteq \mathfrak{b}$ as an inclusion of fractional ideals. -/
private theorem spanSingleton_mul_le_iff [IsFractionRing O K] {b : Ideal O} {x : K} :
    FractionalIdeal.spanSingleton O⁰ x * (b : FractionalIdeal O⁰ K) ≤ b ↔
      ∀ y ∈ b, ∃ z ∈ b, (z : K) = x * y := by
  constructor
  · intro h y hy
    have hmem := h (FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ x)
      ((FractionalIdeal.mem_coeIdeal _).mpr ⟨y, hy, rfl⟩))
    obtain ⟨z, hz, hzx⟩ := (FractionalIdeal.mem_coeIdeal _).mp hmem
    exact ⟨z, hz, hzx⟩
  · intro h
    rw [FractionalIdeal.mul_le]
    intro i hi j hj
    obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).mp hi
    obtain ⟨y, hy, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hj
    obtain ⟨z, hz, hzx⟩ := h y hy
    refine (FractionalIdeal.mem_coeIdeal _).mpr ⟨a * z, b.mul_mem_left a hz, ?_⟩
    change ((a * z : O) : K) = a • x * (y : K)
    rw [Subalgebra.coe_mul, hzx, Algebra.smul_def, mul_assoc]
    rfl

/-- **Invertibility of a prime ideal of an order.** Let $K$ be a number field, $O$ an order in
$K$ (`NumberField.IsOrder`), and $\mathfrak{p}$ a nonzero prime ideal of $O$. Then $\mathfrak{p}$
is invertible as a fractional ideal of $O$ (a unit of the monoid `FractionalIdeal O⁰ K`, whose
identity is $O$: some fractional ideal $\mathfrak{p}'$ has $\mathfrak{p}\mathfrak{p}' = O$) if
and only if $\{x \in K : x\mathfrak{p} \subseteq \mathfrak{p}\} = O$.

This is K. Conrad, *The conductor ideal of an order*, Theorem 3.4 with its proof (p. 5). Mathlib's
fractional ideals are the $O$-submodules $M$ of $K$ with $aM \subseteq O$ for some $a \neq 0$;
as $O$ is Noetherian, these are the finitely generated ones. -/
theorem isUnit_coeIdeal_iff_setOf_mul_mem_eq (hO : NumberField.IsOrder K O) {p : Ideal O}
    [hp : p.IsPrime] (hp0 : p ≠ ⊥) :
    IsUnit (p : FractionalIdeal O⁰ K) ↔
      {x : K | ∀ y ∈ p, ∃ z ∈ p, (z : K) = x * y} = (O : Set K) := by
  have := hO.isFractionRing
  constructor
  · rintro ⟨u, hu⟩
    ext x
    constructor
    · intro hx
      have hle := spanSingleton_mul_le_iff.mpr hx
      have h1 : FractionalIdeal.spanSingleton O⁰ x ≤ 1 :=
        calc FractionalIdeal.spanSingleton O⁰ x
            = FractionalIdeal.spanSingleton O⁰ x * ↑u * ↑u⁻¹ := by
              rw [mul_assoc, Units.mul_inv, mul_one]
          _ ≤ ↑u * ↑u⁻¹ := by
              rw [hu]
              exact mul_le_mul_left hle _
          _ = 1 := Units.mul_inv u
      obtain ⟨x', hx'⟩ :=
        (FractionalIdeal.mem_one_iff _).mp (h1 (FractionalIdeal.mem_spanSingleton_self _ x))
      rw [← hx']
      exact x'.2
    · intro hxO y hy
      exact ⟨⟨x, hxO⟩ * y, p.mul_mem_left _ hy, rfl⟩
  · intro hset
    by_contra hnu
    have hmax : p.IsMaximal := hO.isMaximal_of_isPrime hp0
    obtain ⟨y, hyO, hy⟩ := hO.exists_notMem_mul_mem hp0 hp.ne_top
    have hyp : FractionalIdeal.spanSingleton O⁰ y * (p : FractionalIdeal O⁰ K) ≤ 1 := by
      rw [FractionalIdeal.mul_le]
      intro i hi j hj
      obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).mp hi
      obtain ⟨z, hz, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hj
      refine (FractionalIdeal.mem_one_iff _).mpr ⟨a * ⟨_, hy z hz⟩, ?_⟩
      change ((a : K) * (y * (z : K))) = a • y * (z : K)
      rw [Algebra.smul_def, mul_assoc]
      rfl
    have hF : (1 + FractionalIdeal.spanSingleton O⁰ y) * (p : FractionalIdeal O⁰ K) =
        (p : FractionalIdeal O⁰ K) ⊔ FractionalIdeal.spanSingleton O⁰ y * p := by
      rw [add_mul, one_mul, FractionalIdeal.sup_eq_add]
    obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp
      (hF ▸ sup_le FractionalIdeal.coeIdeal_le_one hyp)
    have hpI : p ≤ I := (FractionalIdeal.coeIdeal_le_coeIdeal K).mp (hI ▸ hF ▸ le_sup_left)
    by_cases hItop : I = ⊤
    · apply hnu
      refine IsUnit.of_mul_eq_one (1 + FractionalIdeal.spanSingleton O⁰ y) ?_
      rw [mul_comm, ← hI, hItop, FractionalIdeal.coeIdeal_top]
    · have hIp : p = I := hmax.eq_of_le hItop hpI
      have hle : FractionalIdeal.spanSingleton O⁰ y * (p : FractionalIdeal O⁰ K) ≤ p := by
        have h := hF ▸ (le_sup_right :
          FractionalIdeal.spanSingleton O⁰ y * (p : FractionalIdeal O⁰ K) ≤
            (p : FractionalIdeal O⁰ K) ⊔ FractionalIdeal.spanSingleton O⁰ y * p)
        rwa [← hI, ← hIp] at h
      have hymem : y ∈ {x : K | ∀ y ∈ p, ∃ z ∈ p, (z : K) = x * y} :=
        spanSingleton_mul_le_iff.mp hle
      rw [hset] at hymem
      exact hyO hymem

omit [NumberField K] in
/-- A finite product of ideals that are invertible as fractional ideals is invertible. -/
private theorem isUnit_coeIdeal_multiset_prod
    (s : Multiset (Ideal O)) (hs : ∀ p ∈ s, IsUnit (p : FractionalIdeal O⁰ K)) :
    IsUnit (s.prod : FractionalIdeal O⁰ K) := by
  induction s using Multiset.induction_on with
  | empty => simp [Ideal.one_eq_top, FractionalIdeal.coeIdeal_top]
  | cons p s ih =>
    rw [Multiset.prod_cons, FractionalIdeal.coeIdeal_mul]
    exact (hs p (Multiset.mem_cons_self _ _)).mul
      (ih fun q hq => hs q (Multiset.mem_cons_of_mem hq))

/-- **Ideals of an order coprime to the conductor are invertible.** Let $K$ be a number field
with ring of integers $\mathcal{O}_K$ (`integralClosure ℤ K`), let $O$ be an order in $K$
(`NumberField.IsOrder`), and let $\mathfrak{c} = \{x \in \mathcal{O}_K : x\mathcal{O}_K
\subseteq O\}$ be its conductor (`Subalgebra.conductorIdeal` of $O$ inside $\mathcal{O}_K$,
pulled back to an ideal of $O$). Let $\mathfrak{b}$ be a nonzero ideal of $O$ with
$\mathfrak{b} + \mathfrak{c} = O$. Then:
1. $\mathfrak{b}$ is the product of a finite multiset of prime ideals of $O$, each invertible as a
   fractional ideal of $O$ (a unit of `FractionalIdeal O⁰ K`); the multiset is empty when
   $\mathfrak{b} = O$;
2. $\mathfrak{b}$ is invertible as a fractional ideal of $O$: some fractional ideal
   $\mathfrak{b}'$ has $\mathfrak{b}\mathfrak{b}' = O$.

This is K. Conrad, *The conductor ideal of an order*, Theorem 3.6 (p. 6), proved as there by
induction on the index $[O : \mathfrak{b}]$, using Theorem 3.1, Lemma 3.2 and Theorem 3.4
(p. 5); ideals are relatively prime when their sum is $O$ (Conrad, §3, p. 4). The strict
inclusion $\mathfrak{b} \subsetneq \mathfrak{p}^{-1}\mathfrak{b}$ is shown with the multiplier
ring of $\mathfrak{p}^{-1}\mathfrak{b}$ (Theorem 3.1) instead of Conrad's growth of
$[O : \mathfrak{p}^k]$. -/
theorem prod_and_isUnit_of_sup_conductor_eq_top (hO : NumberField.IsOrder K O) {b : Ideal O}
    (hb : b ≠ ⊥)
    (hbc : b ⊔ ((O.comap (integralClosure ℤ K).val).conductorIdeal).comap
      (Subalgebra.inclusion hO.le_integralClosure) = ⊤) :
    (∃ s : Multiset (Ideal O),
      (∀ p ∈ s, p.IsPrime ∧ IsUnit (p : FractionalIdeal O⁰ K)) ∧ s.prod = b) ∧
      IsUnit (b : FractionalIdeal O⁰ K) := by
  have := hO.isFractionRing
  set c := ((O.comap (integralClosure ℤ K).val).conductorIdeal).comap
    (Subalgebra.inclusion hO.le_integralClosure) with hc
  suffices H : ∀ n : ℕ, ∀ b : Ideal O, Nat.card (O ⧸ b) = n → b ≠ ⊥ → b ⊔ c = ⊤ →
      ∃ s : Multiset (Ideal O),
        (∀ p ∈ s, p.IsPrime ∧ IsUnit (p : FractionalIdeal O⁰ K)) ∧ s.prod = b by
    obtain ⟨s, hs, hprod⟩ := H _ b rfl hb hbc
    refine ⟨⟨s, hs, hprod⟩, ?_⟩
    rw [← hprod]
    exact isUnit_coeIdeal_multiset_prod s fun p hp => (hs p hp).2
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro b hn hb hbc
  by_cases hbtop : b = ⊤
  · exact ⟨0, by simp, by simp [hbtop, Ideal.one_eq_top]⟩
  obtain ⟨p, hpmax, hbp⟩ := b.exists_le_maximal hbtop
  have hp0 : p ≠ ⊥ := fun h => hb (le_bot_iff.mp (h ▸ hbp))
  have hpc : p ⊔ c = ⊤ := top_unique (hbc ▸ sup_le_sup_right hbp c)
  have hpu : IsUnit (p : FractionalIdeal O⁰ K) := by
    have := hpmax.isPrime
    exact (hO.isUnit_coeIdeal_iff_setOf_mul_mem_eq hp0).mpr (hO.setOf_mul_mem_eq hp0 hpc)
  obtain ⟨u, hu⟩ := hpu
  have hJ : (↑u⁻¹ * (b : FractionalIdeal O⁰ K)) ≤ 1 :=
    calc (↑u⁻¹ * (b : FractionalIdeal O⁰ K)) ≤ ↑u⁻¹ * (p : FractionalIdeal O⁰ K) :=
          mul_le_mul_right ((FractionalIdeal.coeIdeal_le_coeIdeal K).mpr hbp) _
      _ = 1 := by rw [← hu, Units.inv_mul]
  obtain ⟨b', hb'⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hJ
  have hpb' : p * b' = b := by
    apply FractionalIdeal.coeIdeal_injective (K := K)
    change ((p * b' : Ideal O) : FractionalIdeal O⁰ K) = b
    rw [FractionalIdeal.coeIdeal_mul, hb', ← hu, ← mul_assoc, Units.mul_inv, one_mul]
  have hb'0 : b' ≠ ⊥ := by
    rintro rfl
    apply hb
    rw [← hpb', Ideal.mul_bot]
  have hbb' : b ≤ b' := hpb' ▸ Ideal.mul_le.mpr fun _ _ _ hy => b'.mul_mem_left _ hy
  have hb'c : b' ⊔ c = ⊤ := top_unique (hbc ▸ sup_le_sup_right hbb' c)
  have hlt : b < b' := by
    refine lt_of_le_of_ne hbb' fun heq => hpmax.ne_top ?_
    have hinv : (↑u⁻¹ : FractionalIdeal O⁰ K) ≤ 1 := by
      intro x hx
      have hxset : x ∈ {x : K | ∀ y ∈ b', ∃ z ∈ b', (z : K) = x * y} := by
        intro y hy
        have hmem : x * (y : K) ∈ (↑u⁻¹ * (b' : FractionalIdeal O⁰ K)) :=
          FractionalIdeal.mul_mem_mul hx ((FractionalIdeal.mem_coeIdeal _).mpr ⟨y, hy, rfl⟩)
        rw [← heq, ← hb'] at hmem
        obtain ⟨z, hz, hzx⟩ := (FractionalIdeal.mem_coeIdeal _).mp hmem
        exact ⟨z, hz, hzx⟩
      rw [hO.setOf_mul_mem_eq hb'0 hb'c] at hxset
      exact (FractionalIdeal.mem_one_iff _).mpr ⟨⟨x, hxset⟩, rfl⟩
    have h1p : ((⊤ : Ideal O) : FractionalIdeal O⁰ K) ≤ p :=
      calc ((⊤ : Ideal O) : FractionalIdeal O⁰ K) = ↑u * ↑u⁻¹ := by
            rw [FractionalIdeal.coeIdeal_top, Units.mul_inv]
        _ ≤ ↑u * 1 := mul_le_mul_right hinv _
        _ = p := by rw [mul_one, hu]
    exact top_unique ((FractionalIdeal.coeIdeal_le_coeIdeal K).mp h1p)
  have hfin := hO.finite_quotient hb
  have hcard : Nat.card (O ⧸ b') < Nat.card (O ⧸ b) := by
    have hne : Nat.card (O ⧸ b) ≠ 0 := Nat.card_ne_zero.mpr ⟨inferInstance, hfin⟩
    have : b.toAddSubgroup.FiniteIndex := ⟨hne⟩
    rw [← Submodule.cardQuot_apply, ← Submodule.cardQuot_apply]
    exact AddSubgroup.index_strictAnti (Submodule.toAddSubgroup_strictMono hlt)
  obtain ⟨s', hs', hs'prod⟩ := ih _ (hn ▸ hcard) b' rfl hb'0 hb'c
  refine ⟨p ::ₘ s', fun q hq => ?_, ?_⟩
  · rcases Multiset.mem_cons.mp hq with rfl | hq
    · exact ⟨hpmax.isPrime, ⟨u, hu⟩⟩
    · exact hs' q hq
  · rw [Multiset.prod_cons, hs'prod, hpb']

end NumberField.IsOrder

end
