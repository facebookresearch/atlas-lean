/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Lenstra's bound for the different

Let `A → B` be a finite torsion-free extension of discrete valuation rings whose extension of
fraction fields `L / K` is separable, of degree `n`, and let `e` be the ramification index, so
that `𝔪_A B = 𝔪_B ^ e`. If the different ideal of `B` over `A` is `𝔪_B ^ r`, then

`r ≤ e - 1 + e * ord_A(n)`,

where `ord_A` is the normalized valuation of `A`, with values in `ℕ∞`. No separability of the
residue field extension is assumed.

This is the proposition that A. Javanpeykar attributes to H. W. Lenstra, Jr.:
A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number
Theory 8 (2014), 89–140, §4.1, Proposition 4.1.1 and its proof (arXiv:1403.6404v1, p. 21).
The proof is Lenstra's: the trace of `1 / (n x)`, for `x` a uniformizer of `A`, is `1 / x`,
which is not in `A`. Here it is phrased through Mathlib's
`not_dvd_differentIdeal_of_intTrace_notMem`, with the element `1`, whose trace is `n`, and the
ideal `𝔪_A ^ (ord_A(n) + 1)`.

## Main results

* `IsDiscreteValuationRing.le_addVal_finrank_of_differentIdeal_eq_maximalIdeal_pow`: Lenstra's
  bound, for separable fraction field extensions.
* `IsDiscreteValuationRing.le_addVal_finrank_of_differentIdeal_eq_maximalIdeal_pow_of_charZero`:
  the same bound when `A` has characteristic zero, as Javanpeykar states it.
-/

@[expose] public section

open IsLocalRing
open IsDiscreteValuationRing (addVal addVal_le_iff_dvd addVal_pow addVal_uniformizer)

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace IsDiscreteValuationRing

variable (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
  [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B]
  [Module.IsTorsionFree A B] [Module.Finite A B]

/-- The integral trace of `1` in a finite torsion-free extension `B / A` of discrete valuation
rings is the degree of the extension of fraction fields. -/
theorem intTrace_one_eq_finrank_fractionRing :
    Algebra.intTrace A B 1 = (Module.finrank (FractionRing A) (FractionRing B) : A) := by
  apply IsFractionRing.injective A (FractionRing A)
  rw [Algebra.algebraMap_intTrace_fractionRing, map_one,
    ← map_one (algebraMap (FractionRing A) (FractionRing B)), Algebra.trace_algebraMap,
    nsmul_eq_mul, mul_one, map_natCast]

/-- **Lenstra's bound for the different.** Let `A` and `B` be discrete valuation rings with
maximal ideals `𝔪_A` and `𝔪_B`, and let `B` be an `A`-algebra that is finite and torsion-free
as an `A`-module, such that the extension `L / K` of fraction fields is separable; let `n` be its
degree. Let `e` and `r` be natural numbers with `𝔪_A B = 𝔪_B ^ e` and such that the different
ideal of `B` over `A` is `𝔪_B ^ r`. Then

`r ≤ e - 1 + e * ord_A(n)`

in `ℕ∞`, where `ord_A = IsDiscreteValuationRing.addVal A` is the normalized valuation of `A`
(`ord_A(n) = ⊤` when `n = 0` in `A`). No separability of the residue field extension is
assumed.

A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number
Theory 8 (2014), 89–140, §4.1, Proposition 4.1.1 (attributed to H. W. Lenstra, Jr.) and its
proof (arXiv:1403.6404v1, p. 21). Javanpeykar assumes that `A` has characteristic zero and
that `B` is the integral closure of `A` in `L`; this statement assumes instead that `L / K` is
separable and `B` finite over `A`, which follow from those hypotheses, and the integral closure
hypothesis is not used. -/
theorem le_addVal_finrank_of_differentIdeal_eq_maximalIdeal_pow
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)] (e r : ℕ)
    (he : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B ^ e)
    (hr : differentIdeal A B = maximalIdeal B ^ r) :
    (r : ℕ∞) ≤ ((e - 1 : ℕ) : ℕ∞) +
      e * addVal A (Module.finrank (FractionRing A) (FractionRing B) : A) := by
  set n := Module.finrank (FractionRing A) (FractionRing B)
  have he0 : e ≠ 0 := by
    rintro rfl
    have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap A B)
      Algebra.IsIntegral.isIntegral (maximalIdeal B)
    have hcomap : (maximalIdeal B).comap (algebraMap A B) = maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal hmax
    have hle : Ideal.map (algebraMap A B) (maximalIdeal A) ≤ maximalIdeal B := by
      rw [Ideal.map_le_iff_le_comap, hcomap]
    rw [he, pow_zero, Ideal.one_eq_top, top_le_iff] at hle
    exact (maximalIdeal.isMaximal B).ne_top hle
  cases hv : addVal A (n : A) with
  | top => simp [he0]
  | coe k =>
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
    have hP : maximalIdeal B ^ (e * (k + 1)) * ⊤ =
        Ideal.map (algebraMap A B) (maximalIdeal A ^ (k + 1)) := by
      rw [Ideal.mul_top, Ideal.map_pow, he, pow_mul]
    have hn : Algebra.intTrace A B 1 ∉ maximalIdeal A ^ (k + 1) := by
      rw [intTrace_one_eq_finrank_fractionRing, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton, ← addVal_le_iff_dvd, addVal_pow, addVal_uniformizer hϖ, hv,
        nsmul_eq_mul, mul_one, not_le]
      exact_mod_cast Nat.lt_succ_self k
    have hnd := not_dvd_differentIdeal_of_intTrace_notMem A
      (maximalIdeal B ^ (e * (k + 1))) ⊤ hP 1 Submodule.mem_top hn
    rw [hr] at hnd
    have hlt : r < e * (k + 1) := by
      by_contra h
      exact hnd (pow_dvd_pow _ (not_lt.mp h))
    have hrk : r ≤ e - 1 + e * k := by
      have : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr he0
      rw [Nat.mul_succ] at hlt
      omega
    exact_mod_cast hrk

/-- **Lenstra's bound for the different, in characteristic zero.** Let `A` be a discrete
valuation ring of characteristic zero and `B` a discrete valuation ring that is a finite
torsion-free `A`-algebra; let `n` be the degree of the extension of fraction fields. If
`𝔪_A B = 𝔪_B ^ e` and the different ideal of `B` over `A` is `𝔪_B ^ r`, then
`r ≤ e - 1 + e * ord_A(n)`, where `ord_A(n)` is finite as `n ≠ 0` in `A`.

A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number
Theory 8 (2014), 89–140, §4.1, Proposition 4.1.1 (arXiv:1403.6404v1, p. 21). Javanpeykar takes
`B` to be the integral closure of `A` in a finite extension `L` of `K`; such a `B` is finite
over `A`, as Javanpeykar notes in §4.1, and that hypothesis is not used otherwise. -/
theorem le_addVal_finrank_of_differentIdeal_eq_maximalIdeal_pow_of_charZero [CharZero A]
    (e r : ℕ) (he : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B ^ e)
    (hr : differentIdeal A B = maximalIdeal B ^ r) :
    (r : ℕ∞) ≤ ((e - 1 : ℕ) : ℕ∞) +
      e * addVal A (Module.finrank (FractionRing A) (FractionRing B) : A) := by
  have : FiniteDimensional (FractionRing A) (FractionRing B) := .of_isLocalization A B
    (nonZeroDivisors A)
  have : CharZero (FractionRing A) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective A (FractionRing A))
  exact le_addVal_finrank_of_differentIdeal_eq_maximalIdeal_pow A B e r he hr

end IsDiscreteValuationRing
