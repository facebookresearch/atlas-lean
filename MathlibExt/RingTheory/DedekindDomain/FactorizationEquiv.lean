/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Prime-exponent equivalence for fractional ideals of a Dedekind domain

For a Dedekind domain `R` with fraction field `K`, every nonzero fractional ideal
factors uniquely as a finite product of prime powers. This file bundles that
factorization into a multiplicative equivalence between the units of the type of
fractional ideals and the finitely supported prime-exponent functions.

## Main definitions

* `FractionalIdeal.unitsToFinsupp`: sends a unit fractional ideal to its prime
  exponents, via `FractionalIdeal.count`.
* `FractionalIdeal.finsuppToUnits`: reconstructs a unit fractional ideal as the
  finite product of prime powers prescribed by a finitely supported function.
* `FractionalIdeal.factorizationMulEquiv`: the bundled multiplicative
  equivalence `(FractionalIdeal R⁰ K)ˣ ≃* Multiplicative (HeightOneSpectrum R →₀ ℤ)`.

## Main results

* `FractionalIdeal.toUnits_left_inv` and `FractionalIdeal.toUnits_right_inv`:
  the two inverse laws, from `FractionalIdeal.finprod_heightOneSpectrum_factorization'`
  and `FractionalIdeal.count_finsuppProd`.
* `FractionalIdeal.unitsToFinsupp_mul`: valuations add under multiplication, from
  `FractionalIdeal.count_mul`.
-/

@[expose] public section

open scoped nonZeroDivisors

open IsDedekindDomain

namespace FractionalIdeal

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

variable (K)

/-- **Support of the prime exponents of a fractional ideal.** Let $R$ be a Dedekind domain with
fraction field $K$. For a unit fractional ideal $I$ of $R$ in $K$, this is the finite set of
height-one primes $v$ of $R$ at which the $v$-adic valuation of $I$ is nonzero. -/
noncomputable def unitsSupportFinset (u : (FractionalIdeal R⁰ K)ˣ) :
    Finset (HeightOneSpectrum R) :=
  (Filter.eventually_cofinite.mp (finite_factors (u : FractionalIdeal R⁰ K))).toFinset

theorem mem_unitsSupportFinset (u : (FractionalIdeal R⁰ K)ˣ) (v : HeightOneSpectrum R) :
    v ∈ unitsSupportFinset K u ↔ count K v (u : FractionalIdeal R⁰ K) ≠ 0 := by
  unfold unitsSupportFinset
  exact Set.Finite.mem_toFinset _

/-- **Prime exponents of an invertible fractional ideal.** Let $R$ be a Dedekind domain with
fraction field $K$, and let $I$ be a unit of the monoid of fractional ideals of $R$ in $K$.
The prime exponents of $I$ form the finitely supported function from the height-one primes of
$R$ to $\mathbb{Z}$ that sends each height-one prime $v$ to the exponent $\operatorname{ord}_v(I)$
of $v$ in the factorization $I = \prod_v v^{\operatorname{ord}_v(I)}$; its support is the finite
set of $v$ with $\operatorname{ord}_v(I) \neq 0$. -/
noncomputable def unitsToFinsupp (u : (FractionalIdeal R⁰ K)ˣ) :
    HeightOneSpectrum R →₀ ℤ :=
  Finsupp.onFinset (unitsSupportFinset K u) (fun v => count K v (u : FractionalIdeal R⁰ K))
    (fun v hv => (mem_unitsSupportFinset K u v).mpr hv)

@[simp]
theorem unitsToFinsupp_apply (u : (FractionalIdeal R⁰ K)ˣ) (v : HeightOneSpectrum R) :
    unitsToFinsupp K u v = count K v (u : FractionalIdeal R⁰ K) :=
  rfl

/-- **Products of prime powers are nonzero.** Let $R$ be a Dedekind domain with fraction field
$K$. For every finitely supported function $e$ from the height-one primes of $R$ to $\mathbb{Z}$,
the fractional ideal $\prod_v v^{e(v)}$ of $R$ in $K$, the product over the primes $v$ with
$e(v) \neq 0$, is nonzero. -/
theorem finsuppProd_ne_zero (e : HeightOneSpectrum R →₀ ℤ) :
    e.prod (fun v n => (v.asIdeal : FractionalIdeal R⁰ K) ^ n) ≠ 0 := by
  rw [Finsupp.prod_ne_zero_iff]
  intro v _
  exact zpow_ne_zero _ (coeIdeal_ne_zero.mpr v.ne_bot)

/-- **Fractional ideal with prescribed prime exponents.** Let $R$ be a Dedekind domain with
fraction field $K$. For a finitely supported function $e$ from the height-one primes of $R$ to
$\mathbb{Z}$, this is the fractional ideal $\prod_v v^{e(v)}$ of $R$ in $K$, the product over the
primes $v$ with $e(v) \neq 0$, regarded as a unit of the monoid of fractional ideals (it is
nonzero, hence invertible). -/
noncomputable def finsuppToUnits (e : HeightOneSpectrum R →₀ ℤ) :
    (FractionalIdeal R⁰ K)ˣ :=
  Units.mk0 _ (finsuppProd_ne_zero K e)

@[simp]
theorem finsuppToUnits_val (e : HeightOneSpectrum R →₀ ℤ) :
    (↑(finsuppToUnits K e) : FractionalIdeal R⁰ K) =
      e.prod (fun v n => (v.asIdeal : FractionalIdeal R⁰ K) ^ n) :=
  rfl

/-- **Valuations of a product of prime powers.** Let $R$ be a Dedekind domain with fraction
field $K$. For every finitely supported function $e$ from the height-one primes of $R$ to
$\mathbb{Z}$ and every height-one prime $v$ of $R$, the $v$-adic valuation of the fractional
ideal $\prod_w w^{e(w)}$, the product over the primes $w$ with $e(w) \neq 0$, equals $e(v)$. -/
@[simp]
theorem count_finsuppToUnits (v : HeightOneSpectrum R) (e : HeightOneSpectrum R →₀ ℤ) :
    count K v (↑(finsuppToUnits K e) : FractionalIdeal R⁰ K) = e v :=
  count_finsuppProd K v e

/-- **Reconstructing a fractional ideal from its prime exponents.** Let $R$ be a Dedekind domain
with fraction field $K$, and for a unit fractional ideal $I$ of $R$ in $K$ and a height-one prime
$v$ of $R$ write $\operatorname{val}_v(I)$ for the $v$-adic valuation of $I$. Every unit
fractional ideal $I$ of $R$ in $K$ equals $\prod_v v^{\operatorname{val}_v(I)}$, the product over
the height-one primes $v$ of $R$ with $\operatorname{val}_v(I) \neq 0$. -/
theorem toUnits_left_inv (u : (FractionalIdeal R⁰ K)ˣ) :
    finsuppToUnits K (unitsToFinsupp K u) = u := by
  refine Units.ext ?_
  have h0 : ∀ v : HeightOneSpectrum R, v ∉ unitsSupportFinset K u →
      (v.asIdeal : FractionalIdeal R⁰ K) ^ count K v (u : FractionalIdeal R⁰ K) = 1 := by
    intro v hv
    have hcount : count K v (u : FractionalIdeal R⁰ K) = 0 := by
      by_contra hne
      exact hv ((mem_unitsSupportFinset K u v).mpr hne)
    rw [hcount, zpow_zero]
  have hsup : Function.mulSupport
      (fun v => (v.asIdeal : FractionalIdeal R⁰ K) ^ count K v (u : FractionalIdeal R⁰ K)) ⊆
      ↑(unitsSupportFinset K u) := by
    intro v hv
    rw [Finset.mem_coe]
    by_contra hcon
    exact hv (h0 v hcon)
  calc (↑(finsuppToUnits K (unitsToFinsupp K u)) : FractionalIdeal R⁰ K)
      = ∏ v ∈ unitsSupportFinset K u,
        (v.asIdeal : FractionalIdeal R⁰ K) ^ count K v (u : FractionalIdeal R⁰ K) :=
        Finsupp.prod_onFinset _ _ _ _ (fun i _ => zpow_zero _)
    _ = ∏ᶠ v, (v.asIdeal : FractionalIdeal R⁰ K) ^ count K v (u : FractionalIdeal R⁰ K) :=
        (finprod_eq_finsetProd_of_mulSupport_subset _ hsup).symm
    _ = (u : FractionalIdeal R⁰ K) := finprod_heightOneSpectrum_factorization' K u.ne_zero

/-- **Recovering prime exponents from a product of prime powers.** Let $R$ be a Dedekind domain
with fraction field $K$, and let $e$ be a finitely supported function from the height-one primes
of $R$ to $\mathbb{Z}$. The prime-exponent function of the fractional ideal $\prod_w w^{e(w)}$,
the product over the primes $w$ with $e(w) \neq 0$, is $e$: its $v$-adic valuation is $e(v)$
for every height-one prime $v$ of $R$. -/
theorem toUnits_right_inv (e : HeightOneSpectrum R →₀ ℤ) :
    unitsToFinsupp K (finsuppToUnits K e) = e := by
  ext v
  exact count_finsuppProd K v e

/-- **Prime exponents are additive.** Let $R$ be a Dedekind domain with fraction field $K$, and
for a unit fractional ideal $I$ of $R$ in $K$ and a height-one prime $v$ of $R$ write
$\operatorname{val}_v(I)$ for the $v$-adic valuation of $I$. For all unit fractional ideals $I$
and $J$ of $R$ in $K$ and every height-one prime $v$ of $R$,
$\operatorname{val}_v(IJ) = \operatorname{val}_v(I) + \operatorname{val}_v(J)$. -/
theorem unitsToFinsupp_mul (u v : (FractionalIdeal R⁰ K)ˣ) :
    unitsToFinsupp K (u * v) = unitsToFinsupp K u + unitsToFinsupp K v := by
  ext w
  simp only [unitsToFinsupp_apply, Units.val_mul, Finsupp.add_apply]
  exact count_mul K w u.ne_zero v.ne_zero

@[simp]
theorem unitsToFinsupp_one : unitsToFinsupp K (1 : (FractionalIdeal R⁰ K)ˣ) = 0 := by
  ext w
  rw [unitsToFinsupp_apply, Units.val_one, count_one K w, Finsupp.zero_apply]

/-- **Prime factorization isomorphism for fractional ideals.** Let $R$ be a Dedekind domain with
fraction field $K$, and for a unit fractional ideal $I$ of $R$ in $K$ and a height-one prime $v$
of $R$ write $\operatorname{val}_v(I)$ for the $v$-adic valuation of $I$. The factorization
isomorphism is the group isomorphism from the unit group of the fractional ideals of $R$ in $K$
to the additive group of finitely supported functions from the height-one primes of $R$ to
$\mathbb{Z}$ (written multiplicatively) that sends $I$ to the function
$v \mapsto \operatorname{val}_v(I)$. Its inverse sends $e$ to $\prod_v v^{e(v)}$, the product
over the primes $v$ with $e(v) \neq 0$. -/
noncomputable def factorizationMulEquiv :
    (FractionalIdeal R⁰ K)ˣ ≃* Multiplicative (HeightOneSpectrum R →₀ ℤ) where
  toFun u := Multiplicative.ofAdd (unitsToFinsupp K u)
  invFun e := finsuppToUnits K (Multiplicative.toAdd e)
  left_inv u := by
    change finsuppToUnits K
      (Multiplicative.toAdd (Multiplicative.ofAdd (unitsToFinsupp K u))) = u
    rw [toAdd_ofAdd]
    exact toUnits_left_inv K u
  right_inv e := by
    change Multiplicative.ofAdd
      (unitsToFinsupp K (finsuppToUnits K (Multiplicative.toAdd e))) = e
    rw [toUnits_right_inv, ofAdd_toAdd]
  map_mul' u v := by
    rw [← ofAdd_add, unitsToFinsupp_mul]

@[simp]
theorem factorizationMulEquiv_apply (u : (FractionalIdeal R⁰ K)ˣ) (v : HeightOneSpectrum R) :
    Multiplicative.toAdd (factorizationMulEquiv K u) v =
      count K v (u : FractionalIdeal R⁰ K) :=
  rfl

@[simp]
theorem factorizationMulEquiv_symm_val (e : Multiplicative (HeightOneSpectrum R →₀ ℤ)) :
    ((↑((factorizationMulEquiv K).symm e) : FractionalIdeal R⁰ K)) =
      (Multiplicative.toAdd e).prod (fun v n => (v.asIdeal : FractionalIdeal R⁰ K) ^ n) :=
  rfl

/-- **Exponent function of a prime ideal.** Let $R$ be a Dedekind domain with fraction field
$K$ and let $w$ be a height-one prime of $R$. The factorization isomorphism sends the fractional
ideal $w$, as a unit fractional ideal of $R$ in $K$, to the function on height-one primes of $R$
that is $1$ at $w$ and $0$ elsewhere. -/
theorem factorizationMulEquiv_prime_self (w : HeightOneSpectrum R) :
    Multiplicative.toAdd
        (factorizationMulEquiv K
          (Units.mk0 _ (coeIdeal_ne_zero.mpr w.ne_bot))) =
      Finsupp.single w 1 := by
  ext v
  classical
  rw [factorizationMulEquiv_apply, Units.val_mk0, count_maximal]
  split_ifs with h
  · rw [h, Finsupp.single_eq_same]
  · exact (Finsupp.single_eq_of_ne' h).symm

/-- **Inverse factorization of a single prime power.** Let $R$ be a Dedekind domain with fraction
field $K$, let $w$ be a height-one prime of $R$ and let $n \in \mathbb{Z}$. The inverse of the
factorization isomorphism sends the function on height-one primes of $R$ that is $n$ at $w$ and
$0$ elsewhere to the fractional ideal $w^n$. -/
theorem symm_single_zpow (w : HeightOneSpectrum R) (n : ℤ) :
    (↑((factorizationMulEquiv K).symm (Multiplicative.ofAdd (Finsupp.single w n))) :
      FractionalIdeal R⁰ K) = (w.asIdeal : FractionalIdeal R⁰ K) ^ n := by
  change (Finsupp.single w n).prod (fun v m => (v.asIdeal : FractionalIdeal R⁰ K) ^ m) = _
  exact Finsupp.prod_single_index (zpow_zero _)

end FractionalIdeal
