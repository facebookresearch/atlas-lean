/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

@[expose] public section

/-!
# Integrality over an integrally closed domain via minimal polynomials

For an integrally closed domain `R` with fraction field `K` and a field extension `L`
of `K`, an element of `L` algebraic over `K` is integral over `R` if and only if its
`K`-minimal polynomial lifts to `R`, equivalently every coefficient lies in the range
of `algebraMap R K`.

The equality `minpoly K x = (minpoly R x).map (algebraMap R K)` gives another
characterization of integrality.
-/

variable {R K L : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]

namespace minpoly

/-- **Integrality via a lift of the minimal polynomial.** Let $R$ be an integrally closed domain
with fraction field $K$, and let $L$ be a field extension of $K$ that is also an $R$-algebra,
with the $R$-algebra structure on $L$ the composite of $R \to K$ and $K \to L$. An element
$x \in L$ that is algebraic over $K$ is integral over $R$ if and only if the minimal polynomial
of $x$ over $K$ is the image of a polynomial in $R[X]$ under the map $R[X] \to K[X]$ that
applies $R \to K$ to each coefficient. -/
theorem isIntegral_iff_mem_lifts {x : L} (hx : IsAlgebraic K x) :
    IsIntegral R x ↔ minpoly K x ∈ Polynomial.lifts (algebraMap R K) := by
  constructor
  · intro h
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' K h]
    exact Polynomial.mem_lifts _ |>.mpr ⟨_, rfl⟩
  · intro h
    obtain ⟨q, hq, -, hqmonic⟩ :=
      Polynomial.lifts_and_natDegree_eq_and_monic h (minpoly.monic hx.isIntegral)
    refine ⟨q, hqmonic, ?_⟩
    have hroot : Polynomial.aeval x (minpoly K x) = 0 := minpoly.aeval K x
    rw [← hq] at hroot
    rwa [Polynomial.aeval_map_algebraMap] at hroot

/-- **Integrality via the coefficients of the minimal polynomial.** Let $R$ be an integrally
closed domain with fraction field $K$, and let $L$ be a field extension of $K$ that is also an
$R$-algebra, with the $R$-algebra structure on $L$ the composite of $R \to K$ and $K \to L$.
An element $x \in L$ that is algebraic over $K$ is integral over $R$ if and only if every
coefficient of the minimal polynomial of $x$ over $K$ lies in the image of $R$ in $K$. -/
theorem isIntegral_iff_coeff_mem_range {x : L} (hx : IsAlgebraic K x) :
    IsIntegral R x ↔ ∀ n, (minpoly K x).coeff n ∈ Set.range (algebraMap R K) := by
  rw [isIntegral_iff_mem_lifts hx, Polynomial.lifts_iff_coeff_lifts]

end minpoly

namespace IsIntegrallyClosed

/-- **Integrality via equality of minimal polynomials.** Let $A$ be an integrally closed domain
with fraction field $K$, and let $L$ be a field extension of $K$ that is also an $A$-algebra,
with the $A$-algebra structure on $L$ the composite of $A \to K$ and $K \to L$. An element
$\alpha \in L$ that is integral over $K$ is integral over $A$ if and only if the minimal
polynomial of $\alpha$ over $K$ equals the image of the minimal polynomial of $\alpha$ over $A$
under the map $A[X] \to K[X]$ that applies $A \to K$ to each coefficient. Here the minimal
polynomial of $\alpha$ over $A$ is taken to be $0$ when $\alpha$ is not integral over $A$.

Source: Proposition 1.28, in equality form. -/
theorem minpoly_eq_map_iff_isIntegral
    {A : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    {α : L} (hα : IsIntegral K α) :
    minpoly K α = (minpoly A α).map (algebraMap A K) ↔ IsIntegral A α := by
  constructor
  · intro h
    rw [minpoly.isIntegral_iff_coeff_mem_range hα.isAlgebraic]
    intro i
    rw [h, Polynomial.coeff_map]
    exact ⟨_, rfl⟩
  · intro hInt
    exact minpoly.isIntegrallyClosed_eq_field_fractions' K hInt

end IsIntegrallyClosed
