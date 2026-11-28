/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.KoszulComplex.Polynomial
public import MathlibExt.RingTheory.MvPolynomial.HomogeneousVariable
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Homogeneous cycles and boundaries in the polynomial Koszul complex

Let R be a commutative ring, I a linearly ordered variable type and
P = MvPolynomial I R. The exterior basis of
K_n = ⋀_P^n(I →₀ P) is indexed by n-element subsets of I, enumerated
in increasing order. A polynomial coefficient has its own homogeneous
degree, distinct from the exterior degree n.

The additive projection π_(n,d) takes the degree-d homogeneous component
of each polynomial coefficient in this basis. The Koszul differential
∂_n : K_(n+1) → K_n multiplies the ith deletion term by
(−1)^i X_(s_i), so π_(n,d+1)∂_n = ∂_n π_(n+1,d) and
π_(n,0)∂_n = 0.

A cycle in positive exterior degree with homogeneous coefficient degree
d+1 is the boundary of an element with homogeneous coefficient degree d.
A cycle in positive exterior degree with homogeneous coefficient degree
zero is zero. These statements hold over arbitrary R and arbitrary I,
with independent coefficient-ring and variable universes.
-/

@[expose] public section

noncomputable section

universe u v

namespace KoszulComplex

variable (R : Type u) [CommRing R] {I : Type v} [LinearOrder I]

local notation "P" => MvPolynomial I R
local notation "K" n => (⋀[P]^n (I →₀ P))

/-- For a commutative ring R and linearly ordered I, put
P = MvPolynomial I R. The P-basis of ⋀_P^n(I →₀ P) is indexed by
n-element subsets s of I; its vector is the wedge of the basis
elements e_i = Finsupp.single i 1 for i ∈ s, in increasing order. -/
def polynomialExteriorBasis (n : ℕ) : Module.Basis (Set.powersetCard I n) P (K n) :=
  (Finsupp.basisSingleOne (R := P) : Module.Basis I P (I →₀ P)).exteriorPower n

/-- For a commutative ring R and linearly ordered I, the
additive map π_(n,d) on ⋀_P^n(I →₀ P) replaces every polynomial
coefficient in the ordered exterior basis by its degree-d homogeneous
component, with P = MvPolynomial I R.
The polynomial coefficient degree is separate from exterior degree n. -/
def polynomialHomogeneousPart (n d : ℕ) : (K n) →+ (K n) :=
  (polynomialExteriorBasis R n).repr.symm.toAddMonoidHom.comp
    ((Finsupp.mapRange.addMonoidHom
      (MvPolynomial.homogeneousComponent (R := R) (σ := I) d).toAddMonoidHom).comp
      (polynomialExteriorBasis R n).repr.toAddMonoidHom)

theorem polynomialHomogeneousPart_repr (n d : ℕ) (z : K n)
    (s : Set.powersetCard I n) :
    (polynomialExteriorBasis R n).repr (polynomialHomogeneousPart R n d z) s =
      MvPolynomial.homogeneousComponent d ((polynomialExteriorBasis R n).repr z s) := by
  change (polynomialExteriorBasis R n).repr
    ((polynomialExteriorBasis R n).repr.symm
      (Finsupp.mapRange (MvPolynomial.homogeneousComponent d)
        (map_zero (MvPolynomial.homogeneousComponent d))
        ((polynomialExteriorBasis R n).repr z))) s = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- For a commutative ring R and linearly ordered I, an element
z ∈ ⋀_P^n(I →₀ P) is polynomial-homogeneous of degree d if every
coefficient in its ordered exterior basis is homogeneous of degree d
in P = MvPolynomial I R. The zero polynomial is permitted as a
coefficient. -/
def IsPolynomialHomogeneous (n d : ℕ) (z : K n) : Prop :=
  ∀ s : Set.powersetCard I n, ((polynomialExteriorBasis R n).repr z s).IsHomogeneous d

theorem polynomialHomogeneousPart_isHomogeneous (n d : ℕ) (z : K n) :
    IsPolynomialHomogeneous R n d (polynomialHomogeneousPart R n d z) := by
  intro s
  rw [polynomialHomogeneousPart_repr]
  exact MvPolynomial.homogeneousComponent_isHomogeneous d _

theorem polynomialHomogeneousPart_eq_self (n d : ℕ) (z : K n)
    (hz : IsPolynomialHomogeneous R n d z) : polynomialHomogeneousPart R n d z = z := by
  apply (polynomialExteriorBasis R n).repr.injective
  apply Finsupp.ext
  intro s
  rw [polynomialHomogeneousPart_repr]
  exact MvPolynomial.homogeneousComponent_eq_self (hz s)

theorem polynomialHomogeneousPart_smul_basis (n d : ℕ) (p : P)
    (s : Set.powersetCard I n) :
    polynomialHomogeneousPart R n d (p • polynomialExteriorBasis R n s) =
      (MvPolynomial.homogeneousComponent d p) • polynomialExteriorBasis R n s := by
  classical
  apply (polynomialExteriorBasis R n).repr.injective
  apply Finsupp.ext
  intro t
  rw [polynomialHomogeneousPart_repr]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
    smul_eq_mul, Finsupp.single_apply]
  by_cases h : s = t
  · simp only [h, ↓reduceIte, mul_one]
  · simp only [h, Ne.symm h, ↓reduceIte, mul_zero, map_zero]

private theorem polynomialExteriorBasis_orderEmbedding (n : ℕ) (f : Fin n ↪o I) :
    polynomialExteriorBasis R n (Set.powersetCard.ofFinEmbEquiv f) =
      exteriorPower.ιMulti P n (fun j => Finsupp.single (f j) 1) := by
  rw [polynomialExteriorBasis, exteriorPower.basis_apply, exteriorPower.ιMulti_family]
  apply congrArg (exteriorPower.ιMulti P n)
  funext j
  simp only [Equiv.symm_apply_apply, Function.comp_apply, Finsupp.coe_basisSingleOne]

theorem polynomialHomogeneousPart_smul_orderEmbedding (n d : ℕ) (p : P)
    (f : Fin n ↪o I) :
    polynomialHomogeneousPart R n d
        (p • exteriorPower.ιMulti P n (fun j => Finsupp.single (f j) 1)) =
      (MvPolynomial.homogeneousComponent d p) •
        exteriorPower.ιMulti P n (fun j => Finsupp.single (f j) 1) := by
  simpa only [polynomialExteriorBasis_orderEmbedding R n f] using
    polynomialHomogeneousPart_smul_basis R n d p (Set.powersetCard.ofFinEmbEquiv f)

theorem polynomialHomogeneousPart_neg_one_pow_smul (n d i : ℕ) (z : K n) :
    polynomialHomogeneousPart R n d (((-1 : P) ^ i) • z) =
      ((-1 : P) ^ i) • polynomialHomogeneousPart R n d z := by
  induction i generalizing z with
  | zero => simp only [pow_zero, one_smul]
  | succ i ih =>
      simp only [pow_succ, mul_smul, neg_one_smul]
      rw [ih, map_neg]

/-- For a commutative ring R, linearly ordered I, an
(n+1)-element subset s with increasing enumeration s₀,…,sₙ and
p ∈ P = MvPolynomial I R, the Koszul differential sends
p e_s to ∑_(i=0)^n (−1)^i p X_(s_i) e_(s ∖ {s_i}).
Each remaining wedge is ordered increasingly. -/
theorem polynomialDifferential_smul_basis (n : ℕ) (p : P)
    (s : Set.powersetCard I (n + 1)) :
    differential P (I →₀ P) (finsuppFunctional P MvPolynomial.X) n
        (p • polynomialExteriorBasis R (n + 1) s) =
      ∑ i : Fin (n + 1), (-1 : P) ^ i.val •
        ((p * MvPolynomial.X (Set.powersetCard.ofFinEmbEquiv.symm s i)) •
          exteriorPower.ιMulti P n
            (fun q => Finsupp.single
              (Set.powersetCard.ofFinEmbEquiv.symm s (i.succAbove q)) 1)) := by
  rw [map_smul, polynomialExteriorBasis, exteriorPower.basis_apply, exteriorPower.ιMulti_family]
  change p • differential P (I →₀ P) (finsuppFunctional P MvPolynomial.X) n
      (exteriorPower.ιMulti P (n + 1)
        (fun j => Finsupp.single (Set.powersetCard.ofFinEmbEquiv.symm s j) 1)) = _
  rw [differential_apply_ιMulti]
  simp only [finsuppFunctional, Finsupp.linearCombination_single, one_smul,
    Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_left_comm p ((-1 : P) ^ i.val)]
  rfl

/-- For a commutative ring R and linearly ordered I, let
π_(n,d) project the polynomial coefficients in exterior degree n.
Then π_(n,d+1)(∂_n z) = ∂_n(π_(n+1,d) z) for every
z ∈ ⋀_P^(n+1)(I →₀ P), n,d ≥ 0. The differential multiplies
a coefficient by one variable in each signed deletion term. -/
theorem polynomialHomogeneousPart_differential (n d : ℕ) (z : K (n + 1)) :
    polynomialHomogeneousPart R n (d + 1)
        (differential P (I →₀ P) (finsuppFunctional P MvPolynomial.X) n z) =
      differential P (I →₀ P) (finsuppFunctional P MvPolynomial.X) n
        (polynomialHomogeneousPart R (n + 1) d z) := by
  classical
  have hb (s : Set.powersetCard I (n + 1)) (p : P) :
      polynomialHomogeneousPart R n (d + 1)
          (differential P (I →₀ P) (finsuppFunctional P MvPolynomial.X) n
            (p • polynomialExteriorBasis R (n + 1) s)) =
        differential P (I →₀ P) (finsuppFunctional P MvPolynomial.X) n
          (polynomialHomogeneousPart R (n + 1) d
            (p • polynomialExteriorBasis R (n + 1) s)) := by
    rw [polynomialDifferential_smul_basis, map_sum,
      polynomialHomogeneousPart_smul_basis, polynomialDifferential_smul_basis]
    apply Finset.sum_congr rfl
    intro i hi
    rw [polynomialHomogeneousPart_neg_one_pow_smul]
    apply congrArg (fun q : K n => ((-1 : P) ^ i.val) • q)
    let f : Fin n ↪o I := (Fin.succAboveOrderEmb i).trans
      (Set.powersetCard.ofFinEmbEquiv.symm s)
    change polynomialHomogeneousPart R n (d + 1)
        ((p * MvPolynomial.X (Set.powersetCard.ofFinEmbEquiv.symm s i)) •
          exteriorPower.ιMulti P n (fun q => Finsupp.single (f q) 1)) = _
    rw [polynomialHomogeneousPart_smul_orderEmbedding, MvPolynomial.homogeneousComponent_mul_X]
    rfl
  rw [← (polynomialExteriorBasis R (n + 1)).linearCombination_repr z]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  exact hb s _

/-- For a commutative ring R and linearly ordered I, the
degree-zero polynomial-coefficient projection of ∂_n z is zero
for every z ∈ ⋀_P^(n+1)(I →₀ P), with P = MvPolynomial I R.
This is an identity in exterior degree n. -/
theorem polynomialHomogeneousPart_zero_differential (n : ℕ) (z : K (n + 1)) :
    polynomialHomogeneousPart R n 0
      (differential P (I →₀ P) (finsuppFunctional P MvPolynomial.X) n z) = 0 := by
  classical
  have hb (s : Set.powersetCard I (n + 1)) (p : P) :
      polynomialHomogeneousPart R n 0
        (differential P (I →₀ P) (finsuppFunctional P MvPolynomial.X) n
          (p • polynomialExteriorBasis R (n + 1) s)) = 0 := by
    rw [polynomialDifferential_smul_basis, map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [polynomialHomogeneousPart_neg_one_pow_smul]
    let f : Fin n ↪o I := (Fin.succAboveOrderEmb i).trans
      (Set.powersetCard.ofFinEmbEquiv.symm s)
    change ((-1 : P) ^ i.val) • polynomialHomogeneousPart R n 0
        ((p * MvPolynomial.X (Set.powersetCard.ofFinEmbEquiv.symm s i)) •
          exteriorPower.ιMulti P n (fun q => Finsupp.single (f q) 1)) = 0
    rw [polynomialHomogeneousPart_smul_orderEmbedding,
      MvPolynomial.homogeneousComponent_zero_mul_X, zero_smul, smul_zero]
  rw [← (polynomialExteriorBasis R (n + 1)).linearCombination_repr z]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  exact Finset.sum_eq_zero (fun s hs => hb s _)

/-- For a commutative ring R and linearly ordered I, let
z ∈ ⋀_P^(k+1)(I →₀ P) be a Koszul cycle whose exterior-basis
coefficients are homogeneous of degree d+1. There exists
w ∈ ⋀_P^(k+2)(I →₀ P) with homogeneous coefficient degree d
and ∂_(k+1)(w) = z, for k,d ≥ 0 and arbitrary I. -/
theorem polynomialVariables_homogeneous_exact_cycles (k d : ℕ) (z : K (k + 1))
    (hz : differential P (I →₀ P) (finsuppFunctional P MvPolynomial.X) k z = 0)
    (hhom : IsPolynomialHomogeneous R (k + 1) (d + 1) z) :
    ∃ w : K (k + 2), IsPolynomialHomogeneous R (k + 2) d w ∧
      differential P (I →₀ P) (finsuppFunctional P MvPolynomial.X) (k + 1) w = z := by
  obtain ⟨w, hw⟩ := polynomialVariables_exact_cycles R k z hz
  refine ⟨polynomialHomogeneousPart R (k + 2) d w,
    polynomialHomogeneousPart_isHomogeneous R (k + 2) d w, ?_⟩
  rw [← polynomialHomogeneousPart_differential R (k + 1) d w,
    hw, polynomialHomogeneousPart_eq_self R (k + 1) (d + 1) z hhom]

/-- For a commutative ring R and linearly ordered I, a Koszul
cycle z ∈ ⋀_P^(k+1)(I →₀ P) whose exterior-basis coefficients
are homogeneous of polynomial degree zero must satisfy z = 0.
Here k ≥ 0, P = MvPolynomial I R and I is arbitrary. -/
theorem polynomialVariables_homogeneous_zero_cycle (k : ℕ) (z : K (k + 1))
    (hz : differential P (I →₀ P) (finsuppFunctional P MvPolynomial.X) k z = 0)
    (hhom : IsPolynomialHomogeneous R (k + 1) 0 z) : z = 0 := by
  obtain ⟨w, hw⟩ := polynomialVariables_exact_cycles R k z hz
  have h := polynomialHomogeneousPart_zero_differential R (k + 1) w
  rw [hw, polynomialHomogeneousPart_eq_self R (k + 1) 0 z hhom] at h
  exact h

end KoszulComplex
