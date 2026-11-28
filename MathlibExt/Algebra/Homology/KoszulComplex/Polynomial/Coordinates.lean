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

public import MathlibExt.Algebra.Homology.KoszulComplex.Polynomial.Homogeneous
public import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# Signed polynomial Koszul boundaries in exterior coefficient coordinates

Let R be a commutative ring, I a linearly ordered variable type and
P = MvPolynomial I R. The exterior basis of
K_n = ⋀_P^n(I →₀ P) is indexed by n-element subsets s of I, listed
in increasing order. It identifies K_n with the finitely supported
coefficient families F_n = (Set.powersetCard I n) →₀ P.

In these coordinates the differential is
∂(p δ_s) = ∑_(i=0)^n (−1)^i p X_(s_i) δ_(s ∖ {s_i})
for |s| = n+1. This is P-linear, and restricting scalars gives the
same function as an R-linear map. Coefficientwise homogeneous projection
π_d satisfies π_(d+1)∂ = ∂π_d and π_0∂ = 0.

The total-degree filtration in exterior degree n is zero for p < n;
for p ≥ n it consists of families whose polynomial coefficients have
degree at most p−n. A cycle of coefficient degree d+1 in positive
exterior degree has a boundary of coefficient degree d. The variable
type I is arbitrary, and the worlds of R and I are independent.
-/

@[expose] public section

noncomputable section

universe u v

namespace KoszulComplex

variable (R : Type u) [CommRing R] {I : Type v} [LinearOrder I]

local notation "P" => MvPolynomial I R
local notation:max "K" n:max => (⋀[P]^n (I →₀ P))
local notation:max "F" n:max => (Set.powersetCard I n →₀ P)

/-- For a commutative ring R and linearly ordered I, let
P = MvPolynomial I R and F_n = (Set.powersetCard I n) →₀ P.
The coordinate differential F_(n+1) →ₗ[P] F_n is obtained by
converting coefficients to the exterior basis, taking the Koszul
differential x(e_i) = X_i, and converting back. -/
def polynomialCoefficientDifferentialP (n : ℕ) : F (n + 1) →ₗ[P] F n :=
  (polynomialExteriorBasis R n).repr.toLinearMap.comp
    ((differential P (I →₀ P) (finsuppFunctional P MvPolynomial.X) n).comp
      (polynomialExteriorBasis R (n + 1)).repr.symm.toLinearMap)

/-- For a commutative ring R and linearly ordered I, the map
F_(n+1) →ₗ[R] F_n is the restriction of the polynomial-linear
Koszul coordinate differential along R → P = MvPolynomial I R.
Its values and deletion signs are unchanged by this scalar restriction. -/
def polynomialCoefficientDifferential (n : ℕ) : F (n + 1) →ₗ[R] F n :=
  (polynomialCoefficientDifferentialP R n).restrictScalars R

theorem polynomialCoefficientDifferential_apply (n : ℕ) (c : F (n + 1)) :
    polynomialCoefficientDifferential R n c = (polynomialExteriorBasis R n).repr
      (differential P (I →₀ P) (finsuppFunctional P MvPolynomial.X) n
        ((polynomialExteriorBasis R (n + 1)).repr.symm c)) := rfl

theorem polynomialCoefficientDifferential_repr (n : ℕ) (z : K (n + 1)) :
    polynomialCoefficientDifferential R n ((polynomialExteriorBasis R (n + 1)).repr z) =
      (polynomialExteriorBasis R n).repr
        (differential P (I →₀ P) (finsuppFunctional P MvPolynomial.X) n z) := by
  rw [polynomialCoefficientDifferential_apply, LinearEquiv.symm_apply_apply]

/-- For a commutative ring R and arbitrary I, the R-linear map
π_d on F_n = (Set.powersetCard I n) →₀ MvPolynomial I R
takes the degree-d homogeneous component of every coefficient
polynomial. It preserves the finitely supported family structure. -/
def polynomialCoefficientHomogeneousPart (n d : ℕ) : F n →ₗ[R] F n :=
  Finsupp.mapRange.linearMap (MvPolynomial.homogeneousComponent d)

omit [LinearOrder I] in
@[simp]
theorem polynomialCoefficientHomogeneousPart_apply (n d : ℕ) (c : F n)
    (s : Set.powersetCard I n) :
    polynomialCoefficientHomogeneousPart R n d c s = MvPolynomial.homogeneousComponent d (c s) :=
      rfl

theorem polynomialCoefficientHomogeneousPart_repr (n d : ℕ) (z : K n) :
    polynomialCoefficientHomogeneousPart R n d ((polynomialExteriorBasis R n).repr z) =
      (polynomialExteriorBasis R n).repr (polynomialHomogeneousPart R n d z) := by
  ext s
  rw [polynomialCoefficientHomogeneousPart_apply, polynomialHomogeneousPart_repr]

/-- For a commutative ring R and linearly ordered I, the
homogeneous coefficient projections π_d and the Koszul coordinate
differential satisfy π_(d+1)∂_n(c) = ∂_n(π_d(c)) for
c ∈ F_(n+1), n,d ≥ 0. Exterior degree drops by one while
polynomial coefficient degree increases by one. -/
theorem polynomialCoefficientHomogeneousPart_differential (n d : ℕ) (c : F (n + 1)) :
    polynomialCoefficientHomogeneousPart R n (d + 1) (polynomialCoefficientDifferential R n c) =
      polynomialCoefficientDifferential R n
        (polynomialCoefficientHomogeneousPart R (n + 1) d c) := by
  let z := (polynomialExteriorBasis R (n + 1)).repr.symm c
  have h := congrArg (polynomialExteriorBasis R n).repr
    (polynomialHomogeneousPart_differential R n d z)
  simpa only [← polynomialCoefficientHomogeneousPart_repr,
    ← polynomialCoefficientDifferential_repr, z, LinearEquiv.apply_symm_apply] using h

/-- For a commutative ring R and linearly ordered I, the
degree-zero homogeneous coefficient projection of ∂_n(c) is zero
for every c ∈ F_(n+1). Each deletion term multiplies its coefficient
by one variable X_i. -/
theorem polynomialCoefficientHomogeneousPart_zero_differential (n : ℕ) (c : F (n + 1)) :
    polynomialCoefficientHomogeneousPart R n 0 (polynomialCoefficientDifferential R n c) = 0 := by
  let z := (polynomialExteriorBasis R (n + 1)).repr.symm c
  have h := congrArg (polynomialExteriorBasis R n).repr
    (polynomialHomogeneousPart_zero_differential R n z)
  simpa only [← polynomialCoefficientHomogeneousPart_repr,
    ← polynomialCoefficientDifferential_repr, z, LinearEquiv.apply_symm_apply, map_zero] using h

/-- For a linearly ordered type I, an (n+1)-element subset s
and i ∈ Fin(n+1), the deletion index is the n-element subset
s ∖ {s_i}, where s_i is the ith member in increasing order.
The remaining elements retain their increasing order. -/
def polynomialEraseIndex (n : ℕ) (s : Set.powersetCard I (n + 1))
    (i : Fin (n + 1)) : Set.powersetCard I n :=
  Set.powersetCard.ofFinEmbEquiv
    ((Fin.succAboveOrderEmb i).trans (Set.powersetCard.ofFinEmbEquiv.symm s))

/-- For a commutative ring R and linearly ordered I, the
degree-n exterior basis vector indexed by s ∖ {s_i} is the ordered
wedge of e_(s_j) for j ≠ i, with P = MvPolynomial I R and
e_a = Finsupp.single a 1 in I →₀ P. -/
theorem polynomialExteriorBasis_erased (n : ℕ)
    (s : Set.powersetCard I (n + 1)) (i : Fin (n + 1)) :
    polynomialExteriorBasis R n (polynomialEraseIndex n s i) =
      exteriorPower.ιMulti P n
        (fun q => Finsupp.single
          (Set.powersetCard.ofFinEmbEquiv.symm s (i.succAbove q)) 1) := by
  rw [polynomialExteriorBasis, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family, polynomialEraseIndex, Equiv.symm_apply_apply]
  apply congrArg (exteriorPower.ιMulti P n)
  funext q
  rw [Finsupp.coe_basisSingleOne]
  rfl

omit [LinearOrder I] in
/-- For a commutative ring R, arbitrary I and a coefficient
family c ∈ F_n, multiplication by (−1)^i in
P = MvPolynomial I R agrees with multiplication by (−1)^i in R
after restriction of scalars, for every i ≥ 0. -/
theorem polynomialSign_smul_eq (n i : ℕ) (c : F n) :
    ((-1 : P) ^ i) • c = ((-1 : R) ^ i) • c := by
  induction i generalizing c with
  | zero => simp only [pow_zero, one_smul]
  | succ i ih =>
      simp only [pow_succ, mul_smul, neg_one_smul]
      rw [ih]

/-- For a commutative ring R, linearly ordered I, an
(n+1)-element subset s with increasing enumeration s₀,…,sₙ and
p ∈ P = MvPolynomial I R, the R-linear coordinate differential
satisfies ∂_n(p δ_s) =
∑_(i=0)^n (−1)^i δ_(s ∖ {s_i})(p X_(s_i)).
The remaining exterior indices keep their order. -/
theorem polynomialCoefficientDifferential_single (n : ℕ)
    (s : Set.powersetCard I (n + 1)) (p : P) :
    polynomialCoefficientDifferential R n (Finsupp.single s p) =
      ∑ i : Fin (n + 1), (-1 : R) ^ i.val •
        Finsupp.single (polynomialEraseIndex n s i)
          (p * MvPolynomial.X (Set.powersetCard.ofFinEmbEquiv.symm s i)) := by
  classical
  rw [polynomialCoefficientDifferential_apply]
  have hpre : (polynomialExteriorBasis R (n + 1)).repr.symm (Finsupp.single s p) =
      p • polynomialExteriorBasis R (n + 1) s := by
    apply (polynomialExteriorBasis R (n + 1)).repr.injective
    rw [LinearEquiv.apply_symm_apply, map_smul, Module.Basis.repr_self]
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hpre, polynomialDifferential_smul_basis, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, map_smul, ← polynomialExteriorBasis_erased,
    Module.Basis.repr_self]
  have hcoeff :
      (p * MvPolynomial.X (Set.powersetCard.ofFinEmbEquiv.symm s i)) •
          Finsupp.single (polynomialEraseIndex n s i) (1 : P) =
        Finsupp.single (polynomialEraseIndex n s i)
          (p * MvPolynomial.X (Set.powersetCard.ofFinEmbEquiv.symm s i)) := by
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hcoeff]
  exact polynomialSign_smul_eq R n i.val _

/-- For a commutative ring R and arbitrary I, the stage p of the
coefficient filtration on F_n is zero if p < n. For p ≥ n it is
the R-submodule of families c such that every c_s has polynomial
degree at most p−n. Thus p bounds coefficient degree plus the
exterior degree n. -/
def polynomialCoefficientFiltration (n p : ℕ) : Submodule R (F n) :=
  if n ≤ p then
    Finsupp.submodule (fun _ : Set.powersetCard I n =>
      MvPolynomial.restrictTotalDegree I R (p - n))
  else ⊥

omit [LinearOrder I] in
theorem polynomialCoefficientFiltration_eq_bot_of_lt (n p : ℕ) (hp : p < n) :
    polynomialCoefficientFiltration (I := I) R n p = ⊥ := by
  rw [polynomialCoefficientFiltration, if_neg (not_le_of_gt hp)]

omit [LinearOrder I] in
theorem polynomialCoefficientFiltration_mem_iff (n p : ℕ) (hp : n ≤ p) (c : F n) :
    c ∈ polynomialCoefficientFiltration R n p ↔
      ∀ s : Set.powersetCard I n, c s ∈ MvPolynomial.restrictTotalDegree I R (p - n) := by
  rw [polynomialCoefficientFiltration, if_pos hp, Finsupp.mem_submodule_iff]

omit [LinearOrder I] in
theorem polynomialCoefficientFiltration_mono (n : ℕ) :
    Monotone (polynomialCoefficientFiltration (R := R) (I := I) n) := by
  intro p q hpq c hc
  by_cases hnp : n ≤ p
  · have hcoeff := (polynomialCoefficientFiltration_mem_iff R n p hnp c).mp hc
    rw [polynomialCoefficientFiltration_mem_iff R n q (hnp.trans hpq)]
    intro s
    apply MvPolynomial.restrictSupport_mono (R := R)
      (show {e : I →₀ ℕ | e.degree ≤ p - n} ⊆ {e | e.degree ≤ q - n} from
        fun e he => by
          change e.degree ≤ p - n at he
          exact he.trans (Nat.sub_le_sub_right hpq n))
    exact hcoeff s
  · have hzero : c = 0 := by
      rw [polynomialCoefficientFiltration, if_neg hnp, Submodule.mem_bot] at hc
      exact hc
    rw [hzero]
    exact (polynomialCoefficientFiltration R n q).zero_mem

theorem polynomialCoefficientFiltration_single (n p : ℕ) (hp : n ≤ p)
    (s : Set.powersetCard I n) (a : P)
    (ha : a ∈ MvPolynomial.restrictTotalDegree I R (p - n)) :
    Finsupp.single s a ∈ polynomialCoefficientFiltration R n p := by
  classical
  rw [polynomialCoefficientFiltration_mem_iff R n p hp]
  intro t
  by_cases h : t = s
  · subst t
    rw [Finsupp.single_eq_same]
    exact ha
  · rw [Finsupp.single_eq_of_ne h]
    exact (MvPolynomial.restrictTotalDegree I R (p - n)).zero_mem

omit [LinearOrder I] in
theorem polynomialCoefficientHomogeneousPart_mem_filtration (n d : ℕ) (c : F n) :
    polynomialCoefficientHomogeneousPart R n d c ∈ polynomialCoefficientFiltration R n (d + n) := by
  rw [polynomialCoefficientFiltration_mem_iff R n (d + n) (by omega)]
  intro s
  rw [polynomialCoefficientHomogeneousPart_apply, Nat.add_sub_cancel]
  exact MvPolynomial.homogeneousComponent_mem_restrictTotalDegree d (c s)

omit [LinearOrder I] in
theorem polynomialCoefficientHomogeneousPart_isHomogeneous (n d : ℕ) (c : F n) :
    ∀ s : Set.powersetCard I n,
      (polynomialCoefficientHomogeneousPart R n d c s).IsHomogeneous d := by
  intro s
  rw [polynomialCoefficientHomogeneousPart_apply]
  exact MvPolynomial.homogeneousComponent_isHomogeneous d (c s)

omit [LinearOrder I] in
theorem polynomialCoefficient_mem_filtration_of_isHomogeneous (n d : ℕ) (c : F n)
    (hc : ∀ s, (c s).IsHomogeneous d) :
    c ∈ polynomialCoefficientFiltration R n (d + n) := by
  rw [polynomialCoefficientFiltration_mem_iff R n (d + n) (by omega)]
  intro s
  rw [Nat.add_sub_cancel]
  exact MvPolynomial.IsHomogeneous.mem_restrictTotalDegree (hc s)

omit [LinearOrder I] in
private theorem polynomialConstantPart_eq_self (p : P)
    (hp : p ∈ MvPolynomial.restrictTotalDegree I R 0) :
    MvPolynomial.homogeneousComponent 0 p = p := by
  classical
  apply MvPolynomial.ext
  intro e
  rw [MvPolynomial.coeff_homogeneousComponent]
  by_cases he : e.degree = 0
  · rw [if_pos he]
  · rw [if_neg he]
    have hzero : p.coeff e = 0 := by
      by_contra hcoeff
      have hs : e ∈ p.support := MvPolynomial.mem_support_iff.mpr hcoeff
      change p ∈ MvPolynomial.restrictSupport R {e : I →₀ ℕ | e.degree ≤ 0} at hp
      rw [MvPolynomial.mem_restrictSupport_iff] at hp
      have hdegree : e.degree ≤ 0 := hp hs
      exact he (Nat.le_zero.mp hdegree)
    exact hzero.symm

omit [LinearOrder I] in
theorem polynomialCoefficientHomogeneousPart_zero_eq_self (n : ℕ) {c : F n}
    (hc : c ∈ polynomialCoefficientFiltration R n n) :
    polynomialCoefficientHomogeneousPart R n 0 c = c := by
  have hcoeff := (polynomialCoefficientFiltration_mem_iff R n n le_rfl c).mp hc
  apply Finsupp.ext
  intro s
  rw [polynomialCoefficientHomogeneousPart_apply]
  apply polynomialConstantPart_eq_self R (c s)
  simpa only [Nat.sub_self] using hcoeff s

omit [LinearOrder I] in
theorem polynomialCoefficientHomogeneousPart_zero_of_filtration (n p d : ℕ)
    (hp : p < d + n) {c : F n} (hc : c ∈ polynomialCoefficientFiltration R n p) :
    polynomialCoefficientHomogeneousPart R n d c = 0 := by
  by_cases hnp : n ≤ p
  · have hcoeff := (polynomialCoefficientFiltration_mem_iff R n p hnp c).mp hc
    apply Finsupp.ext
    intro s
    rw [polynomialCoefficientHomogeneousPart_apply, Finsupp.zero_apply]
    apply MvPolynomial.homogeneousComponent_eq_zero' d (c s)
    intro e he
    have hdegree : e.degree ≤ p - n :=
      by
        have hsupport := hcoeff s
        change c s ∈ MvPolynomial.restrictSupport R {e : I →₀ ℕ | e.degree ≤ p - n} at hsupport
        rw [MvPolynomial.mem_restrictSupport_iff] at hsupport
        exact hsupport he
    intro heq
    rw [heq] at hdegree
    omega
  · have hc0 : c = 0 := by
      rw [polynomialCoefficientFiltration, if_neg hnp, Submodule.mem_bot] at hc
      exact hc
    rw [hc0, map_zero]

omit [LinearOrder I] in
theorem polynomialCoefficient_sub_highest_mem_lower (n d : ℕ) {c : F n}
    (hc : c ∈ polynomialCoefficientFiltration R n ((d + 1) + n)) :
    c - polynomialCoefficientHomogeneousPart R n (d + 1) c ∈
      polynomialCoefficientFiltration R n (d + n) := by
  have hcoeff := (polynomialCoefficientFiltration_mem_iff R n ((d + 1) + n) (by omega) c).mp hc
  rw [polynomialCoefficientFiltration_mem_iff R n (d + n) (by omega)]
  intro s
  rw [Finsupp.sub_apply, polynomialCoefficientHomogeneousPart_apply, Nat.add_sub_cancel]
  have hp : c s ∈ MvPolynomial.restrictTotalDegree I R (d + 1) := by
    simpa only [Nat.add_sub_cancel] using hcoeff s
  have hupper : c s - MvPolynomial.homogeneousComponent (d + 1) (c s) ∈
      MvPolynomial.restrictTotalDegree I R (d + 1) :=
    (MvPolynomial.restrictTotalDegree I R (d + 1)).sub_mem hp
      (MvPolynomial.homogeneousComponent_mem_restrictTotalDegree (d + 1) (c s))
  apply (MvPolynomial.mem_restrictTotalDegree_iff_highestComponent_zero d _ hupper).mpr
  rw [map_sub, MvPolynomial.homogeneousComponent_eq_self
    (MvPolynomial.homogeneousComponent_isHomogeneous (d + 1) (c s)), sub_self]

/-- For a commutative ring R and linearly ordered I, suppose
c ∈ F_(k+1) is a coordinate Koszul cycle and every coefficient of c
is homogeneous of degree d+1. Then there exists w ∈ F_(k+2)
whose coefficients are homogeneous of degree d and satisfy
∂_(k+1)(w) = c. Here k,d ≥ 0 and I is arbitrary. -/
theorem polynomialCoefficient_homogeneous_exact_cycles (k d : ℕ) (c : F (k + 1))
    (hc : polynomialCoefficientDifferential R k c = 0)
    (hhom : ∀ s, (c s).IsHomogeneous (d + 1)) :
    ∃ w : F (k + 2), (∀ s, (w s).IsHomogeneous d) ∧
      polynomialCoefficientDifferential R (k + 1) w = c := by
  let z : K (k + 1) := (polynomialExteriorBasis R (k + 1)).repr.symm c
  have hz : differential P (I →₀ P) (finsuppFunctional P MvPolynomial.X) k z = 0 := by
    apply (polynomialExteriorBasis R k).repr.injective
    rw [map_zero]
    exact hc
  have hhomz : IsPolynomialHomogeneous R (k + 1) (d + 1) z := by
    intro s
    simpa only [z, LinearEquiv.apply_symm_apply] using hhom s
  obtain ⟨w, hwHom, hw⟩ := polynomialVariables_homogeneous_exact_cycles R k d z hz hhomz
  refine ⟨(polynomialExteriorBasis R (k + 2)).repr w, hwHom, ?_⟩
  rw [polynomialCoefficientDifferential_repr, hw]
  exact (polynomialExteriorBasis R (k + 1)).repr.apply_symm_apply c

theorem polynomialCoefficient_homogeneous_zero_cycle (k : ℕ) (c : F (k + 1))
    (hc : polynomialCoefficientDifferential R k c = 0)
    (hhom : ∀ s, (c s).IsHomogeneous 0) : c = 0 := by
  let z : K (k + 1) := (polynomialExteriorBasis R (k + 1)).repr.symm c
  have hz : differential P (I →₀ P) (finsuppFunctional P MvPolynomial.X) k z = 0 := by
    apply (polynomialExteriorBasis R k).repr.injective
    rw [map_zero]
    exact hc
  have hhomz : IsPolynomialHomogeneous R (k + 1) 0 z := by
    intro s
    simpa only [z, LinearEquiv.apply_symm_apply] using hhom s
  have hzero := polynomialVariables_homogeneous_zero_cycle R k z hz hhomz
  have h := congrArg (polynomialExteriorBasis R (k + 1)).repr hzero
  simpa only [z, LinearEquiv.apply_symm_apply, map_zero] using h

end KoszulComplex
