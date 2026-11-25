/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.KoszulComplex.Polynomial.Homogeneous
public import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# Original polynomial Koszul chains in exterior-basis coefficient coordinates

The native polynomial-linear differential is transported through its actual
exterior basis, then restricted to the original coefficient ring. These
coordinates are finitely supported polynomial coefficient families. Their
homogeneous projection and total-degree filtration expose the already
constructed homogeneous Koszul boundaries without changing the complex.
-/

@[expose] public section

noncomputable section

universe u v

namespace KoszulComplex

variable (R : Type u) [CommRing R] {I : Type v} [LinearOrder I]

local notation "P" => MvPolynomial I R
local notation:max "K" n:max => (⋀[P]^n (I →₀ P))
local notation:max "F" n:max => (Set.powersetCard I n →₀ P)

/-- The original polynomial Koszul differential in its actual exterior-basis coordinates. -/
def polynomialCoefficientDifferentialP (n : ℕ) : F (n + 1) →ₗ[P] F n :=
  (polynomialExteriorBasis R n).repr.toLinearMap.comp
    ((differential P (I →₀ P) (finsuppFunctional P MvPolynomial.X) n).comp
      (polynomialExteriorBasis R (n + 1)).repr.symm.toLinearMap)

/-- Restrict only the scalar ring of the original coordinate differential. -/
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

/-- Coefficientwise homogeneous projection over the original ground ring. -/
def polynomialCoefficientHomogeneousPart (n d : ℕ) : F n →ₗ[R] F n :=
  Finsupp.mapRange.linearMap (MvPolynomial.homogeneousComponent d)

omit [LinearOrder I] in
@[simp]
theorem polynomialCoefficientHomogeneousPart_apply (n d : ℕ) (c : F n)
    (s : Set.powersetCard I n) :
    polynomialCoefficientHomogeneousPart R n d c s = MvPolynomial.homogeneousComponent d (c s) := rfl

theorem polynomialCoefficientHomogeneousPart_repr (n d : ℕ) (z : K n) :
    polynomialCoefficientHomogeneousPart R n d ((polynomialExteriorBasis R n).repr z) =
      (polynomialExteriorBasis R n).repr (polynomialHomogeneousPart R n d z) := by
  ext s
  rw [polynomialCoefficientHomogeneousPart_apply, polynomialHomogeneousPart_repr]

/-- The actual coordinate differential raises coefficient degree by one. -/
theorem polynomialCoefficientHomogeneousPart_differential (n d : ℕ) (c : F (n + 1)) :
    polynomialCoefficientHomogeneousPart R n (d + 1) (polynomialCoefficientDifferential R n c) =
      polynomialCoefficientDifferential R n
        (polynomialCoefficientHomogeneousPart R (n + 1) d c) := by
  let z := (polynomialExteriorBasis R (n + 1)).repr.symm c
  have h := congrArg (polynomialExteriorBasis R n).repr
    (polynomialHomogeneousPart_differential R n d z)
  simpa only [← polynomialCoefficientHomogeneousPart_repr,
    ← polynomialCoefficientDifferential_repr, z, LinearEquiv.apply_symm_apply] using h

/-- Polynomial coefficients do not acquire a constant term under the original differential. -/
theorem polynomialCoefficientHomogeneousPart_zero_differential (n : ℕ) (c : F (n + 1)) :
    polynomialCoefficientHomogeneousPart R n 0 (polynomialCoefficientDifferential R n c) = 0 := by
  let z := (polynomialExteriorBasis R (n + 1)).repr.symm c
  have h := congrArg (polynomialExteriorBasis R n).repr
    (polynomialHomogeneousPart_zero_differential R n z)
  simpa only [← polynomialCoefficientHomogeneousPart_repr,
    ← polynomialCoefficientDifferential_repr, z, LinearEquiv.apply_symm_apply, map_zero] using h

/-- Canonical ordered deletion index in an exterior-coordinate family. -/
def polynomialEraseIndex (n : ℕ) (s : Set.powersetCard I (n + 1))
    (i : Fin (n + 1)) : Set.powersetCard I n :=
  Set.powersetCard.ofFinEmbEquiv
    ((Fin.succAboveOrderEmb i).trans (Set.powersetCard.ofFinEmbEquiv.symm s))

/-- The native variable exterior basis at the canonical deletion index. -/
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
/-- Integral signs agree under the original polynomial scalar restriction. -/
theorem polynomialSign_smul_eq (n i : ℕ) (c : F n) :
    ((-1 : P) ^ i) • c = ((-1 : R) ^ i) • c := by
  induction i generalizing c with
  | zero => simp only [pow_zero, one_smul]
  | succ i ih =>
      simp only [pow_succ, mul_smul, neg_one_smul]
      rw [ih]

/-- Actual signed variable deletion in original coefficient coordinates. -/
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

/-- Total coefficient degree plus the actual exterior degree. Stages below
exterior degree are zero, rather than using truncated subtraction there. -/
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

/-- Homogeneous coefficient families inherit the actual arbitrary-variable
Koszul boundary construction through the original exterior basis. -/
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
