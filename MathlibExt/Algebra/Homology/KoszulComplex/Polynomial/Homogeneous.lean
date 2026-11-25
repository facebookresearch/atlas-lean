/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.KoszulComplex.Polynomial
public import MathlibExt.RingTheory.MvPolynomial.HomogeneousVariable
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Homogeneous boundaries in the arbitrary-variable polynomial Koszul complex

Coefficientwise homogeneous projection is transported through the actual
exterior basis of the free polynomial coefficient module. The original
Koszul differential raises polynomial coefficient degree by one. Projecting
the already constructed arbitrary-variable boundary therefore gives an
actual boundary in the required homogeneous degree. Degree-zero cycles are
treated separately and vanish in positive exterior degree.
-/

@[expose] public section

noncomputable section

universe u v

namespace KoszulComplex

variable (R : Type u) [CommRing R] {I : Type v} [LinearOrder I]

local notation "P" => MvPolynomial I R
local notation "K" n => (⋀[P]^n (I →₀ P))

/-- The original exterior basis of the free module on all polynomial variables. -/
def polynomialExteriorBasis (n : ℕ) : Module.Basis (Set.powersetCard I n) P (K n) :=
  (Finsupp.basisSingleOne (R := P) : Module.Basis I P (I →₀ P)).exteriorPower n

/-- Project the actual polynomial coefficients of an exterior element to a
fixed homogeneous degree. The map is additive; no polynomial-linearity is claimed. -/
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

/-- Homogeneity of the literal polynomial coefficients in the exterior basis. -/
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

/-- Polynomial coefficient multiplication by variables is the original
Koszul differential on each scalar multiple of an exterior basis vector. -/
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

/-- The actual variable Koszul differential raises polynomial coefficient
degree by one and commutes with the corresponding homogeneous projections. -/
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

/-- No degree-zero polynomial coefficients occur in the image of the actual
variable Koszul differential. -/
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

/-- Every actual positive-exterior cycle of positive homogeneous coefficient
degree has a constructed boundary in the immediately preceding coefficient degree. -/
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

/-- A degree-zero polynomial cycle in positive exterior degree is zero. This
is the endpoint where a preceding negative coefficient degree has no terms. -/
theorem polynomialVariables_homogeneous_zero_cycle (k : ℕ) (z : K (k + 1))
    (hz : differential P (I →₀ P) (finsuppFunctional P MvPolynomial.X) k z = 0)
    (hhom : IsPolynomialHomogeneous R (k + 1) 0 z) : z = 0 := by
  obtain ⟨w, hw⟩ := polynomialVariables_exact_cycles R k z hz
  have h := polynomialHomogeneousPart_zero_differential R (k + 1) w
  rw [hw, polynomialHomogeneousPart_eq_self R (k + 1) 0 z hhom] at h
  exact h

end KoszulComplex
