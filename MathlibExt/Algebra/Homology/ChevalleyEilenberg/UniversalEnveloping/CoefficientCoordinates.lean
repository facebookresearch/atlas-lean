/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.UniversalEnveloping.FilteredDifferential
public import MathlibExt.Algebra.Lie.UniversalEnveloping.PBW.FilteredCoordinates
public import MathlibExt.Algebra.Homology.KoszulComplexPolynomialCoordinates
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Polynomial coordinates for enveloping Chevalley–Eilenberg terms

A basis of the Lie module, the tensor basis equivalence, and the PBW
coefficient map identify each exterior-first term with finitely supported
polynomial coefficients on exterior basis elements. In these coordinates,
the total filtration is the coefficient-degree bound plus exterior degree.
-/

@[expose] public section

noncomputable section

universe u v w

open scoped TensorProduct

namespace ChevalleyEilenberg

open UniversalEnvelopingAlgebra.PBW

variable (R : Type u) [CommRing R]
  (L : Type v) [LieRing L] [LieAlgebra R L]
  {I : Type w} [LinearOrder I]

local notation "P" => MvPolynomial I R
local notation "F" n => (Set.powersetCard I n →₀ P)

/-- Coordinate equivalence on the original exterior-first regular coefficient carrier. -/
def envelopingCoefficientCoordinates (b : Module.Basis I R L) (n : ℕ) :
    (⋀[R]^n L) ⊗[R] regularCoefficients R L ≃ₗ[R] F n := by
  classical
  exact (TensorProduct.comm R (⋀[R]^n L) (regularCoefficients R L)).trans
    ((TensorProduct.equivFinsuppOfBasisRight (M := regularCoefficients R L)
      (b.exteriorPower n)).trans (Finsupp.mapRange.linearEquiv (polynomialCoordinates b)))

theorem envelopingCoefficientCoordinates_tmul_apply (b : Module.Basis I R L) (n : ℕ)
    (x : ⋀[R]^n L) (u : regularCoefficients R L) (s : Set.powersetCard I n) :
    envelopingCoefficientCoordinates R L b n (x ⊗ₜ[R] u) s =
      (b.exteriorPower n).repr x s • polynomialCoordinates b u := by
  classical
  change (Finsupp.mapRange.linearEquiv (polynomialCoordinates b))
    (TensorProduct.equivFinsuppOfBasisRight (b.exteriorPower n)
      (TensorProduct.comm R (⋀[R]^n L) (regularCoefficients R L) (x ⊗ₜ[R] u))) s = _
  rw [TensorProduct.comm_tmul]
  change polynomialCoordinates b
    (TensorProduct.equivFinsuppOfBasisRight (b.exteriorPower n) (u ⊗ₜ[R] x) s) = _
  rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, map_smul]

theorem envelopingCoefficientCoordinates_basis_tmul (b : Module.Basis I R L) (n : ℕ)
    (s : Set.powersetCard I n) (u : regularCoefficients R L) :
    envelopingCoefficientCoordinates R L b n (b.exteriorPower n s ⊗ₜ[R] u) =
      Finsupp.single s (polynomialCoordinates b u) := by
  classical
  ext t
  rw [envelopingCoefficientCoordinates_tmul_apply, Module.Basis.repr_self]
  by_cases h : t = s
  · subst t
    simp only [Finsupp.single_eq_same, one_smul]
  · simp only [Finsupp.single_eq_of_ne h, zero_smul]

theorem envelopingCoefficientCoordinates_symm_single (b : Module.Basis I R L) (n : ℕ)
    (s : Set.powersetCard I n) (p : P) :
    (envelopingCoefficientCoordinates R L b n).symm (Finsupp.single s p) =
      b.exteriorPower n s ⊗ₜ[R] (polynomialCoordinates b).symm p := by
  apply (envelopingCoefficientCoordinates R L b n).injective
  rw [LinearEquiv.apply_symm_apply, envelopingCoefficientCoordinates_basis_tmul,
    LinearEquiv.apply_symm_apply]

omit [LinearOrder I] in
private theorem polynomialDegree_mono {p q : ℕ} (hpq : p ≤ q) :
    MvPolynomial.restrictTotalDegree I R p ≤ MvPolynomial.restrictTotalDegree I R q := by
  apply MvPolynomial.restrictSupport_mono
  intro e he
  exact he.trans hpq

/-- The original total CE filtration maps into its polynomial coefficient degree bound. -/
theorem envelopingCoefficientCoordinates_mem_filtration (b : Module.Basis I R L)
    (n p : ℕ) {z : (⋀[R]^n L) ⊗[R] regularCoefficients R L}
    (hz : z ∈ envelopingFiltration R L p n) :
    envelopingCoefficientCoordinates R L b n z ∈
      KoszulComplex.polynomialCoefficientFiltration R n p := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨q, v, u, hq, hu, rfl⟩ := hz
      rw [KoszulComplex.polynomialCoefficientFiltration_mem_iff R n p (by omega)]
      intro s
      rw [envelopingCoefficientCoordinates_tmul_apply]
      apply (MvPolynomial.restrictTotalDegree I R (p - n)).smul_mem
      exact polynomialDegree_mono R (show q ≤ p - n by omega)
        ((polynomialCoordinates_mem_degree_iff b q u).mpr hu)
  | zero =>
      rw [map_zero]
      exact (KoszulComplex.polynomialCoefficientFiltration R n p).zero_mem
  | add z w hz hw ihz ihw =>
      rw [map_add]
      exact (KoszulComplex.polynomialCoefficientFiltration R n p).add_mem ihz ihw
  | smul r z hz ih =>
      rw [map_smul]
      exact (KoszulComplex.polynomialCoefficientFiltration R n p).smul_mem r ih

/-- Polynomial coefficient bounds lift through the original coordinate
equivalence into the enveloping CE filtration. -/
theorem envelopingCoefficientCoordinates_symm_mem_filtration (b : Module.Basis I R L)
    (n p : ℕ) {c : F n}
    (hc : c ∈ KoszulComplex.polynomialCoefficientFiltration R n p) :
    (envelopingCoefficientCoordinates R L b n).symm c ∈ envelopingFiltration R L p n := by
  classical
  by_cases hnp : n ≤ p
  · have hcoeff := (KoszulComplex.polynomialCoefficientFiltration_mem_iff R n p hnp c).mp hc
    rw [← Finsupp.sum_single c]
    simp only [Finsupp.sum, map_sum]
    apply (envelopingFiltration R L p n).sum_mem
    intro s hs
    rw [envelopingCoefficientCoordinates_symm_single]
    apply tmul_mem_envelopingFiltration R L p n (p - n)
      (b.exteriorPower n s) ((polynomialCoordinates b).symm (c s)) (by omega)
    apply (polynomialCoordinates_mem_degree_iff b (p - n) _).mp
    simpa only [LinearEquiv.apply_symm_apply] using hcoeff s
  · have hzero : c = 0 := by
      rw [KoszulComplex.polynomialCoefficientFiltration, if_neg hnp, Submodule.mem_bot] at hc
      exact hc
    rw [hzero, map_zero]
    exact (envelopingFiltration R L p n).zero_mem

/-- total-degree membership is equivalent to the polynomial
coefficient-degree membership, over the original scalar ring. -/
theorem envelopingCoefficientCoordinates_mem_filtration_iff (b : Module.Basis I R L)
    (n p : ℕ) (z : (⋀[R]^n L) ⊗[R] regularCoefficients R L) :
    envelopingCoefficientCoordinates R L b n z ∈
      KoszulComplex.polynomialCoefficientFiltration R n p ↔
      z ∈ envelopingFiltration R L p n := by
  constructor
  · intro hz
    simpa only [LinearEquiv.symm_apply_apply] using
      envelopingCoefficientCoordinates_symm_mem_filtration R L b n p hz
  · exact envelopingCoefficientCoordinates_mem_filtration R L b n p

end ChevalleyEilenberg
