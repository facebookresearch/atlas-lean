/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import MathlibExt.LinearAlgebra.Finsupp.ScalarExtensionCoordinates
public import MathlibExt.LinearAlgebra.ExteriorPower.BaseChange

/-!
# Polynomial cotangent and exterior coordinates

The polynomial cotangent module is the native free module on its actual
variable differentials. Scalar extension and the existing exterior-power
base change equivalence give canonical coordinates in every degree.
Coefficient cancellation retains the original coefficient first and
requires no coefficient flatness or projectivity.

The coordinate detectors are the native exterior-basis determinant
pairings. For a differential word their entries are actual polynomial
partial derivatives. All constructions apply over arbitrary commutative
ground rings and arbitrary variable types; a linear order is needed only
to name an oriented basis coordinate.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct

universe u v w w'

namespace KaehlerDifferential

variable (k : Type u) [CommRing k] (σ : Type v)

local notation "A" => MvPolynomial σ k
local notation "V" => (σ →₀ k)
local notation "Ω" => KaehlerDifferential k A

/-- The original free generator module extended to the polynomial algebra is its actual
native cotangent module, with no basis or equivalence certificate supplied. -/
def mvPolynomialBaseChangeEquiv : A ⊗[k] V ≃ₗ[A] Ω :=
  (Finsupp.scalarExtensionCoordinates k A σ).trans (mvPolynomialEquiv k σ).symm

/-- The original extended coordinate generator is the actual differential of its variable. -/
theorem mvPolynomialBaseChangeEquiv_tmul_single (i : σ) (a : A) :
    mvPolynomialBaseChangeEquiv k σ (a ⊗ₜ[k] Finsupp.single i (1 : k)) =
      a • D k A (MvPolynomial.X i) := by
  rw [mvPolynomialBaseChangeEquiv, LinearEquiv.trans_apply,
    Finsupp.scalarExtensionCoordinates_tmul_single, map_one, one_mul]
  exact mvPolynomialBasis_repr_symm_single k σ i a

/-- The actual ground-linear polynomial cotangent generator, extended additively from
the original finitely supported free module. -/
def mvPolynomialCotangentGenerator : V →ₗ[k] Ω :=
  ((mvPolynomialBaseChangeEquiv k σ).toLinearMap.restrictScalars k).comp
    (TensorProduct.mk k A V 1)

/-- The cotangent generator sends the original unit basis element to `dX`. -/
theorem mvPolynomialCotangentGenerator_single (i : σ) :
    mvPolynomialCotangentGenerator k σ (Finsupp.single i (1 : k)) =
      D k A (MvPolynomial.X i) := by
  change mvPolynomialBaseChangeEquiv k σ ((1 : A) ⊗ₜ[k] Finsupp.single i (1 : k)) = _
  rw [mvPolynomialBaseChangeEquiv_tmul_single, one_smul]

/-- Original free exterior generator coordinates are the actual polynomial differential forms. -/
def mvPolynomialExteriorEquiv (n : ℕ) : A ⊗[k] (⋀[k]^n V) ≃ₗ[A] (⋀[A]^n Ω) :=
  (exteriorPower.baseChangeEquiv k A V n).trans
    (exteriorPower.mapEquiv A (A ⊗[k] V) n (mvPolynomialBaseChangeEquiv k σ))

/-- The comparison preserves every original decomposable generator word and its actual
polynomial coefficient. -/
theorem mvPolynomialExteriorEquiv_tmul_ιMulti (n : ℕ) (a : A) (v : Fin n → V) :
    mvPolynomialExteriorEquiv k σ n (a ⊗ₜ[k] exteriorPower.ιMulti k n v) =
      a • exteriorPower.ιMulti A n (fun j => mvPolynomialCotangentGenerator k σ (v j)) := by
  rw [mvPolynomialExteriorEquiv, LinearEquiv.trans_apply,
    exteriorPower.baseChangeEquiv_apply_tmul_ιMulti, map_smul,
    exteriorPower.mapEquiv_apply_ιMulti]
  rfl

/-- Every original variable wedge is the corresponding actual differential wedge. -/
theorem mvPolynomialExteriorEquiv_tmul_basis (n : ℕ) (a : A) (f : Fin n → σ) :
    mvPolynomialExteriorEquiv k σ n
      (a ⊗ₜ[k] exteriorPower.ιMulti k n (fun j => Finsupp.single (f j) (1 : k))) =
      a • exteriorPower.ιMulti A n (fun j => D k A (MvPolynomial.X (f j))) := by
  rw [mvPolynomialExteriorEquiv_tmul_ιMulti]
  simp only [mvPolynomialCotangentGenerator_single]

section Coefficients

variable (M : Type w) [AddCommGroup M] [Module k M] [Module (MvPolynomial σ k) M]
  [SMulCommClass k (MvPolynomial σ k) M] [IsScalarTower k (MvPolynomial σ k) M]

/-- The original coefficient-first free exterior model is the actual coefficient-first
polynomial differential-form module. No flatness of the coefficient is required. -/
def mvPolynomialCoefficientExteriorEquiv (n : ℕ) :
    M ⊗[k] (⋀[k]^n V) ≃ₗ[A] M ⊗[A] (⋀[A]^n Ω) :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange k A A M (⋀[k]^n V)).symm.trans
    (TensorProduct.congr (LinearEquiv.refl A M) (mvPolynomialExteriorEquiv k σ n))

/-- The original coefficient head remains first, with the original cotangent generator in every tail slot. -/
theorem mvPolynomialCoefficientExteriorEquiv_tmul_ιMulti
    (n : ℕ) (m : M) (v : Fin n → V) :
    mvPolynomialCoefficientExteriorEquiv k σ M n (m ⊗ₜ[k] exteriorPower.ιMulti k n v) =
      m ⊗ₜ[A] exteriorPower.ιMulti A n
        (fun j => mvPolynomialCotangentGenerator k σ (v j)) := by
  rw [mvPolynomialCoefficientExteriorEquiv, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    mvPolynomialExteriorEquiv_tmul_ιMulti, one_smul]

/-- Original variable wedges give original coefficient differential wedges over every ground ring. -/
theorem mvPolynomialCoefficientExteriorEquiv_tmul_basis
    (n : ℕ) (m : M) (f : Fin n → σ) :
    mvPolynomialCoefficientExteriorEquiv k σ M n
      (m ⊗ₜ[k] exteriorPower.ιMulti k n (fun j => Finsupp.single (f j) (1 : k))) =
      m ⊗ₜ[A] exteriorPower.ιMulti A n (fun j => D k A (MvPolynomial.X (f j))) := by
  rw [mvPolynomialCoefficientExteriorEquiv_tmul_ιMulti]
  simp only [mvPolynomialCotangentGenerator_single]

/-- The inverse recovers the independently specified original free coefficient word. -/
theorem mvPolynomialCoefficientExteriorEquiv_symm_tmul_basis
    (n : ℕ) (m : M) (f : Fin n → σ) :
    (mvPolynomialCoefficientExteriorEquiv k σ M n).symm
      (m ⊗ₜ[A] exteriorPower.ιMulti A n (fun j => D k A (MvPolynomial.X (f j)))) =
      m ⊗ₜ[k] exteriorPower.ιMulti k n (fun j => Finsupp.single (f j) (1 : k)) := by
  apply (mvPolynomialCoefficientExteriorEquiv k σ M n).injective
  rw [LinearEquiv.apply_symm_apply, mvPolynomialCoefficientExteriorEquiv_tmul_basis]

section Coordinates

variable [LinearOrder σ]

/-- The actual exterior-basis coordinate detector on polynomial differential forms. -/
def mvPolynomialFormCoordinate (n : ℕ) (s : Set.powersetCard σ n) :
    (⋀[A]^n Ω) →ₗ[A] A :=
  ((mvPolynomialBasis k σ).exteriorPower n).coord s

/-- Actual polynomial partial derivatives give the determinant coordinate of an
original differential word. This holds over a general commutative ground ring. -/
theorem mvPolynomialFormCoordinate_differentials
    (n : ℕ) (s : Set.powersetCard σ n) (f : Fin n → A) :
    mvPolynomialFormCoordinate k σ n s
      (exteriorPower.ιMulti A n (fun j => D k A (f j))) =
      (Matrix.of fun i j =>
        MvPolynomial.pderiv (Set.powersetCard.ofFinEmbEquiv.symm s j) (f i)).det := by
  rw [mvPolynomialFormCoordinate, exteriorPower.basis_coord,
    exteriorPower.ιMultiDual_apply_ιMulti]
  congr 1
  apply Matrix.ext
  intro i j
  change (mvPolynomialBasis k σ).coord (Set.powersetCard.ofFinEmbEquiv.symm s j) (D k A (f i)) =
    MvPolynomial.pderiv (Set.powersetCard.ofFinEmbEquiv.symm s j) (f i)
  rw [Module.Basis.coord_apply]
  exact mvPolynomialBasis_repr_apply k σ _ _

/-- The coefficient form detector uses the original coefficient and native scalar unitor. -/
def mvPolynomialCoefficientFormCoordinate (n : ℕ) (s : Set.powersetCard σ n) :
    M ⊗[A] (⋀[A]^n Ω) →ₗ[A] M :=
  (TensorProduct.rid A M).toLinearMap.comp
    (TensorProduct.map LinearMap.id (mvPolynomialFormCoordinate k σ n s))

omit [Module k M] [SMulCommClass k (MvPolynomial σ k) M]
  [IsScalarTower k (MvPolynomial σ k) M] in
/-- Evaluation of an original pure coefficient form is the actual scalar coordinate acting
on its original coefficient, without any coefficient basis. -/
theorem mvPolynomialCoefficientFormCoordinate_tmul
    (n : ℕ) (s : Set.powersetCard σ n) (m : M) (ω : ⋀[A]^n Ω) :
    mvPolynomialCoefficientFormCoordinate k σ M n s (m ⊗ₜ[A] ω) =
      mvPolynomialFormCoordinate k σ n s ω • m := by
  rw [mvPolynomialCoefficientFormCoordinate, LinearMap.comp_apply,
    TensorProduct.map_tmul, LinearMap.id_apply]
  change (TensorProduct.rid A M) (m ⊗ₜ[A] mvPolynomialFormCoordinate k σ n s ω) =
    mvPolynomialFormCoordinate k σ n s ω • m
  exact TensorProduct.rid_tmul m _

omit [Module k M] [SMulCommClass k (MvPolynomial σ k) M]
  [IsScalarTower k (MvPolynomial σ k) M] in
/-- The detector of a coefficient differential word is the actual Jacobian minor
acting on the original coefficient. -/
theorem mvPolynomialCoefficientFormCoordinate_differentials
    (n : ℕ) (s : Set.powersetCard σ n) (m : M) (f : Fin n → A) :
    mvPolynomialCoefficientFormCoordinate k σ M n s
      (m ⊗ₜ[A] exteriorPower.ιMulti A n (fun j => D k A (f j))) =
      (Matrix.of fun i j =>
        MvPolynomial.pderiv (Set.powersetCard.ofFinEmbEquiv.symm s j) (f i)).det • m := by
  rw [mvPolynomialCoefficientFormCoordinate_tmul, mvPolynomialFormCoordinate_differentials]

/-- The original oriented coordinate word has actual coefficient one at its own column. -/
theorem mvPolynomialFormCoordinate_basis (n : ℕ) (s : Set.powersetCard σ n) :
    mvPolynomialFormCoordinate k σ n s
      (exteriorPower.ιMulti A n (fun j =>
        D k A (MvPolynomial.X (Set.powersetCard.ofFinEmbEquiv.symm s j)))) = 1 := by
  simp only [mvPolynomialFormCoordinate, ← mvPolynomialBasis_apply]
  change ((mvPolynomialBasis k σ).exteriorPower n).coord s
    (exteriorPower.ιMulti_family A n (mvPolynomialBasis k σ) s) = 1
  rw [Module.Basis.coord_apply, ← exteriorPower.basis_apply, Module.Basis.repr_self,
    Finsupp.single_eq_same]

omit [Module k M] [SMulCommClass k (MvPolynomial σ k) M]
  [IsScalarTower k (MvPolynomial σ k) M] in
/-- The oriented actual variable word is detected as its original coefficient. -/
theorem mvPolynomialCoefficientFormCoordinate_basis
    (n : ℕ) (s : Set.powersetCard σ n) (m : M) :
    mvPolynomialCoefficientFormCoordinate k σ M n s
      (m ⊗ₜ[A] exteriorPower.ιMulti A n (fun j =>
        D k A (MvPolynomial.X (Set.powersetCard.ofFinEmbEquiv.symm s j)))) = m := by
  rw [mvPolynomialCoefficientFormCoordinate_tmul, mvPolynomialFormCoordinate_basis, one_smul]

end Coordinates

end Coefficients

end KaehlerDifferential
