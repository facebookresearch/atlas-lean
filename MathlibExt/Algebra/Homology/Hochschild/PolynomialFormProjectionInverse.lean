/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Algebra.Homology.Hochschild.PolynomialFormProjection

/-!
# Inverse factorial normalization in one polynomial degree

Let `k` be a commutative ring, `A` a polynomial `k`-algebra, and `M` a compatible symmetric
coefficient module. In degree `n`, the universal-form projection satisfies `π_n ∘ ε_n = n! •
id` for signed polynomial antisymmetrization `ε_n`.

When `(n! : k)` is invertible, the scaled map `(n!)⁻¹ • π_n` is exactly the inverse polynomial
exterior comparison. It is a two-sided inverse of `ε_n`. The polynomial comparison is defined
over a general commutative ring; the fixed-degree invertibility condition identifies its
forward map with this scaling.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild.PolynomialDiagonal

variable (k : Type u) [CommRing k] (σ : Type v)
  (M : Type w) [AddCommGroup M] [Module k M] [Module (MvPolynomial σ k) M]
  [SMulCommClass k (MvPolynomial σ k) M] [IsScalarTower k (MvPolynomial σ k) M]

local notation "A" => MvPolynomial σ k
local notation "Ω" => KaehlerDifferential k A

variable (n : ℕ) [Invertible (n.factorial : k)]

/-- The coefficient-form homology map scaled by an inverse factorial.

For a fixed degree `n` with invertible `(n! : k)`, multiply the unscaled coefficient-form
homology map by `(n!)⁻¹`. -/
def scaledCoefficientFormHomologyMap :
    (Symmetric.chainComplex k A M).homology n →ₗ[k] M ⊗[A] (⋀[A]^n Ω) :=
  ⅟ (n.factorial : k) • Symmetric.coefficientDifferentialFormHomologyLinearMap k A M n

/-- The left inverse law for inverse-factorial form projection.

For every degree-`n` coefficient form `ω`, the scaled projection of its signed polynomial
antisymmetrization equals `ω`. -/
theorem scaledCoefficientFormHomologyMap_antisymmetrization
    (ω : M ⊗[A] (⋀[A]^n Ω)) :
    scaledCoefficientFormHomologyMap k σ M n
      (polynomialAntisymmetrizationHomology k σ M n ω) = ω := by
  rw [scaledCoefficientFormHomologyMap, LinearMap.smul_apply,
    coefficientFormHomologyMap_antisymmetrization,
    ← Nat.cast_smul_eq_nsmul (R := k), smul_smul, invOf_mul_self, one_smul]

/-- The scaled form projection as the polynomial inverse comparison.

With `(n! : k)` invertible, the scaled coefficient-form homology map equals the linear map of
the polynomial differential-form equivalence. -/
theorem scaledCoefficientFormHomologyMap_eq_inverse :
    scaledCoefficientFormHomologyMap k σ M n =
      (symmetricHochschildDifferentialFormEquiv k σ M n).toLinearMap := by
  ext z
  let e := polynomialAntisymmetrizationHomologyEquiv k σ M n
  let E := symmetricHochschildDifferentialFormEquiv k σ M n
  obtain ⟨ω, rfl⟩ := e.surjective z
  have he : e ω = polynomialAntisymmetrizationHomology k σ M n ω :=
    (congrFun (LinearEquiv.coe_toLinearMap e) ω).symm.trans
      (LinearMap.congr_fun (polynomialAntisymmetrizationHomologyEquiv_toLinearMap k σ M n) ω)
  have hl : scaledCoefficientFormHomologyMap k σ M n (e ω) = ω :=
    (congrArg (scaledCoefficientFormHomologyMap k σ M n) he).trans
      (scaledCoefficientFormHomologyMap_antisymmetrization k σ M n ω)
  have hr : E.toLinearMap (e ω) = ω :=
    (congrFun (LinearEquiv.coe_toLinearMap E) (e ω)).trans
      ((congrArg E he).trans (polynomialAntisymmetrizationHomology_coordinates k σ M n ω))
  exact hl.trans hr.symm

/-- The right inverse law for inverse-factorial form projection.

For every degree-`n` polynomial Hochschild homology class, signed antisymmetrization after the
scaled form projection returns the class. -/
theorem antisymmetrization_scaledCoefficientFormHomologyMap
    (z : (Symmetric.chainComplex k A M).homology n) :
    polynomialAntisymmetrizationHomology k σ M n
      (scaledCoefficientFormHomologyMap k σ M n z) = z := by
  rw [scaledCoefficientFormHomologyMap_eq_inverse]
  rw [← polynomialAntisymmetrizationHomologyEquiv_toLinearMap]
  exact LinearEquiv.symm_apply_apply _ _

/-- The polynomial coefficient-form homology isomorphism.

The polynomial exterior comparison gives an isomorphism from degree-`n` Hochschild homology to
the coefficient-form module. When `n!` is invertible, its forward map is the inverse-
factorial-scaled form projection. -/
def scaledCoefficientFormHomologyIso :
    (Symmetric.chainComplex k A M).homology n ≅ ModuleCat.of k (M ⊗[A] (⋀[A]^n Ω)) :=
  (symmetricHochschildDifferentialFormEquiv k σ M n).toModuleIso

/-- The forward map of the inverse-factorial form comparison.

With `(n! : k)` invertible, the forward isomorphism map is the scaled coefficient-form
homology projection. -/
theorem scaledCoefficientFormHomologyIso_hom :
    (scaledCoefficientFormHomologyIso k σ M n).hom.hom =
      scaledCoefficientFormHomologyMap k σ M n := by
  exact (scaledCoefficientFormHomologyMap_eq_inverse k σ M n).symm

omit [Invertible (n.factorial : k)] in
/-- The signed inverse of the polynomial form comparison.

The inverse isomorphism map is polynomial signed antisymmetrization. This inverse description
is stated without a factorial-invertibility hypothesis. -/
theorem scaledCoefficientFormHomologyIso_inv :
    (scaledCoefficientFormHomologyIso k σ M n).inv.hom =
      polynomialAntisymmetrizationHomology k σ M n :=
  polynomialAntisymmetrizationHomologyEquiv_toLinearMap k σ M n

end ModuleCat.Algebra.Hochschild.PolynomialDiagonal
