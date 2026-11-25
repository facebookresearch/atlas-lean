/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Algebra.Homology.Hochschild.PolynomialFormProjection

/-!
# Inverting polynomial form projection in one degree

In degree n, the unscaled form
projection differs from the inverse
polynomial antisymmetrization by n!.
When n! is invertible in the ground
ring, rescaling the projection gives
that inverse. Only this fixed-degree
unit condition is required.
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

/-- Rescale the original form projection by the fixed-degree inverse factorial. -/
def scaledCoefficientFormHomologyMap :
    (Symmetric.chainComplex k A M).homology n →ₗ[k] M ⊗[A] (⋀[A]^n Ω) :=
  ⅟ (n.factorial : k) • Symmetric.coefficientDifferentialFormHomologyLinearMap k A M n

/-- The rescaled projection is a left inverse of signed antisymmetrization. -/
theorem scaledCoefficientFormHomologyMap_antisymmetrization
    (ω : M ⊗[A] (⋀[A]^n Ω)) :
    scaledCoefficientFormHomologyMap k σ M n
      (polynomialAntisymmetrizationHomology k σ M n ω) = ω := by
  rw [scaledCoefficientFormHomologyMap, LinearMap.smul_apply,
    coefficientFormHomologyMap_antisymmetrization,
    ← Nat.cast_smul_eq_nsmul (R := k), smul_smul, invOf_mul_self, one_smul]

/-- The rescaled original projection is exactly the original
polynomial inverse, as an equality of linear maps. -/
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

/-- The fixed-degree rescaled projection and antisymmetrization
also satisfy the right inverse law on the original Hochschild homology. -/
theorem antisymmetrization_scaledCoefficientFormHomologyMap
    (z : (Symmetric.chainComplex k A M).homology n) :
    polynomialAntisymmetrizationHomology k σ M n
      (scaledCoefficientFormHomologyMap k σ M n z) = z := by
  rw [scaledCoefficientFormHomologyMap_eq_inverse]
  rw [← polynomialAntisymmetrizationHomologyEquiv_toLinearMap]
  exact LinearEquiv.symm_apply_apply _ _

/-- The native polynomial form isomorphism has the rescaled projection
as its forward linear map. -/
def scaledCoefficientFormHomologyIso :
    (Symmetric.chainComplex k A M).homology n ≅ ModuleCat.of k (M ⊗[A] (⋀[A]^n Ω)) :=
  (symmetricHochschildDifferentialFormEquiv k σ M n).toModuleIso

/-- The isomorphism retains the rescaled projection. -/
theorem scaledCoefficientFormHomologyIso_hom :
    (scaledCoefficientFormHomologyIso k σ M n).hom.hom =
      scaledCoefficientFormHomologyMap k σ M n := by
  exact (scaledCoefficientFormHomologyMap_eq_inverse k σ M n).symm

omit [Invertible (n.factorial : k)] in
/-- Its inverse is the signed polynomial antisymmetrization. -/
theorem scaledCoefficientFormHomologyIso_inv :
    (scaledCoefficientFormHomologyIso k σ M n).inv.hom =
      polynomialAntisymmetrizationHomology k σ M n :=
  polynomialAntisymmetrizationHomologyEquiv_toLinearMap k σ M n

end ModuleCat.Algebra.Hochschild.PolynomialDiagonal
