/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.PolynomialNormalizedExterior
public import MathlibExt.Algebra.Homology.Hochschild.SymmetricEulerianOperators
public import MathlibExt.LinearAlgebra.TensorPower.EulerianAntisymmetrization

/-!
# Eulerian weights of polynomial antisymmetric representatives

In the rational Eulerian setting, signed polynomial
antisymmetric representatives in degree n lie in weight n.
The action follows from their signed permutation formulas
and the polynomial exterior homology comparison.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild.PolynomialDiagonal

variable (k : Type u) [CommRing k] [Algebra ℚ k] (σ : Type v)
  (M : Type w) [AddCommGroup M] [Module k M] [Module (MvPolynomial σ k) M]
  [SMulCommClass k (MvPolynomial σ k) M] [IsScalarTower k (MvPolynomial σ k) M]

local notation "A" => MvPolynomial σ k
local notation "V" => σ →₀ k

-- Use the canonical symmetric opposite-action dictionaries locally.
attribute [local instance] Symmetric.opModule Symmetric.actionsComm
  Symmetric.kOpComm Symmetric.kOpTower

/-- Every original signed polynomial degree-n tensor has exactly its top Eulerian weight. -/
theorem polynomialSignedRepresentative_eulerian (n i : ℕ) (x : M ⊗[k] (⋀[k]^n V)) :
    Symmetric.coefficientEulerianOperator k A M n i (polynomialSignedRepresentative k σ M n x) =
      if i = n then polynomialSignedRepresentative k σ M n x else 0 := by
  let F := TensorProduct.map (LinearMap.id : M →ₗ[k] M) (TensorPower.exteriorAntisymmetrization k A n)
  let L := TensorProduct.map (LinearMap.id : M →ₗ[k] M)
    (exteriorPower.map n (polynomialGeneratorLinear k σ))
  have hF : ((polynomialAntisymmetricCoefficientMap k σ M).f n).hom.comp
      (coefficientFreeExteriorEquiv k σ M n).symm.toLinearMap = F.comp L := by
    rw [polynomialAntisymmetricCoefficientMap_free_coordinates,
      AdjacentBar.exteriorAntisymmetrizationAlong,
      TensorPower.exteriorAntisymmetrization_naturality]
    change TensorProduct.map (LinearMap.id : M →ₗ[k] M)
        ((TensorPower.exteriorAntisymmetrization k A n).comp
          (exteriorPower.map n (polynomialGeneratorLinear k σ))) =
      (TensorProduct.map (LinearMap.id : M →ₗ[k] M)
        (TensorPower.exteriorAntisymmetrization k A n)).comp
          (TensorProduct.map (LinearMap.id : M →ₗ[k] M)
            (exteriorPower.map n (polynomialGeneratorLinear k σ)))
    rw [← TensorProduct.map_comp, LinearMap.id_comp]
  have hx : polynomialSignedRepresentative k σ M n x = F (L x) :=
    DFunLike.congr_fun hF x
  have hE : (Symmetric.coefficientEulerianOperator k A M n i).comp F =
      if i = n then F else 0 :=
    TensorPower.coefficientEulerian_exteriorAntisymmetrization k A M n i
  rw [hx]
  have h := DFunLike.congr_fun hE (L x)
  by_cases hi : i = n
  · simpa only [LinearMap.comp_apply, ite_eq_left hi] using h
  · simpa only [LinearMap.comp_apply, ite_eq_right hi, LinearMap.zero_apply] using h

end ModuleCat.Algebra.Hochschild.PolynomialDiagonal
