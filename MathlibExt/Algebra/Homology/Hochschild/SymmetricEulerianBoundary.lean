/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/-
UNEXECUTED source proposal. Boundary compatibility is derived from the
original signed A-balanced cuts, not supplied as a law certificate.
-/
module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricBalancedConvolutionBoundary
public import MathlibExt.Algebra.Homology.Hochschild.SymmetricEulerianOperators
public import MathlibExt.LinearAlgebra.FiniteDyadicProjectorIntertwining

/-!
# Eulerian boundary compatibility

In positive degrees, bar-lambda at parameter two is
twice the identity plus the proper shuffle convolution.
Its boundary compatibility and the rational orthogonal
projectors give the boundary square for each Eulerian
weight. Loday’s second lambda operation is the negative
of this bar-lambda operation, with the same compatibility.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct BigOperators

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

attribute [local instance] ModuleCat.Algebra.Hochschild.uliftSMulCommClass

variable (k : Type u) [CommRing k] [Algebra ℚ k]
  (A : Type v) [CommRing A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

/-- The original bar-lambda operation at two commutes with the Hochschild boundary, including the original degree-one zero boundary. -/
theorem lambdaTwoOperator_boundary (n : ℕ) :
    ((chainComplex k A M).d (n + 1) n).hom.comp (lambdaTwoOperator k A M (n + 1)) =
      (lambdaTwoOperator k A M n).comp ((chainComplex k A M).d (n + 1) n).hom := by
  change ((algebraBoundary k A M n).restrictScalars k).comp (lambdaTwoOperator k A M (n + 1)) =
    (lambdaTwoOperator k A M n).comp ((algebraBoundary k A M n).restrictScalars k)
  cases n with
  | zero =>
    rw [algebraBoundary_zero]
    change (0 : M ⊗[k] TensorPower k 1 A →ₗ[k] M ⊗[k] TensorPower k 0 A).comp
        (lambdaTwoOperator k A M 1) =
      (lambdaTwoOperator k A M 0).comp
        (0 : M ⊗[k] TensorPower k 1 A →ₗ[k] M ⊗[k] TensorPower k 0 A)
    simp only [LinearMap.zero_comp, LinearMap.comp_zero]
  | succ n =>
    unfold lambdaTwoOperator
    rw [coefficientEulerianLambda_two_eq_proper_pairings k A M (n + 2) (by omega),
      coefficientEulerianLambda_two_eq_proper_pairings k A M (n + 1) (by omega)]
    simp only [LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_smul,
      LinearMap.smul_comp, LinearMap.comp_id, LinearMap.id_comp]
    congr 1
    have h := congrArg (fun f => f.restrictScalars k)
      (algebraProperShuffleConvolutionTwo_boundary k A M n)
    simpa only [LinearMap.restrictScalars_comp,
      algebraProperShuffleConvolutionTwo_restrictScalars] using h

/-- Every original rational Eulerian coefficient operator commutes with the
full Hochschild boundary. The conclusion is from the bar-lambda boundary square and the original rational projector laws. -/
theorem coefficientEulerian_boundary (n i : ℕ) :
    ((chainComplex k A M).d (n + 1) n).hom.comp
        (coefficientEulerianOperator k A M (n + 1) i) =
      (coefficientEulerianOperator k A M n i).comp
        ((chainComplex k A M).d (n + 1) n).hom := by
  change ((algebraBoundary k A M n).restrictScalars k).comp
      (coefficientEulerianOperator k A M (n + 1) i) =
    (coefficientEulerianOperator k A M n i).comp ((algebraBoundary k A M n).restrictScalars k)
  have hlambda : ((algebraBoundary k A M n).restrictScalars k).comp
      (lambdaTwoOperator k A M (n + 1)) =
    (lambdaTwoOperator k A M n).comp ((algebraBoundary k A M n).restrictScalars k) :=
    lambdaTwoOperator_boundary k A M n
  exact LinearMap.dyadicProjectorIntertwiner_comp
    (coefficientEulerianOperator k A M (n + 1)) (coefficientEulerianOperator k A M n)
    (n + 1) n ((algebraBoundary k A M n).restrictScalars k)
    (coefficientEulerian_projector_laws k A M (n + 1)).2
    (coefficientEulerian_projector_laws k A M n).2
    (fun j hj => coefficientEulerian_outside k A M (n + 1) j hj)
    (fun j hj => coefficientEulerian_outside k A M n j hj)
    (coefficientEulerian_projector_laws k A M (n + 1)).1
    (coefficientEulerian_projector_laws k A M n).1
    (by
      simpa only [LinearMap.dyadicProjectorSum, ← lambdaTwoOperator_eq_sum] using
        hlambda) i

end ModuleCat.Algebra.Hochschild.Symmetric
