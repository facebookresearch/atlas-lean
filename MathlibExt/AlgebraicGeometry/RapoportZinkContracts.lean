/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.AdicDerivedContracts
public import MathlibExt.AlgebraicGeometry.SemistableWeilDeligne

/-!
# Nearby cycles of a semistable degeneration and their inertia monodromy

For a proper scheme `X` over a discrete valuation ring with geometric trait `T`, the nearby object
is `i^* Rj_*` of the continuous `ℚ_ℓ` coefficients, for the generic and special arrows into the
normalized model. Specialization is the map from the coefficients on the special fibre, and the
inertia operator of `σ` is the endomorphism of the nearby object induced by the actions of `σ`
on the normalized model and on the generic fibre (`AdicDerivedContracts.nearbyMonodromy`).
`nearbyLog` is the truncated logarithm of the operator of the tame generator.

The hypotheses are that the coefficient maps `f⁻¹ C(-, ℚ_ℓ) ⟶ C(-, ℚ_ℓ)` along the special arrow
(for specialization) and along the Galois automorphisms of the generic fibre (for the inertia
operators) are isomorphisms.

The Rapoport–Zink part (the perverse nearby object `RΨ(ℚ_ℓ)[d]`, its monodromy filtration and
the filtered resolution with its spectral sequence) is not included: it needs a constructible
coefficient category over the continuous coefficient ring sheaf, which is left for later work.

Source: Illusie, Astérisque 223 (1994), Exposé I, §§3.1–3.3,
https://www.numdam.org/item/AST_1994__223__9_0/
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.RapoportZinkContracts

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open AdicDerivedContracts
open GeometricSemistableTraits GeometricAdicGaloisOperators
open SemistableWeilDeligne

attribute [local instance] HasDerivedCategory.standard

variable (ell : ℕ) [Fact ell.Prime]
  (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K L : Type) [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [IsAlgClosure K L] (π : R) (T : GeometricTrait R K L π)
  (X : Over (Spec (.of R))) [IsProper X.hom]
  [DerivedFunctorTheory ℚ_[ell]]

/-- The nearby object `i^* Rj_* C(-, ℚ_ℓ)`. -/
abbrev nearby :=
  nearbyObject ℚ_[ell] (RationalCoefficients.{0} ell)
    (genericArrow (L := L) X) (specialArrow π T X)

/-- The specialization map from the coefficients on the special fibre to the nearby object. -/
def specialization
    [IsIso (ProEtaleCohomologyFunctoriality.coefficientPullback ℚ_[ell]
      (RationalCoefficients.{0} ell) (specialArrow π T X))] :
    continuousComplex ℚ_[ell] (RationalCoefficients.{0} ell)
      (SpecialFibre π T X) ⟶ nearby ell R K L π T X :=
  AdicDerivedContracts.specialization ℚ_[ell] (RationalCoefficients.{0} ell)
    (genericArrow (L := L) X) (specialArrow π T X)

variable [∀ σ : Galois K L, IsIso (ProEtaleCohomologyFunctoriality.coefficientPullback ℚ_[ell]
    (RationalCoefficients.{0} ell) (genericGalois (K := K) X σ))]

/-- The operator of an inertia element on the nearby object. -/
def inertiaOperator (σ : Inertia π T) : End (nearby ell R K L π T X) :=
  AdicDerivedContracts.nearbyMonodromy ℚ_[ell] (RationalCoefficients.{0} ell)
    (genericArrow (L := L) X) (specialArrow π T X)
    (normalGalois (K := K) X σ.1.1) (genericGalois (K := K) X σ.1.1)
    ((inertiaSchemeCompatibility π T X).genericSquare σ)
    ((inertiaSchemeCompatibility π T X).specialSquare σ)

/-- The logarithm `∑_{0 < i ≤ d} (-1)^(i+1) (σ - 1)^i / i` of the operator of the tame generator
`σ`, truncated at degree `d`. -/
def nearbyLog (d : ℕ) (B : TameCoordinate ell R K L π T) :
    End (nearby ell R K L π T X) :=
  ∑ i ∈ (Finset.range (d + 1)).filter (fun i ↦ 0 < i),
    (((-1 : ℚ_[ell]) ^ (i + 1)) * (i : ℚ_[ell])⁻¹) •
      (inertiaOperator ell R K L π T X B.generator - 1) ^ i

end MathlibExt.AlgebraicGeometry.RapoportZinkContracts
