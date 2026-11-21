/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import MathlibExt.AlgebraicGeometry.SemistableAdicMonodromy
public import MathlibExt.AlgebraicGeometry.RapoportZinkContracts

/-!
# Geometric unipotence for proper strictly semistable degeneration

Authors: Luc Illusie; the nearby-cycle calculation uses Michael Rapoport
and Thomas Zink.
Source: Illusie, *Autour du theoreme de monodromie locale*, Astérisque 223
(1994), Exposé I, Corollary 3.3, p. 35; section 3.1, pp. 33--34, gives the
precise geometric hypotheses.
https://www.numdam.org/item/AST_1994__223__9_0/

The completed `SemistableModels` core supplies general models over actual
DVRs, prescribed uniformizers, etale charts, global smooth components and
actual intersection schemes with their restriction inclusion maps. A
provider identifying a paper's family with such a model is separate input.
The proof request specializes this generic interface to Z_p: every inertia
element acts unipotently on actual rational adic H^n, with exponent n+1.
Generic local-monodromy logarithms, unramified fields and strict-local
vanishing-cycle fibres are existing public toolbox.

The general sections below provide actual global nearby/inertia,
Weil--Deligne, monodromy-filtration and normalized Rapoport--Zink
filtered-resolution/stratum-grade signatures over henselian DVRs. General
provider proofs and canonical face/Gysin/arithmetic refinements remain
explicit shared obligations. No mixed-characteristic weight-monodromy
conjecture or arbitrary spectral-sequence/representation input is assumed.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.SemistableAdicMonodromy

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.PadicNeronModels
open MathlibExt.AlgebraicGeometry.SemistableAdicMonodromy

/-- Illusie's geometric semistable all-inertia nilpotence bound. -/
public theorem_wanted inertia_unipotent
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime]
    (ellNeResidueCharacteristic : ell ≠ p)
    (X : Over (trait p)) [IsProper X.hom]
    (semistable : IsStrictlySemistable p X)
    (n : ℕ) (σ : Galois p) (inertiaElement : σ ∈ inertia p) :
    (galoisOperator p X ell σ n - 1) ^ (n + 1) = 0

end WantedExt.AlgebraicGeometry.SemistableAdicMonodromy

namespace WantedExt.AlgebraicGeometry.GeneralSemistableDegeneration

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.Limits
open MathlibExt.AlgebraicGeometry
open GeometricSemistableTraits AdicDerivedContracts AdicConstructibleContracts
open SemistableWeilDeligne

attribute [local instance] HasDerivedCategory.standard

/-!
## General provider requests

These statements work over actual henselian DVRs and the actual geometric
normalization. All shared derived-functor, coefficient, perverse and
tame-coordinate inputs are named, characterized contracts on actual
objects and maps. Their source-covered adapters may be provided separately.
The external geometric providers below are not assumptions of a paper's
new conclusion. The original Z_p component above remains available.

The RZ signature identifies the actual filtered nearby resolution and its
actual stratum/Tate grades. Canonical face/Gysin and arithmetic refinements
remain explicit shared obligations; native d1 is already fixed by the complex.
No generic-H monodromy-weight conjecture is asserted.
-/

/-- The all-inertia cohomological bound over a general henselian trait. -/
public theorem_wanted generalInertiaUnipotent
    (ell p : ℕ) [Fact ell.Prime]
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [CharP (IsLocalRing.ResidueField R) p]
    (ellNeResidue : ell ≠ p)
    (K L : Type) [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsAlgClosure K L]
    (π : R) (T : GeometricTrait R K L π)
    (X : Over (Spec (.of R))) [IsProper X.hom]
    (semistable : SemistableModels.IsStrictlySemistable R π X)
    (n : ℕ) (σ : Inertia π T) :
    (operator ell R K L X σ.1.1 n - 1) ^ (n + 1) = 0

/-- The actual shifted nearby object belongs to the characterized middle
  heart. -/
public instance_wanted nearbyMiddleHeart
    (ell p : ℕ) [Fact ell.Prime]
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [CharP (IsLocalRing.ResidueField R) p]
    (ellNeResidue : ell ≠ p)
    (K L : Type) [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsAlgClosure K L]
    (π : R) (T : GeometricTrait R K L π)
    (X : Over (Spec (.of R))) [IsProper X.hom]
    (semistable : SemistableModels.IsStrictlySemistable R π X)
    (d : ℕ) [SmoothOfRelativeDimension d ((SemistableModels.genericFunctor R
      K).obj X).hom]
    [DerivedFunctorTheory ℚ_[ell]]
    [CoefficientTheory ℚ_[ell]
      (GeometricAdicGaloisOperators.RationalCoefficients.{0} ell)]
    [InertiaSchemeCompatibility π T X]
    [CoefficientPresentation ell (Residue π T)
      (RapoportZinkContracts.specialModel R K L π T X)]
    [PerverseTheory ell (Residue π T) (RapoportZinkContracts.specialModel R
      K L π T X)] :
    RapoportZinkContracts.NearbyPerverseMembership ell R K L π T X d

/-- The actual geometric nearby monodromy has its relative-dimension bound. -/
public theorem_wanted nearbyInertiaNilpotent
    (ell p : ℕ) [Fact ell.Prime]
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [CharP (IsLocalRing.ResidueField R) p]
    (ellNeResidue : ell ≠ p)
    (K L : Type) [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsAlgClosure K L]
    (π : R) (T : GeometricTrait R K L π)
    (X : Over (Spec (.of R))) [IsProper X.hom]
    (semistable : SemistableModels.IsStrictlySemistable R π X)
    (d : ℕ) [SmoothOfRelativeDimension d ((SemistableModels.genericFunctor R
      K).obj X).hom]
    [DerivedFunctorTheory ℚ_[ell]]
    [CoefficientTheory ℚ_[ell]
      (GeometricAdicGaloisOperators.RationalCoefficients.{0} ell)]
    [InertiaSchemeCompatibility π T X] (σ : Inertia π T) :
    (RapoportZinkContracts.inertiaOperator ell R K L π T X σ - 1) ^ (d + 1) = 0

/-- Deligne's laws for the fixed kernel-image filtration of actual nearby N. -/
public theorem_wanted nearbyMonodromyFiltration
    (ell : ℕ) [Fact ell.Prime]
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K L : Type) [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsAlgClosure K L]
    (π : R) (T : GeometricTrait R K L π)
    (X : Over (Spec (.of R))) [IsProper X.hom] (d : ℕ)
    [DerivedFunctorTheory ℚ_[ell]]
    [CoefficientTheory ℚ_[ell]
      (GeometricAdicGaloisOperators.RationalCoefficients.{0} ell)]
    [InertiaSchemeCompatibility π T X]
    [CoefficientPresentation ell (Residue π T)
      (RapoportZinkContracts.specialModel R K L π T X)]
    [PerverseTheory ell (Residue π T) (RapoportZinkContracts.specialModel R
      K L π T X)]
    [RapoportZinkContracts.NearbyPerverseMembership ell R K L π T X d]
    [Abelian (PerverseHeart ell (Residue π T)
      (RapoportZinkContracts.specialModel R K L π T X))]
    (B : TameCoordinate ell R K L π T)
    (nilpotent : (RapoportZinkContracts.perverseLog ell R K L π T X d B) ^
      (d + 1) = 0) :
    MathlibExt.CategoryTheory.MonodromyFiltration.MonodromyLaws
      (RapoportZinkContracts.perverseLog ell R K L π T X d B) d

/-- The normalized actual semistable Weil--Deligne association laws. -/
public theorem_wanted semistableWeilDeligne
    (ell p : ℕ) [Fact ell.Prime]
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [CharP (IsLocalRing.ResidueField R) p]
    (ellNeResidue : ell ≠ p)
    (K L : Type) [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsAlgClosure K L]
    (π : R) (T : GeometricTrait R K L π)
    (X : Over (Spec (.of R))) [IsProper X.hom]
    (semistable : SemistableModels.IsStrictlySemistable R π X) (n : ℕ)
    [CohomologyFunctoriality ell R K L X n]
    (A : ArithmeticFrobenius R K L π T) (B : TameCoordinate ell R K L π T) :
    SemistableWeilDeligneLaws ell R K L X n A B

/-- The general geometric filtered-resolution and actual stratum-grade
  provider. -/
public instance_wanted rapoportZinkTheory
    (ell p : ℕ) [Fact ell.Prime]
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [CharP (IsLocalRing.ResidueField R) p]
    (ellNeResidue : ell ≠ p)
    (K L : Type) [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsAlgClosure K L]
    (π : R) (T : GeometricTrait R K L π)
    (X : Over (Spec (.of R))) [IsProper X.hom]
    (semistable : SemistableModels.IsStrictlySemistable R π X)
    (d : ℕ) [SmoothOfRelativeDimension d ((SemistableModels.genericFunctor R
      K).obj X).hom]
    [DerivedFunctorTheory ℚ_[ell]]
    [CoefficientTheory ℚ_[ell]
      (GeometricAdicGaloisOperators.RationalCoefficients.{0} ell)]
    [InertiaSchemeCompatibility π T X]
    [CoefficientPresentation ell (Residue π T)
      (RapoportZinkContracts.specialModel R K L π T X)]
    [PerverseTheory ell (Residue π T) (RapoportZinkContracts.specialModel R
      K L π T X)]
    [RapoportZinkContracts.NearbyPerverseMembership ell R K L π T X d]
    [Abelian (PerverseHeart ell (Residue π T)
      (RapoportZinkContracts.specialModel R K L π T X))]
    [Fintype (irreducibleComponents ((SemistableModels.specialFunctor R).obj
      X).left)]
    [HasFiniteBiproducts (CochainComplex (ModuleCat.{1} ℚ_[ell]) ℤ)]
    (B : TameCoordinate ell R K L π T) (ellInvertible : (ell : L) ≠ 0) :
    RapoportZinkContracts.RapoportZinkTheory ell R K L π T X d B ellInvertible

end WantedExt.AlgebraicGeometry.GeneralSemistableDegeneration
