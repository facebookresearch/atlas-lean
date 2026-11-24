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
# Unipotence of inertia for proper strictly semistable degenerations

For a proper strictly semistable scheme over a henselian discrete valuation ring with residue
characteristic `p` and a prime `ℓ ≠ p`, every inertia element `σ` acts unipotently on the rational
`ℓ`-adic cohomology `H^n` of the geometric generic fibre, with `(σ - 1)^(n+1) = 0` (Illusie,
Corollary 3.3; the hypotheses are those of §3.1), first over `ℤ_p` and then over a general trait.
On the nearby object, the inertia operators satisfy `(σ - 1)^(d+1) = 0` in relative dimension `d`.
The last request is the normalized Weil–Deligne association for the semistable cohomology.

The Rapoport–Zink part (the perverse nearby object, its monodromy filtration and the filtered
resolution with its stratum grades) is not included: it needs a constructible coefficient category
over the continuous coefficient ring sheaf, which is left for later work.

Source: Illusie, *Autour du théorème de monodromie locale*, Astérisque 223 (1994), Exposé I,
Corollary 3.3, p. 35, and §3.1, pp. 33–34, https://www.numdam.org/item/AST_1994__223__9_0/
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

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
open GeometricSemistableTraits AdicDerivedContracts
open SemistableWeilDeligne

attribute [local instance] HasDerivedCategory.standard

/-!
## General traits

The same bounds over a henselian discrete valuation ring with algebraically closed fraction field
extension `L`, for its geometric trait `T`, and the Weil–Deligne association. The residue
characteristic is a prime `p`, as in Illusie's §3.
-/

/-- The all-inertia cohomological bound over a general henselian trait. -/
public theorem_wanted generalInertiaUnipotent
    (ell p : ℕ) [Fact ell.Prime] [Fact p.Prime]
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

/-- On the nearby object, `(σ - 1)^(d+1) = 0` for every inertia element, in relative dimension
`d`. -/
public theorem_wanted nearbyInertiaNilpotent
    (ell p : ℕ) [Fact ell.Prime] [Fact p.Prime]
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
    [∀ σ : Galois K L, IsIso (ProEtaleCohomologyFunctoriality.coefficientPullback ℚ_[ell]
      (GeometricAdicGaloisOperators.RationalCoefficients.{0} ell) (genericGalois (K := K) X σ))]
    (σ : Inertia π T) :
    (RapoportZinkContracts.inertiaOperator ell R K L π T X σ - 1) ^ (d + 1) = 0

/-- The Weil–Deligne association laws for the semistable cohomology. -/
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

end WantedExt.AlgebraicGeometry.GeneralSemistableDegeneration
