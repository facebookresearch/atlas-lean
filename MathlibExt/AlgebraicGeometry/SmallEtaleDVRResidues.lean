/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SmallEtaleCohomologySystem
public import MathlibExt.AlgebraicGeometry.DVRSectionLattices

/-!
# Actual DVR localization cones and oriented torsion residues

The localization arrow is the fixed native Tate restriction and its cone
is an actual cochain mapping cone. Purity compares that exact cone with
the residue field's actual Tate RΓ object shifted by -1. The degree-one
orientation is fixed by every actual Kummer uniformizer and the literal
constant coefficient one.

Higher residues are maps relative to this purity comparison. Their
zero kernel depends only on the fixed localization arrow. Higher
cup/tensor coherence of the purity choices is an additional comparison
boundary; it is not silently claimed by degree-one orientation.
Source: Schreieder arXiv1801.05397v5 §2.3; Stacks étale purity.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SmallEtaleDVRResidues

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.SmallEtaleTorsionCoefficients
open MathlibExt.AlgebraicGeometry.SmallEtaleDerivedCohomology
open MathlibExt.AlgebraicGeometry.SmallEtaleTateRestriction
open MathlibExt.AlgebraicGeometry.SmallEtaleCohomologySystem
open MathlibExt.AlgebraicGeometry.DVRSectionLattices
attribute [local instance] HasDerivedCategory.standard

variable [AllSheafificationSources] [AllContinuousSources]
  [AllDerivedSectionsSources] [AllDerivedPushSources]

/-- Literal coefficient reduction sends the actual integer unit to the actual Z/l unit. -/
def scalarReduction (l : ℕ) :
    ModuleCat.of Scalar Scalar ⟶ ModuleCat.of Scalar (FiniteCoefficient l) :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton Scalar (FiniteCoefficient l) (1 : FiniteCoefficient l))

def coefficientReduction {l : ℕ} (S : Data l) (X : Scheme.{0}) :
    constantUnit X ⟶ S.coefficient X 0 :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{1} Scalar)).map (scalarReduction l)

/-- Actual degree-zero coefficient one in the fixed RΓ model. -/
def coefficientOne {l : ℕ} (S : Data l) (X : Scheme.{0}) : S.H X 0 0 :=
  globalUnit X 0 ≫ (derivedSections X).map
    ((DerivedCategory.singleFunctor (Coefficients X) 0).map (coefficientReduction S X))

def shiftedCoefficientOne {l : ℕ} (S : Data l) (X : Scheme.{0}) :
    (DerivedCategory.singleFunctor (ModuleCat.{1} Scalar) 1).obj (ModuleCat.of Scalar Scalar) ⟶
      (globalObject X (S.coefficient X 0))⟦(-1 : ℤ)⟧ :=
  ((DerivedCategory.singleFunctors (ModuleCat.{1} Scalar)).shiftIso (-1) 1 0 (by omega)).inv.app
    (ModuleCat.of Scalar Scalar) ≫ (coefficientOne S X)⟦(-1 : ℤ)⟧'

variable {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [HasExt.{2} (Coefficients (Spec (.of K)))]

abbrev genericMap : Spec (.of K) ⟶ Spec (.of R) := Spec.algebraMap R K
abbrev closedMap : Spec (.of (IsLocalRing.ResidueField R)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))

def genericUniformizer (u : Uniformizer (R := R) (K := K)) : (Γ(Spec (.of K),⊤))ˣ :=
  Units.map (Scheme.ΓSpecIso (.of K)).inv.hom.toMonoidHom u.genericUnit

/-- All actual Tate localization-cone comparisons, with degree-one Kummer orientation. -/
structure OrientedResidues {l : ℕ} (S : Data l)
    (M : ∀ j : ℕ, LocalizationModel S (genericMap (R := R) (K := K)) (j+1)) where
  comparison : ∀ j : ℕ, DerivedCategory.Q.obj (localizationCone (M j)) ≅
    (globalObject (Spec (.of (IsLocalRing.ResidueField R)))
      (S.coefficient (Spec (.of (IsLocalRing.ResidueField R))) j))⟦(-1 : ℤ)⟧
  uniformizer : ∀ (u : Uniformizer (R := R) (K := K))
    (E : KummerExactness (Spec (.of K)) (S.gm (Spec (.of K))) l)
    (A : UnitSection (Spec (.of K)) (S.gm (Spec (.of K))) (genericUniformizer u)),
    kummer (Spec (.of K)) (S.gm (Spec (.of K))) l E (genericUniformizer u) A ≫
      coneBoundary (M 0) ≫ (comparison 0).hom =
        shiftedCoefficientOne S (Spec (.of (IsLocalRing.ResidueField R)))

/-- A residue class is computed by the actual cone boundary and native inverse shift. -/
def residue {l : ℕ} {S : Data l}
    {M : ∀ j : ℕ, LocalizationModel S (genericMap (R := R) (K := K)) (j+1)}
    (P : OrientedResidues S M) (i : ℤ) (j : ℕ) :
    S.H (Spec (.of K)) i (j+1) → S.H (Spec (.of (IsLocalRing.ResidueField R))) (i-1) j :=
  fun a => (shiftFunctor (DerivedCategory (ModuleCat.{1} Scalar)) (-1 : ℤ)).preimage
    (((DerivedCategory.singleFunctors (ModuleCat.{1} Scalar)).shiftIso (-1) i (i-1)
      (by omega)).hom.app (ModuleCat.of Scalar Scalar) ≫
        a ≫ coneBoundary (M j) ≫ (P.comparison j).hom)

/-- The unramified zero test can be made on the fixed cone without choosing a purity isomorphism. -/
def HasZeroBoundary {l : ℕ} {S : Data l}
    {M : ∀ j : ℕ, LocalizationModel S (genericMap (R := R) (K := K)) (j+1)}
    (i : ℤ) (j : ℕ) (a : S.H (Spec (.of K)) i (j+1)) : Prop :=
  a ≫ coneBoundary (M j) = 0

end MathlibExt.AlgebraicGeometry.SmallEtaleDVRResidues
