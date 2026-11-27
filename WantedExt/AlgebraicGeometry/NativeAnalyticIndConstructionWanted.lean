/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.NativeTemperedHolomorphicModels
public import MathlibExt.AlgebraicGeometry.NativeBetaModuleDerivedModels
public import MathlibExt.AlgebraicGeometry.IndSheafDerivedAlphaModels
public import MathlibExt.CategoryTheory.NativeBoundedBimoduleModels
public import MathlibExt.AlgebraicGeometry.CanonicalOppositeRings

/-!
# Genuine native analytic Ind construction requests

Every constructor targets the complete already normalized source type:
actual alpha/left-beta and tensor coherence, original differential
constants, all ordinary module actions, all LF/subanalytic probes and
both compact-closure local-End distribution actions. Full analytic
construction proofs are tracked here separately from the public
definitions and computed de Rham/solution expressions.
Source: DK1311.2374v2 Sections2.2,4.10,5.1,5.2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.NativeAnalyticIndConstructionWanted

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory TopologicalSpace
open MathlibExt.AlgebraicGeometry
open CompactSupportIndSheaves NativeIndDifferentialContexts NativeTemperedHolomorphicModels
open RingedComplexCoefficientModels NativeBetaModuleDerivedModels IndSheafDerivedAlphaModels
open MathlibExt.CategoryTheory.NativeRingedAdjointImageModels
open MathlibExt.CategoryTheory.NativeBoundedBimoduleModels
open MathlibExt.CategoryTheory.NativeDerivedBimoduleCalculus
open MathlibExt.CategoryTheory.NativeOppositeBimoduleModels
open scoped Manifold ContDiff

def_wanted actual_ind_space_context (X : TopCat.{0}) [T2Space X] [LocallyCompactSpace X]
    [SigmaCompactSpace X]
    [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)]
    [CompactSheafSource ℂ X] : IndSpaceSource X

variable (X : TopCat.{0})
  [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)]
  [CompactSheafSource ℂ X]

local instance wantedIndPreadditive : Preadditive (IndSheaf ℂ X) := Abelian.toPreadditive

variable [C : IndSpaceSource X]

def_wanted actual_ordinary_beta_module_source (R : TopCat.Sheaf RingCat.{0} X)
    [BetaRingSource X R] : OrdinaryBetaModuleSource X R

theorem_wanted actual_native_balanced_tensor_derivation (R S T : Mon (IndSheaf ℂ X)) :
  TensorDerivationSource R S T

theorem_wanted actual_native_module_hom_closed (R S T : Mon (IndSheaf ℂ X))
    [TensorDerivationSource R S T] : TensorHomSource R S T

theorem_wanted actual_native_left_tensor_derivation (R S T : Mon (IndSheaf ℂ X)) :
  LeftTensorDerivationSource R S T

theorem_wanted actual_native_left_module_hom_closed (R S T : Mon (IndSheaf ℂ X))
    [LeftTensorDerivationSource R S T] : LeftTensorHomSource R S T

def_wanted actual_native_opposite_module_map (R S Rop Sop : Mon (IndSheaf ℂ X))
    (RO : OppositeMonoidSource R Rop) (SO : OppositeMonoidSource S Sop) :
  OppositeBimoduleSource R S Rop Sop RO SO

def_wanted actual_beta_unit_normalization (R : TopCat.Sheaf RingCat.{0} X)
    [BetaRingSource X R] : BetaUnitNormalizationSource X R

section OrdinaryBetaExact

variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{0}]

local instance wantedOrdinaryModulePreadditive (R : TopCat.Sheaf RingCat.{0} X) :
    Preadditive (OrdinaryModule X R) := Abelian.toPreadditive

theorem_wanted actual_beta_modules_exact (R : TopCat.Sheaf RingCat.{0} X)
    [BetaRingSource X R] (N : OrdinaryBetaModuleSource X R) (S : BetaUnitNormalizationSource X R)
    [(betaUnitModules X R N S).Additive] : ExactImageSource (betaUnitModules X R N S)

end OrdinaryBetaExact

theorem_wanted actual_ind_coefficients_exact (R S : Mon (IndSheaf ℂ X))
    [(Bimod.forget (B := S) R).Additive] : ExactCoefficientSource R S

theorem_wanted actual_ind_coefficients_bounded (R S : Mon (IndSheaf ℂ X))
    [(Bimod.forget (B := S) R).Additive] (E : ExactCoefficientSource R S) :
  BoundedCoefficientSource R S E

theorem_wanted actual_source_alpha_exact
    [(IndSheafAlphaBetaModels.alpha ℂ X C.alpha).Additive] : ExactAlphaSource ℂ X C.alpha

variable (M : Type) [TopologicalSpace M]
  [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]
  [HasSheafify (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)]
  [CompactSheafSource ℂ (TopCat.of M)]

local instance wantedManifoldIndPreadditive : Preadditive (IndSheaf ℂ (TopCat.of M)) :=
  Abelian.toPreadditive

variable [IndSpaceSource (TopCat.of M)]

def_wanted actual_differential_beta_ring
    (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} ℂ) : DifferentialBetaSource M O

def_wanted actual_opposite_differential_beta_ring
    (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} ℂ) : OppositeDifferentialBetaSource M O

variable [∀ Z : TopCat.{0}, HasSheafify (Opens.grothendieckTopology Z) (ModuleCat.{0} ℂ)]
  (n : ℕ) [ChartedSpace (TemperedDistributionSectionModels.ComplexCoordinates n) M]
  [IsManifold 𝓘(ℂ, TemperedDistributionSectionModels.ComplexCoordinates n) ∞ M]
  [HolomorphicCoefficientSheaves.SheafCondition
    (TemperedDistributionSectionModels.ComplexCoordinates n) M]
  [DifferentialBetaSource M (analyticCoefficients n M)]
  [DifferentialBetaSource M (analyticConjugateCoefficients n M)]
  [OppositeDifferentialBetaSource M (analyticConjugateCoefficients n M)]

def_wanted actual_conjugate_structure_module : ConjugateStructureModuleSource n M

def_wanted actual_native_tempered_distribution_source [T2Space M] [LocallyCompactSpace M]
    [SecondCountableTopology M] : NativeTemperedSourcePacket n M

/-- The canonical identification of the coefficient sheaves of the conjugate opposite
differential ring and the conjugate differential ring. -/
def_wanted actual_conjugate_canonical_carrier :
  CanonicalOppositeRings.CanonicalOppositeCarrier M (analyticConjugateCoefficients n M)

/-- The opposite monoid structure whose carrier is the β-image of the canonical carrier. -/
def_wanted actual_conjugate_opposite_ring
    (c : CanonicalOppositeRings.CanonicalOppositeCarrier M (analyticConjugateCoefficients n M)) :
  {RO : OppositeMonoidSource (Dbar n M) (DbarOp n M) // CanonicalOppositeRings.IsCanonicalOpposite c RO}

def_wanted actual_coefficient_opposite_ring : OppositeMonoidSource (K M) (K M)

end WantedExt.AlgebraicGeometry.NativeAnalyticIndConstructionWanted
