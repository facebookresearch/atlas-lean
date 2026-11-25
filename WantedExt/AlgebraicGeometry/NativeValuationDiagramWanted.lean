/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.NativeValuationDiagramModels

/-!
# Full source valuation excision for coefficients and perfected Perf

All four actual rings, every quotient/localization/residue arrow,
categorical section limit and native comparison are fixed first.
Absolutely integrally closed valuation rings are tested in all ranks:
their fraction fields are algebraically closed. Finite coefficient
rings need not be commutative. Descent is the output.
The valuation theorems explicitly retain the finite-ring assumption
fixed before Notation5.8. Generic initial/diagram source constructors
retain their all-ring construction scope.

Sources: Bhatt--Mathew1807.04725v4, Theorem4.1 and the valuation
squares in the proofs of Theorems5.13/5.16.
-/

set_option autoImplicit false
@[expose] public section

namespace MathlibExt.AlgebraicGeometry.NativeValuationDiagramModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open GeneralArcCoverModels GeneralEtaleCoefficientModels GeneralEtalePullbackCoherence
open GeneralEtaleCoherentFamilies GeneralCoefficientHyperdescentModels
open FrobeniusPerfectionModels GlobalFpPerfectionModels GlobalPerfectedPerfModels
open OrdinarySchemeTorModels OrdinaryConstantCoefficientModels
open MathlibExt.AlgebraicTopology.NativeInitialSectionModels
open MathlibExt.AlgebraicTopology.QuasicategoricalModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle

section Coefficients
variable (Λ : Type) [Ring Λ] [Finite Λ]
  [∀ Y : Scheme.{0}, HasSheafify Y.smallEtaleTopology (ModuleCat.{1} Λ)]
  (S : ∀ {Y Z : Scheme.{0}} (f : Y ⟶ Z), EtalePullbackSource Λ f)
  (U : ∀ Y : Scheme.{0}, EtaleComplexesPullbackCoherence.EtaleBaseChangeUnitSource Y)
  (C : CoefficientPseudofunctorSource Λ S U) (D : DerivedCoefficientFamily Λ S U C)

/-- **Evaluating constructible sections at the cone point of a diagram.** Let $\Lambda$ be a finite
ring, not necessarily commutative, with sheafification of étale sheaves of $\Lambda$-modules on
every scheme and the given étale coefficient data `S`, `U`, `C` and `D`. For a small category $J$,
a qcqs scheme $X$ and a diagram $H$ of schemes over $X$ indexed by $J$: an equivalence, in the sense
of `InitialSectionComparison`, between the sections of the family of constructible complexes over
the augmented diagram (that of $H$ with $X$ adjoined as cone point) and the fibre of this family
at $X$. It consists of the evaluation at the cone point, normalized by the section value there, an
inverse map, natural equivalences between both composites and the identities, and the fact that
the evaluation is a categorical weak equivalence. -/
def_wanted native_constructible_diagram_source {J : Type} [Category.{0} J] {X : QcqsScheme}
    (H : J ⥤ Over X) :
  InitialSectionComparison (constructibleProjection Λ S U C D)
    (augmentedCoefficientBase H) coefficientAugmentationVertex

def_wanted native_amplitude_diagram_source {J : Type} [Category.{0} J] {X : QcqsScheme}
    (H : J ⥤ Over X) (n : ℕ) :
  InitialSectionComparison (amplitudeProjection Λ S U C D n)
    (augmentedCoefficientBase H) coefficientAugmentationVertex

variable
  (V : ValuationRingData) [IsAlgClosed (FractionRing V.ring)]
  (p : PrimeSpectrum V.ring) (E : ValuationExcision V p)

theorem_wanted constructible_valuation_excision [Finite Λ]
    (I : InitialSectionComparison (constructibleProjection Λ S U C D)
      (augmentedCoefficientBase (excisionSpan V p E)) coefficientAugmentationVertex) :
  CategoricalWeakEquivalence
    (coefficientDiagramComparison (excisionSpan V p E) (constructibleProjection Λ S U C D) I)

theorem_wanted amplitude_valuation_excision [Finite Λ] (n : ℕ)
    (I : InitialSectionComparison (amplitudeProjection Λ S U C D n)
      (augmentedCoefficientBase (excisionSpan V p E)) coefficientAugmentationVertex) :
  CategoricalWeakEquivalence
    (coefficientDiagramComparison (excisionSpan V p E) (amplitudeProjection Λ S U C D n) I)

end Coefficients

section Perfected
variable {ℓ : ℕ} {F : FrobeniusSource ℓ} (G : GlobalPerfectionSource F)
  {N : ShuffleAlgebraFunctor ℤ} {S : AffineScalarSystem N} (M : AffineModuleFibration N S)
  (V : ValuationRingData) [IsAlgClosed (FractionRing V.ring)]
  (p : PrimeSpectrum V.ring) (E : ValuationExcision V p)
  (b : ZMod ℓ →+* V.ring)

theorem_wanted perfected_perf_valuation_excision :
  CategoricalWeakEquivalence
    (perfectedComparison (X := valuationFpScheme V b) (excisionSpan V p E) G M)

theorem_wanted perfected_tor_valuation_excision (T : OrdinaryTorSystem N) (n : ℕ)
    (I : TorComparison M T
      (perfectedDiagram (X := valuationFpScheme V b) (excisionSpan V p E) G)
      (-(n : ℤ)) (n : ℤ)) :
  CategoricalWeakEquivalence I.map

end Perfected

end MathlibExt.AlgebraicGeometry.NativeValuationDiagramModels
