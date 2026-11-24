/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.GeneralCoefficientHyperdescentModels

/-!
# Hypercomplete arc descent of the actual enhanced coefficient categories

The comparison map is the independently constructed native initial
evaluation inverse followed by actual section restriction. Hypercovers
test every native relative matching map. The theorem conclusions are
categorical weak equivalences on the original full coefficient families.

Source: Bhatt--Mathew1807.04725v4, Theorem5.13.
-/

set_option autoImplicit false
@[expose] public section

namespace MathlibExt.AlgebraicGeometry.GeneralCoefficientHyperdescentModels

open _root_.CategoryTheory
open GeneralArcCoverModels GeneralArcHypercoverModels GeneralEtaleCoherentFamilies
open GeneralEtaleCoefficientModels GeneralEtalePullbackCoherence
open MathlibExt.AlgebraicTopology.QuasicategoricalModels
open MathlibExt.AlgebraicTopology.CategoricalCocartesianSections

variable (Λ : Type) [Ring Λ]
  [∀ Y : _root_.AlgebraicGeometry.Scheme.{0},
    HasSheafify Y.smallEtaleTopology (ModuleCat.{1} Λ)]
  (S : ∀ {Y Z : _root_.AlgebraicGeometry.Scheme.{0}} (f : Y ⟶ Z), EtalePullbackSource Λ f)
  (U : ∀ Y : _root_.AlgebraicGeometry.Scheme.{0},
    EtaleComplexesPullbackCoherence.EtaleBaseChangeUnitSource Y)
  (C : CoefficientPseudofunctorSource Λ S U) (D : DerivedCoefficientFamily Λ S U C)

/-- The same native fixed-amplitude family has all actual cocartesian transports. -/
theorem_wanted native_amplitude_cocartesian (n : ℕ) :
  CocartesianFibration (amplitudeProjection Λ S U C D n)

/-- The generic native initial-index comparison is constructed before assuming any arc-cover condition. -/
def_wanted native_constructible_hypercover_comparison {X : QcqsScheme}
    (H : SimplicialObject (Over X)) :
    HypercoverComparisonSource H (constructibleProjection Λ S U C D)

/-- Its fixed-amplitude counterpart uses the same actual initial evaluation. -/
def_wanted native_amplitude_hypercover_comparison {X : QcqsScheme}
    (H : SimplicialObject (Over X)) (n : ℕ) :
    HypercoverComparisonSource H (amplitudeProjection Λ S U C D n)

/-- Theorem5.13 is a full categorical equivalence on every actual arc hypercover. -/
theorem_wanted constructible_arc_hyperdescent [Finite Λ] {X : QcqsScheme}
    (H : SimplicialObject (Over X)) [∀ m : ℕ, CategoryTheory.Limits.HasLimit (matchingDiagram H m)]
    (h : IsArcHypercover H)
    (I : HypercoverComparisonSource H (constructibleProjection Λ S U C D)) :
    CategoricalWeakEquivalence (constructibleComparison H Λ S U C D I)

/-- The source's symmetric fixed-amplitude categories satisfy the same hypercomplete arc descent. -/
theorem_wanted amplitude_arc_hyperdescent [Finite Λ] {X : QcqsScheme}
    (H : SimplicialObject (Over X)) [∀ m : ℕ, CategoryTheory.Limits.HasLimit (matchingDiagram H m)]
    (h : IsArcHypercover H) (n : ℕ)
    (I : HypercoverComparisonSource H (amplitudeProjection Λ S U C D n)) :
    CategoricalWeakEquivalence (amplitudeComparison H Λ S U C D n I)

end MathlibExt.AlgebraicGeometry.GeneralCoefficientHyperdescentModels
