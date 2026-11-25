/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.NativeEtaleDerivedFibreModels

/-!
# Native full K-injective coefficient fibre construction

Every source complex, homogeneous Hom, native replacement map and
whole augmentation comparison is fixed. The actual derived-family
fibre map uses those original source operators. Hyperdescent is not
part of these generic construction hypotheses or conclusions.

Sources: Keller Section2; HA Section1.3.1; Bhatt--Mathew1807.04725v4,
Notation5.8.
-/

set_option autoImplicit false
@[expose] public section

namespace MathlibExt.AlgebraicGeometry.NativeEtaleDerivedFibreModels

open _root_.CategoryTheory _root_.AlgebraicGeometry
open GeneralArcCoverModels GeneralEtaleCoefficientModels GeneralEtalePullbackCoherence
open GeneralEtaleCoherentFamilies NativeEtaleCoefficientSourceModels

variable (Λ : Type) [Ring Λ]
  [∀ Y : Scheme.{0}, HasSheafify Y.smallEtaleTopology (ModuleCat.{1} Λ)]
  (X : QcqsScheme) (N : CoefficientDGOrdinarySource Λ X.scheme)
  (F : CoefficientSimplicialFunctorSource Λ X.scheme N)

/-- Native K-injective replacement retains its entire actual coefficient-source functor. -/
def_wanted native_coefficient_kinjective_resolution : KInjectiveResolutionSource Λ X N F

/-- The full native K-injective DG model realizes the whole ordinary quasi-isomorphism localization. -/
theorem_wanted native_coefficient_kinjective_localization (R : KInjectiveResolutionSource Λ X N F) :
  KInjectiveLocalizationSource Λ X N F R

/-- The actual whole native augmentation identifies this full K-injective model with the original derived-family fibre. -/
def_wanted native_coefficient_fibre_comparison
    (S : ∀ {Y Z : Scheme.{0}} (f : Y ⟶ Z), EtalePullbackSource Λ f)
    (U : ∀ Y : Scheme.{0}, EtaleComplexesPullbackCoherence.EtaleBaseChangeUnitSource Y)
    (C : CoefficientPseudofunctorSource Λ S U) (D : DerivedCoefficientFamily Λ S U C)
    (E : CoefficientFibreEntrySource Λ S U C X)
    (R : KInjectiveResolutionSource Λ X N F) : CoefficientFibreComparison Λ X N F S U C D E R

end MathlibExt.AlgebraicGeometry.NativeEtaleDerivedFibreModels
