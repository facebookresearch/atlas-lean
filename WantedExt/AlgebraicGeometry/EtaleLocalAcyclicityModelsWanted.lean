/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.EtaleLocalAcyclicityModels

/-!
# Native strict-local, finite-coefficient and microsupport construction requests

All geometric limits, Milnor fibres, derived restriction units and
specialization arrows are fixed in MathlibExt. The finite-coefficient
toolbox provides ordinary closed-stalk and inverse-image comparisons;
it contains no local-acyclicity or singular-support theorem. Vanishing
models represent the actual specialization, and singular support is its
smallest cotangent microsupport.

Sources: Beilinson, arXiv:1505.06768v8, Sections 1.1--1.3, Theorem 1.3(i);
Saito, arXiv:1510.03018v4, Section 1.1; Bhatt--Scholze, arXiv:1309.1198,
finite discrete étale/pro-étale coefficients. The source general
derived-functor and strict-localization constructions are integration
inputs; these requests do not claim that their mathematics is absent.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.EtaleLocalAcyclicityModelsWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry
open AdicDerivedContracts FiniteEtaleConstructibleModels
open CotangentBundleTestModels CotangentTransversalTests
open EtaleStrictLocalizationModels EtaleLocalAcyclicityModels

def_wanted nativeStrictLocalizationSystem : StrictLocalizationSystem

def_wanted nativeFiniteConstructibleTheory (Λ k : Type) [CommRing Λ]
    [Finite Λ] [IsLocalRing Λ] [Field k]
    (ell m : ℕ) [Fact ell.Prime] [CharP Λ (ell ^ m)]
    (positive : 0 < m) (invertible : (ell : k) ≠ 0) [DerivedFunctorTheory Λ] :
    ConstructibleTheory Λ k

def_wanted nativeVanishingModel (Λ : Type) [CommRing Λ] [DerivedFunctorTheory Λ]
    (X Y : Scheme.{0}) (f : X ⟶ Y) (Ω : GeometricField)
    (x : Spec (.of Ω.carrier) ⟶ X) (K : Derived Λ X)
    (LX : StrictLocalization Ω x) (LY : StrictLocalization Ω (x ≫ f))
    (M : LocalMorphism Ω x f LX LY) (t : Generization Ω x f LY)
    [IsIso (closedStalkArrow Λ Ω x LX K)] : VanishingModel Λ Ω x K f LX LY M t

def_wanted nativeSingularSupport (Λ k : Type) [CommRing Λ]
    [Finite Λ] [IsLocalRing Λ] [Field k]
    (ell m : ℕ) [Fact ell.Prime] [CharP Λ (ell ^ m)]
    (positive : 0 < m) (invertible : (ell : k) ≠ 0) [DerivedFunctorTheory Λ]
    (G : StrictLocalizationSystem) (T : ConstructibleTheory Λ k)
    (X : Over (Spec (.of k))) [Smooth X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (BX : CotangentBundle X) (K : Derived Λ X.left)
    (constructible : IsBoundedConstructible Λ k X K) :
    {C : ClosedCone X BX // IsSingularSupport Λ k G T X C K constructible}

private def check_nativeStrictLocalizationSystem : DefWanted StrictLocalizationSystem :=
  nativeStrictLocalizationSystem

private def check_nativeFiniteConstructibleTheory (Λ k : Type) [CommRing Λ]
    [Finite Λ] [IsLocalRing Λ] [Field k]
    (ell m : ℕ) [Fact ell.Prime] [CharP Λ (ell ^ m)]
    (positive : 0 < m) (invertible : (ell : k) ≠ 0) [DerivedFunctorTheory Λ] :
    DefWanted (ConstructibleTheory Λ k) :=
  nativeFiniteConstructibleTheory Λ k ell m positive invertible

private def check_nativeVanishingModel (Λ : Type) [CommRing Λ] [DerivedFunctorTheory Λ]
    (X Y : Scheme.{0}) (f : X ⟶ Y) (Ω : GeometricField)
    (x : Spec (.of Ω.carrier) ⟶ X) (K : Derived Λ X)
    (LX : StrictLocalization Ω x) (LY : StrictLocalization Ω (x ≫ f))
    (M : LocalMorphism Ω x f LX LY) (t : Generization Ω x f LY)
    [IsIso (closedStalkArrow Λ Ω x LX K)] :
    DefWanted (VanishingModel Λ Ω x K f LX LY M t) :=
  nativeVanishingModel Λ X Y f Ω x K LX LY M t

private def check_nativeSingularSupport (Λ k : Type) [CommRing Λ]
    [Finite Λ] [IsLocalRing Λ] [Field k]
    (ell m : ℕ) [Fact ell.Prime] [CharP Λ (ell ^ m)]
    (positive : 0 < m) (invertible : (ell : k) ≠ 0) [DerivedFunctorTheory Λ]
    (G : StrictLocalizationSystem) (T : ConstructibleTheory Λ k)
    (X : Over (Spec (.of k))) [Smooth X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (BX : CotangentBundle X) (K : Derived Λ X.left)
    (constructible : IsBoundedConstructible Λ k X K) :
    DefWanted {C : ClosedCone X BX // IsSingularSupport Λ k G T X C K constructible} :=
  nativeSingularSupport Λ k ell m positive invertible G T X BX K constructible

end WantedExt.AlgebraicGeometry.EtaleLocalAcyclicityModelsWanted
