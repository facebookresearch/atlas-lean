/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.GeneralEtaleDerivedEnhancements

/-!
# General left-module étale source construction requests

The coefficient ring is any Ring, including noncommutative rings. All
schemes and native étale base-change/left-adjoint functors retain their
actual module action and all shifted cochains. These are generic source
constructors/proofs; no arc or constructible hyperdescent is an input.

Sources: Bhatt--Mathew arXiv:1807.04725v4, Notation 5.8 and Theorem 5.13;
Stacks Project, Tags 03Q4 and 09YU; native Mathlib site/derived primitives.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.GeneralEtaleCoefficientSourcesWanted

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open GeneralArcCoverModels GeneralEtaleCoefficientModels

theorem_wanted etale_module_sheafification (Λ : Type) [Ring Λ] :
    ∀ X : Scheme.{0}, HasSheafify X.smallEtaleTopology (ModuleCat.{1} Λ)

variable (Λ : Type) [Ring Λ]
  [∀ X : Scheme.{0}, HasSheafify X.smallEtaleTopology (ModuleCat.{1} Λ)]

def_wanted etale_pullback_source (X Y : Scheme.{0}) (f : X ⟶ Y) : EtalePullbackSource Λ f

theorem_wanted etale_pullback_exact (X Y : Scheme.{0}) (f : X ⟶ Y)
    (S : EtalePullbackSource Λ f) : IsExactPullback Λ S

def_wanted valuation_excision (V : ValuationRingData) (p : PrimeSpectrum V.ring) :
    ValuationExcision V p

end WantedExt.AlgebraicGeometry.GeneralEtaleCoefficientSourcesWanted
