/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.GeneralEtaleCoherentFamilies
public import MathlibExt.AlgebraicGeometry.FrobeniusPerfectionModels

/-!
# Full coherent coefficient and affine Frobenius source goals

The raw coefficient family fixes every source object, inverse-image
functor and native unit/composition mate. Its full categorical
localization inverts actual vertical coefficient quasi-isomorphisms,
retaining all noninvertible categorical parameter maps. Constructible
base change is an output condition, never an arc descent input.

Frobenius is the actual natural r -> r^p endomorphism on every F_p-algebra,
including the zero ring. Native affine perfection already takes its
DIRECT colimit. Global qcqs perfection/gluing, full Perf normalization
and hypercomplete arc descent remain separate required interfaces.

Source: Bhatt--Mathew arXiv:1807.04725v4, Notation5.8, Theorems5.13/5.16;
native Mathlib adjunction/Grothendieck/coherent section constructions.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CoherentEtalePerfectionSourcesWanted

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open GeneralEtaleCoefficientModels GeneralEtalePullbackCoherence
open GeneralEtaleCoherentFamilies FrobeniusPerfectionModels
open MathlibExt.AlgebraicTopology.CategoricalCocartesianSections

def_wanted fp_frobenius (p : ℕ) (hp : p.Prime) : FrobeniusSource p

variable (Λ : Type) [Ring Λ]
  [∀ X : Scheme.{0}, HasSheafify X.smallEtaleTopology (ModuleCat.{1} Λ)]
  (S : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y), EtalePullbackSource Λ f)
  (U : ∀ X : Scheme.{0}, EtaleComplexesPullbackCoherence.EtaleBaseChangeUnitSource X)

def_wanted native_coefficient_pseudofunctor : CoefficientPseudofunctorSource Λ S U

variable (C : CoefficientPseudofunctorSource Λ S U)

def_wanted coherent_derived_family : DerivedCoefficientFamily Λ S U C

theorem_wanted constructible_cocartesian (D : DerivedCoefficientFamily Λ S U C) :
    CocartesianFibration (constructibleProjection Λ S U C D)

end WantedExt.AlgebraicGeometry.CoherentEtalePerfectionSourcesWanted
