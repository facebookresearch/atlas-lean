/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`TauCeti/Geometry/Hodge/Conjugation.lean`, `TauCeti/Geometry/Hodge/Structure.lean`,
`TauCeti/Geometry/Hodge/Mixed/Basic.lean` and
`TauCeti/Geometry/Hodge/Mixed/Bigrading.lean` in
https://github.com/TauCetiProject/TauCeti
at commit 62bbc0596dc3539d488232e4e924a338548ea0a9:
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Tau Ceti contributors

Modification notice: specialized the arithmetic carrier to finite-dimensional
rational vector spaces, retained an actual complex base-change map and its
conjugation, and used the source's proved bigrading characterization as the
mixed definition. No geometric realization or category-existence theorem is
assumed here.
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom

/-!
# Rational pure and mixed Hodge data

The rational carrier is a finite-dimensional rational vector space, and the
complex carrier is a genuine base change of it along a rational linear map.
Conjugation fixes its rational image. Mixed purity is expressed by the
opposed-bigrading characterization proved in the TauCeti source, including
recovery of both filtrations and conjugation modulo lower weight. A bare
existence of an unrelated Hodge structure on graded pieces would lose that
link.

These are completed definitions; the geometry producing them is requested
separately. Sources: P. Deligne, *Théorie de Hodge II*, §§1.2 and 2.3;
C. Peters and J. Steenbrink, *Mixed Hodge Structures*, Chapter 3.
-/

@[expose] public noncomputable section

namespace MathlibExt.Geometry.RationalHodgeStructures

open CategoryTheory

/-- A genuine complexification of the given finite-dimensional rational vector
space with the rationally induced conjugation. Rational Hodge structures live on
finite-dimensional rational vector spaces. -/
structure RationalComplexification (V : ModuleCat.{0} ℚ) where
  /-- The rational carrier is finite-dimensional. -/
  [finiteDimensional : FiniteDimensional ℚ V]
  /-- The complex vector space. -/
  complexSpace : ModuleCat.{0} ℂ
  /-- Its rational structure, restricted from the complex one. -/
  [ratModule : Module ℚ complexSpace]
  /-- The rational and complex scalar actions are compatible. -/
  [isScalarTower : IsScalarTower ℚ ℂ complexSpace]
  /-- The rational comparison map from the rational carrier. -/
  comparisonMap : V →ₗ[ℚ] complexSpace
  /-- It exhibits the complex space as the base change `ℂ ⊗[ℚ] V`. -/
  baseChange : IsBaseChange ℂ comparisonMap
  /-- The complex conjugation. -/
  conjugation : complexSpace ≃ₛₗ[starRingEnd ℂ] complexSpace
  /-- Conjugation is an involution. -/
  involutive : Function.Involutive conjugation
  /-- Conjugation fixes the rational image. -/
  rational_fixed : ∀ v, conjugation (comparisonMap v) = comparisonMap v

attribute [instance] RationalComplexification.ratModule
  RationalComplexification.isScalarTower

/-- Complexification of a rational subspace through the fixed comparison map. -/
def complexifiedSubspace {V : ModuleCat.{0} ℚ} (C : RationalComplexification V)
    (U : Submodule ℚ V) : Submodule ℂ C.complexSpace :=
  Submodule.span ℂ (C.comparisonMap '' (U : Set V))

/-- The bounded opposed-filtration definition of a pure Hodge structure. -/
structure PureHodgeStructure {V : ModuleCat.{0} ℚ} (C : RationalComplexification V)
    (w : ℤ) where
  F : ℤ → Submodule ℂ C.complexSpace
  antitone : Antitone F
  exhaustive : ∃ p, F p = ⊤
  opposed : ∀ p, IsCompl (F p) ((F (w + 1 - p)).map C.conjugation.toLinearMap)

/-- A Hodge bigrading recovering the actual rational weight and complex
Hodge filtrations, with conjugation modulo the actual lower weight space. -/
structure IsHodgeBigrading {V : ModuleCat.{0} ℚ} (C : RationalComplexification V)
    (W : ℤ → Submodule ℚ V) (F : ℤ → Submodule ℂ C.complexSpace)
    (I : ℤ × ℤ → Submodule ℂ C.complexSpace) : Prop where
  independent : iSupIndep I
  weight : ∀ k, complexifiedSubspace C (W k) =
    ⨆ (pq : ℤ × ℤ) (_ : pq.1 + pq.2 ≤ k), I pq
  hodge : ∀ p, F p = ⨆ (pq : ℤ × ℤ) (_ : p ≤ pq.1), I pq
  conjugate_lower : ∀ pq,
    (I pq).map C.conjugation.toLinearMap ≤
      I pq.swap ⊔ complexifiedSubspace C (W (pq.1 + pq.2 - 1))

/-- Rational mixed Hodge data, using the source's bigrading-equivalent
definition of graded purity rather than an arbitrary named predicate. -/
structure MixedHodgeStructure {V : ModuleCat.{0} ℚ} (C : RationalComplexification V) where
  W : ℤ → Submodule ℚ V
  monotone : Monotone W
  W_top : ∃ k, W k = ⊤
  W_bot : ∃ k, W k = ⊥
  F : ℤ → Submodule ℂ C.complexSpace
  antitone : Antitone F
  F_top : ∃ p, F p = ⊤
  F_bot : ∃ p, F p = ⊥
  bigrading : ∃ I : ℤ × ℤ → Submodule ℂ C.complexSpace, IsHodgeBigrading C W F I

/-- A mixed Hodge morphism is an actual rational map with its compatible
complexification, preserving the two fixed filtrations. -/
structure MixedHodgeMap {V V' : ModuleCat.{0} ℚ}
    {C : RationalComplexification V} {C' : RationalComplexification V'}
    (H : MixedHodgeStructure C) (H' : MixedHodgeStructure C') where
  rationalMap : V →ₗ[ℚ] V'
  complexMap : C.complexSpace →ₗ[ℂ] C'.complexSpace
  comparison : ∀ v, complexMap (C.comparisonMap v) = C'.comparisonMap (rationalMap v)
  weights : ∀ k, (H.W k).map rationalMap ≤ H'.W k
  hodge : ∀ p, (H.F p).map complexMap ≤ H'.F p

/-- Identity maps preserve all comparison and filtration data. -/
def MixedHodgeMap.id {V : ModuleCat.{0} ℚ} {C : RationalComplexification V}
    (H : MixedHodgeStructure C) : MixedHodgeMap H H where
  rationalMap := LinearMap.id
  complexMap := LinearMap.id
  comparison := by intro v; rfl
  weights := by intro k; simp
  hodge := by intro p; simp

/-- Composition is composition of the actual realization maps. -/
def MixedHodgeMap.comp {V V' V'' : ModuleCat.{0} ℚ}
    {C : RationalComplexification V} {C' : RationalComplexification V'}
    {C'' : RationalComplexification V''}
    {H : MixedHodgeStructure C} {H' : MixedHodgeStructure C'} {H'' : MixedHodgeStructure C''}
    (g : MixedHodgeMap H' H'') (f : MixedHodgeMap H H') : MixedHodgeMap H H'' where
  rationalMap := g.rationalMap.comp f.rationalMap
  complexMap := g.complexMap.comp f.complexMap
  comparison := by intro v; simp only [LinearMap.comp_apply, f.comparison, g.comparison]
  weights := by
    intro k
    rw [Submodule.map_comp]
    exact (Submodule.map_mono (f.weights k)).trans (g.weights k)
  hodge := by
    intro p
    rw [Submodule.map_comp]
    exact (Submodule.map_mono (f.hodge p)).trans (g.hodge p)

end MathlibExt.Geometry.RationalHodgeStructures
