/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.MinimalFibration.ConnectedSimplexTriviality
public import MathlibExt.Topology.Category.TopCat.FixedFiberGauge

/-!
# Minimal-fibration fixed-fiber consumers

Public clients for simplex pullback triviality and the algebra of product
coordinate gauges, including the new-to-old transition orientation.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory Simplicial
open scoped Simplicial SSet.modelCategoryQuillen

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.MinimalFibrationFixedFiberTests

universe u

section MinimalFibration

variable {E A B E₀ E₁ : SSet.{u}}

example (p : E ⟶ B) (hp : SSet.MinimalFibration.IsMinimalFibration p)
    {f₀ f₁ : A ⟶ B} (H : SSet.Homotopy f₀ f₁)
    {p₀ : E₀ ⟶ A} {g₀ : E₀ ⟶ E} (sq₀ : IsPullback g₀ p₀ p f₀)
    {p₁ : E₁ ⟶ A} {g₁ : E₁ ⟶ E} (sq₁ : IsPullback g₁ p₁ p f₁) :
    ∃ e : E₀ ≅ E₁, e.hom ≫ p₁ = p₀ :=
  SSet.MinimalFibration.exists_iso_pullback_of_homotopy p hp H sq₀ sq₁

example {n : ℕ} (p : E ⟶ (Δ[n] : SSet.{u}))
    (hp : SSet.MinimalFibration.IsMinimalFibration p) :
    CategoryTheory.TrivialBundleWithFiber
      (pullback p
        (SSet.const (X := (Δ[0] : SSet.{u}))
          (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))))) p :=
  SSet.MinimalFibration.trivialBundleWithFiber_stdSimplex p hp

example (p : E ⟶ (Δ[0] : SSet.{u}))
    (hp : SSet.MinimalFibration.IsMinimalFibration p) :
    CategoryTheory.TrivialBundleWithFiber
      (pullback p
        (SSet.const (X := (Δ[0] : SSet.{u}))
          (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)))) p :=
  SSet.MinimalFibration.trivialBundleWithFiber_stdSimplex p hp

example (p : E ⟶ B) (hp : SSet.MinimalFibration.IsMinimalFibration p)
    [B.IsConnected] (b₀ : B.obj (Opposite.op ⦋0⦌))
    {n : ℕ} (σ : Δ[n] ⟶ B) :
    CategoryTheory.TrivialBundleWithFiber
      (pullback p (SSet.const (X := (Δ[0] : SSet.{u})) b₀))
      (pullback.snd p σ) :=
  SSet.MinimalFibration.trivialBundleWithFiber_pullback_stdSimplex p hp b₀ σ

end MinimalFibration

section Gauges

variable {B B' E F : TopCat.{u}} {p : E ⟶ B}

example (a : TopCat.FixedFiberGauge B F) :
    a.e.hom ≫ CartesianMonoidalCategory.fst B F =
      CartesianMonoidalCategory.fst B F :=
  a.hom_fst

example (a : TopCat.FixedFiberGauge B F) :
    a.e.inv ≫ CartesianMonoidalCategory.fst B F =
      CartesianMonoidalCategory.fst B F :=
  a.inv_fst

example (g : B' ⟶ B) (a : TopCat.FixedFiberGauge B F) :
    (TopCat.FixedFiberGauge.baseChange g a).e.hom ≫
        CartesianMonoidalCategory.fst B' F =
      CartesianMonoidalCategory.fst B' F :=
  (TopCat.FixedFiberGauge.baseChange g a).hom_fst

example (h : CategoryTheory.TrivialBundleWithFiber F p)
    (a : TopCat.FixedFiberGauge B F) :
    CategoryTheory.TrivialBundleWithFiber F p :=
  h.gauge a

example (h : CategoryTheory.TrivialBundleWithFiber F p)
    (a : TopCat.FixedFiberGauge B F) :
    (h.gauge a).r =
      CartesianMonoidalCategory.lift p h.r ≫ a.e.hom ≫
        CartesianMonoidalCategory.snd B F :=
  h.gauge_r a

example (h₀ h₁ : CategoryTheory.TrivialBundleWithFiber F p) :
    (h₀.transitionGauge h₁).e.hom =
      BinaryFan.IsLimit.lift h₁.isLimit
          (CartesianMonoidalCategory.fst B F)
          (CartesianMonoidalCategory.snd B F) ≫
        CartesianMonoidalCategory.lift p h₀.r :=
  h₀.transitionGauge_hom h₁

example (h₀ h₁ : CategoryTheory.TrivialBundleWithFiber F p) :
    h₁.gauge (h₀.transitionGauge h₁) = h₀ :=
  h₀.gauge_transition h₁

end Gauges

end MathlibExtTest.AlgebraicTopology.SimplicialSet.MinimalFibrationFixedFiberTests
