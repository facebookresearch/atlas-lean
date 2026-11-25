/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ExpansionParameterModels

/-!
# Actual standard families of relative expansions

The m-parameter standard model is built recursively from the original
pair by the actual blowup of the preceding model times A1 along its
boundary at parameter zero. Its distinguished divisor is the schematic
closure of the prescribed boundary away from that zero parameter.
The central fibre is compared with the actual ruled quotient chain.

Thus arbitrary families with a similar closed fibre are not substituted
for Jun Li's standard expansion. Parameter maps, contractions, boundary
maps and both universal properties are literal native scheme maps.
Source: Jun Li arXiv:math/0009097v1, Section 4.1, printed pp39--40.
Generic blowup properties are completed AxiomMath/Stacks source; native
carrier assembly remains a construction request.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.StandardRelativeExpansionModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry
open _root_.CategoryTheory.CartesianMonoidalCategory _root_.CategoryTheory.MonObj
open ExpandedTargetChainGeometry ExpansionParameterModels CartierIdealModels
open RelativeProjectiveLineModels

variable {k : Type} [Field k]

structure BlowupAlong (Y : Over (Spec (.of k))) (I : Y.left.IdealSheafData) where
  scheme : Over (Spec (.of k))
  map : scheme ⟶ Y
  proper : IsProper map.left
  cartier : IsEffectiveCartier (I.comap map.left)
  universal : ∀ (T : Over (Spec (.of k))) (f : T ⟶ Y),
    IsEffectiveCartier (I.comap f.left) → ∃! g : T ⟶ scheme, g ≫ map = f

variable (P : RelativePair (k := k))

structure StandardChart (m : ℕ) where
  scheme : Over (Spec (.of k))
  projection : scheme ⟶ ParameterSpace k m
  contraction : scheme ⟶ prod P.target (ParameterSpace k m)
  projection_eq : contraction ≫ prod.snd = projection
  boundary : prod P.divisor (ParameterSpace k m) ⟶ scheme
  [boundary_closed : IsClosedImmersion boundary.left]
  boundary_cartier : IsEffectiveCartier boundary.left.ker
  boundary_contraction : boundary ≫ contraction = prod.map P.inclusion (𝟙 _)

attribute [instance] StandardChart.boundary_closed

def centerMap {m : ℕ} (U : StandardChart P m) :
    prod P.divisor (ParameterSpace k m) ⟶ prod U.scheme (affineLine k) :=
  prod.lift U.boundary (toUnit _ ≫ zeroPoint k)

def boundaryBeforeMap {m : ℕ} (U : StandardChart P m) :
    prod P.divisor (lastParameterOpen k m) ⟶ prod U.scheme (affineLine k) :=
  prod.lift
    (prod.map (𝟙 P.divisor)
      (lastOpenInclusion k m ≫ (prod.fst : ParameterSpace k (m + 1) ⟶ ParameterSpace k m)) ≫
        U.boundary)
    ((prod.snd : prod P.divisor (lastParameterOpen k m) ⟶ lastParameterOpen k m) ≫
      lastOpenInclusion k m ≫ (prod.snd : ParameterSpace k (m + 1) ⟶ affineLine k))

/-- The actual blowup and schematic strict-transform normalization at one step. -/
structure StandardStep {m : ℕ} (U : StandardChart P m) (V : StandardChart P (m + 1)) where
  blowup : BlowupAlong (prod U.scheme (affineLine k)) (centerMap P U).left.ker
  identifies : V.scheme ≅ blowup.scheme
  projection : identifies.hom ≫ blowup.map ≫ prod.map U.projection (𝟙 (affineLine k)) = V.projection
  contraction : identifies.hom ≫ blowup.map ≫ prod.map U.contraction (𝟙 (affineLine k)) ≫
    (prod.associator P.target (ParameterSpace k m) (affineLine k)).hom = V.contraction
  boundary_open :
    (prod.map (𝟙 P.divisor) (lastOpenInclusion k m) ≫ V.boundary) ≫
      identifies.hom ≫ blowup.map = boundaryBeforeMap P U
  strict_transform : V.boundary.left.ker =
    (prod.map (𝟙 P.divisor) (lastOpenInclusion k m) ≫ V.boundary).left.ker

variable (R : ProjectiveLine P.divisor.left (normalLineModule P))

/-- All standard models, with their defining blowups and actual special fibres. -/
structure StandardSystem where
  chart : ∀ m : ℕ, StandardChart P m
  seed : (chart 0).scheme ≅ P.target
  seed_contraction : seed.hom = (chart 0).contraction ≫ prod.fst
  seed_boundary : (chart 0).boundary ≫ seed.hom =
    (prod.fst : prod P.divisor (ParameterSpace k 0) ⟶ P.divisor) ≫ P.inclusion
  step : ∀ m : ℕ, StandardStep P (chart m) (chart (m + 1))
  fibre : ∀ m : ℕ, ExpandedSpecialFibre P R m
  fibre_comparison : ∀ m : ℕ, (fibre m).scheme ≅ pullback (chart m).projection (origin k m)
  fibre_contraction : ∀ m : ℕ,
    (fibre_comparison m).hom ≫ pullback.fst (chart m).projection (origin k m) ≫
      (chart m).contraction ≫ prod.fst = (fibre m).contraction
  fibre_boundary : ∀ m : ℕ,
    (fibre m).boundary ≫ (fibre_comparison m).hom ≫
      pullback.fst (chart m).projection (origin k m) =
    prod.lift (𝟙 P.divisor) (toUnit P.divisor ≫ origin k m) ≫ (chart m).boundary

end MathlibExt.AlgebraicGeometry.StandardRelativeExpansionModels
