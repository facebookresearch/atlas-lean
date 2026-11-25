/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StandardRelativeExpansionModels
public import MathlibExt.AlgebraicGeometry.LinearizedLineBundles

/-!
# Actual scaling actions on standard relative expansions

The torus and all of its coordinate units are fixed schemes/ring sections.
Parameter multiplication uses Jun Li's adjacent unit ratios. Contraction,
projection and distinguished boundary equivariance are equations of the
actual native scheme actions. No free scaling or quotient operation is
substituted for those maps.
Source: Jun Li arXiv:math/0009097v1, Equations (1.3),(4.1), Sections 1.2,4.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ExpansionScalingModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open ExpandedTargetChainGeometry StandardRelativeExpansionModels ExpansionParameterModels

variable {k : Type} [Field k]

def adjacentUnit {R : Type} [CommRing R] {m : ℕ} (u : Fin m → Rˣ) (i : Fin m) : Rˣ :=
  if h : i.val = 0 then u i else u i * (u ⟨i.val - 1, by omega⟩)⁻¹

def originalProductAction {G B : Over (Spec (.of k))} [GrpObj G] [ModObj G B]
    (Y : Over (Spec (.of k))) : G ⊗ prod Y B ⟶ prod Y B :=
  prod.lift (CartesianMonoidalCategory.snd G (prod Y B) ≫ prod.fst)
    ((G ◁ (prod.snd : prod Y B ⟶ B)) ≫ γ[G,B])

variable (P : RelativePair (k := k))
  (R : RelativeProjectiveLineModels.ProjectiveLine P.divisor.left (normalLineModule P))
  (S : StandardSystem P R) (m : ℕ) (H : TorusTheory k m)

structure ScalingData where
  parameter : letI := H.group; ModObj (torusScheme k m) (ParameterSpace k m)
  standard : letI := H.group; ModObj (torusScheme k m) (S.chart m).scheme
  coordinates : letI := H.group; letI := parameter;
    ∀ (T : Over (Spec (.of k))) (g : T ⟶ torusScheme k m) (t : T ⟶ ParameterSpace k m) (i : Fin m),
      (CartesianMonoidalCategory.lift g t ≫ γ[torusScheme k m,ParameterSpace k m]).left.appTop.hom
        (parameterCoordinate k m i) =
          (adjacentUnit (H.units T g) i : Γ(T.left, ⊤)) * t.left.appTop.hom (parameterCoordinate k m i)
  projection : letI := H.group; letI := parameter; letI := standard;
    γ[torusScheme k m,(S.chart m).scheme] ≫ (S.chart m).projection =
      (torusScheme k m ◁ (S.chart m).projection) ≫ γ[torusScheme k m,ParameterSpace k m]
  contraction : letI := H.group; letI := parameter; letI := standard;
    γ[torusScheme k m,(S.chart m).scheme] ≫ (S.chart m).contraction =
      (torusScheme k m ◁ (S.chart m).contraction) ≫ originalProductAction P.target
  boundary : letI := H.group; letI := parameter; letI := standard;
    originalProductAction P.divisor ≫ (S.chart m).boundary =
      (torusScheme k m ◁ (S.chart m).boundary) ≫ γ[torusScheme k m,(S.chart m).scheme]

end MathlibExt.AlgebraicGeometry.ExpansionScalingModels
