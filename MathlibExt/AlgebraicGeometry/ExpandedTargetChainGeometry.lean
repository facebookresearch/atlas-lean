/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeProjectiveLineModels
public import MathlibExt.AlgebraicGeometry.ProjectiveLineSystems

/-!
# Actual ruled chains in expanded relative targets

The pair is a smooth projective scheme with a genuine smooth Cartier
divisor. Its normal line is the computed dual of the native conormal
module. Each added component is P(O_D plus N_D/Y), with its actual
coordinate sections and inverse normal directions. The chain is the
scheme quotient identifying these exact boundary maps, with the full
universal property and contraction to the original target fixed.

This is the special-fibre geometry; variable-length expansion families
are the standard-model/base-change/descent layer, rather than constant
chains over arbitrary parameter schemes.
Source: Jun Li arXiv:math/0009097v1, Sections 1 and4, pp6 and39.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ExpandedTargetChainGeometry

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open CartierIdealModels NativeLineDuals RelativeProjectiveLineModels
open CoherentCurveLinearSeries

variable {k : Type} [Field k]

structure RelativePair where
  target : Over (Spec (.of k))
  divisor : Over (Spec (.of k))
  inclusion : divisor ⟶ target
  [closed : IsClosedImmersion inclusion.left]
  targetSmooth : Smooth target.hom
  targetProjective : ProjectiveSpace.IsProjective target
  divisorSmooth : Smooth divisor.hom
  divisorConnected : GeometricallyConnected divisor.hom
  cartier : IsEffectiveCartier inclusion.left.ker
  normal : SchemeNormalBundleMaps.NormalBundleModel inclusion.left 1
  normalLine : IsLineBundle (dualModule divisor.left normal.conormal)

attribute [instance] RelativePair.closed

def normalLineModule (P : RelativePair (k := k)) : P.divisor.left.Modules :=
  dualModule P.divisor.left P.normal.conormal

variable (P : RelativePair (k := k))
  (R : ProjectiveLine P.divisor.left (normalLineModule P))

def ruledScheme : Over (Spec (.of k)) := Over.mk (R.projection ≫ P.divisor.hom)

def ruledZero : P.divisor ⟶ ruledScheme P R :=
  Over.homMk R.zero (by
    change R.zero ≫ (R.projection ≫ P.divisor.hom) = P.divisor.hom
    rw [← Category.assoc, R.zero_over, Category.id_comp])

def ruledInfinity : P.divisor ⟶ ruledScheme P R :=
  Over.homMk R.infinity (by
    change R.infinity ≫ (R.projection ≫ P.divisor.hom) = P.divisor.hom
    rw [← Category.assoc, R.infinity_over, Category.id_comp])

def ruledContraction : ruledScheme P R ⟶ P.target :=
  Over.homMk (R.projection ≫ P.inclusion.left) (by
    change (R.projection ≫ P.inclusion.left) ≫ P.target.hom = R.projection ≫ P.divisor.hom
    rw [Category.assoc, Over.w P.inclusion])

/-- The actual quotient chain, including both ends and every joining divisor.

With the subline convention of `RelativeProjectiveLineModels` (the zero section is the
`𝒪`-subline, with normal `N`; the infinity section is the `N`-subline, with normal `Nᵛ`), the
strict transform of the original target meets the first ruled component along its infinity
section (normal `Nᵛ` there, against `N` on the target side), each ruled component is glued at its
zero section to the infinity section of the next, and the exposed boundary is the zero section of
the last component (Li, math/0009097v1, §4.1). -/
structure ExpandedSpecialFibre (m : ℕ) where
  scheme : Over (Spec (.of k))
  original : P.target ⟶ scheme
  ruled : Fin m → (ruledScheme P R ⟶ scheme)
  boundary : P.divisor ⟶ scheme
  first : ∀ h : 0 < m, P.inclusion ≫ original = ruledInfinity P R ≫ ruled ⟨0, h⟩
  joins : ∀ (j : Fin m) (h : j.val + 1 < m),
    ruledZero P R ≫ ruled j = ruledInfinity P R ≫ ruled ⟨j.val + 1, h⟩
  last : ∀ h : 0 < m,
    boundary = ruledZero P R ≫ ruled ⟨m - 1, by omega⟩
  empty : m = 0 → boundary = P.inclusion ≫ original
  contraction : scheme ⟶ P.target
  original_contraction : original ≫ contraction = 𝟙 P.target
  ruled_contraction : ∀ j : Fin m, ruled j ≫ contraction = ruledContraction P R
  boundary_contraction : boundary ≫ contraction = P.inclusion
  universal : ∀ (Z : Over (Spec (.of k))) (f : P.target ⟶ Z)
      (g : Fin m → (ruledScheme P R ⟶ Z)),
    (∀ h : 0 < m, P.inclusion ≫ f = ruledInfinity P R ≫ g ⟨0, h⟩) →
    (∀ (j : Fin m) (h : j.val + 1 < m),
      ruledZero P R ≫ g j = ruledInfinity P R ≫ g ⟨j.val + 1, h⟩) →
        ∃! q : scheme ⟶ Z, original ≫ q = f ∧ ∀ j, ruled j ≫ q = g j

end MathlibExt.AlgebraicGeometry.ExpandedTargetChainGeometry
