/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.IntegrableHiggsBundles

/-!
# Tests for integrable Higgs bundles

The zero Higgs field is integrable, so every vector bundle is a Higgs bundle; a morphism of
Higgs bundles is determined by its underlying module map.
-/

open CategoryTheory MathlibExt.AlgebraicGeometry.IntegrableHiggsBundles
open MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies

variable {X : ComplexScheme}

/-- The Higgs square of the zero field vanishes. -/
example (E : X.left.Modules) :
    square (0 : E ⟶ moduleTensor X.left E (Omega X 1)) = 0 := by
  simp [square]

/-- Every vector bundle with the zero field is an integrable Higgs bundle. -/
noncomputable def zeroHiggs (E : X.left.Modules) (r : ℕ)
    (hE : MathlibExt.AlgebraicGeometry.CurveVectorBundles.IsVectorBundle E r) : HiggsBundle X where
  rank := r
  module := E
  bundle := hE
  theta := 0
  integrable := by simp [square]

/-- Morphisms of Higgs bundles agree when their module maps agree. -/
example (E F : HiggsBundle X) (f g : E ⟶ F)
    (h : HiggsBundle.forget.map f = HiggsBundle.forget.map g) : f = g :=
  HiggsBundle.forget.map_injective h
