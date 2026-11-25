/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.DerivedInternalHom

/-!
# Tests for the derived internal Hom

Precomposition on `RHom(-, N)` is contravariantly functorial, so it sends an isomorphism to an
isomorphism whose inverse is precomposition with the inverse.
-/

open CategoryTheory MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.DerivedInternalHom

attribute [local instance] HasDerivedCategory.standard

variable [HasDerivedTensors.{0}] {X : AlgebraicGeometry.Scheme.{0}}

example {K K' : D X} (e : K ≅ K') (N : D X)
    [((derivedTensor X).obj K).IsLeftAdjoint] [((derivedTensor X).obj K').IsLeftAdjoint] :
    precomp e.hom N ≫ precomp e.inv N = 𝟙 (internalHom X K' N) := by
  rw [← precomp_comp, e.inv_hom_id, precomp_id]

example {K K' : D X} (e : K ≅ K') (N : D X)
    [((derivedTensor X).obj K).IsLeftAdjoint] [((derivedTensor X).obj K').IsLeftAdjoint] :
    precomp e.inv N ≫ precomp e.hom N = 𝟙 (internalHom X K N) := by
  rw [← precomp_comp, e.hom_inv_id, precomp_id]

/-- `precomp a N` is the transpose of `a ⊗ᴸ 1` followed by evaluation. -/
example {K K' : D X} (a : K ⟶ K') (N : D X)
    [((derivedTensor X).obj K).IsLeftAdjoint] [((derivedTensor X).obj K').IsLeftAdjoint] :
    (internalHomEquiv X K _ N).symm (precomp a N) =
      ((derivedTensor X).map a).app (internalHom X K' N) ≫
        (Adjunction.ofIsLeftAdjoint ((derivedTensor X).obj K')).counit.app N := by
  simp [precomp]
