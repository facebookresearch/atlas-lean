/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Weight.PositiveCompression
public import MathlibExt.Analysis.VonNeumannAlgebra.Weight
public import MathlibExt.Analysis.VonNeumannAlgebra.MultiplicationPredual

/-!
# Source semifiniteness gives the actual finite-square ultraweak density

The original finite-positive integration span lies in the exact
finite-square module by the neutral scalar-weight compression APIs.
Source semifiniteness transfers its actual ultraweak density to that same
module. Weight-independent multiplication and predual continuity APIs are
supplied by the neutral MultiplicationPredual sibling.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace

noncomputable section

namespace VonNeumannAlgebra

universe uH

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Source finite-positive-span semifiniteness gives density of the actual original square module. -/
theorem weightFiniteSquareUltraweakDense (M : VonNeumannAlgebra H)
    (φ : CStarAlgebra.ScalarWeight.Weight M) (hφ : IsSemifiniteWeight M φ) :
    Dense ((φ.finiteSquareSubmodule.map (ultraweakLinearEquiv M).symm.toLinearMap :
      Submodule ℂ (Ultraweak M)) : Set (Ultraweak M)) := by
  change Dense ((φ.finiteIntegrationDomain.map (ultraweakLinearEquiv M).symm.toLinearMap :
    Submodule ℂ (Ultraweak M)) : Set (Ultraweak M)) at hφ
  apply hφ.mono
  exact Submodule.map_mono φ.finiteIntegrationDomain_le_finiteSquareSubmodule


end VonNeumannAlgebra

end
