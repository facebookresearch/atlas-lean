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
# Ultraweak density of a semifinite weight's square domain

For an extended positive weight on a concrete von Neumann algebra, the finite-positive
integration span lies in `n_φ={x : φ(x* x)<∞}`. If the integration span is ultraweakly dense,
then `n_φ` is ultraweakly dense as well.

This density assertion requires semifiniteness in the finite-positive span sense. Faithfulness
and normality of the weight are not premises.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace

noncomputable section

namespace VonNeumannAlgebra

universe uH

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Semifinite square domain is ultraweakly dense.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `φ : M₊ → [0,∞]` be an extended
positive weight: additive, homogeneous for finite nonnegative real scalars, and zero at
zero. if `span ℂ {a ≥ 0 : φ(a)<∞}` is ultraweakly dense in `M`, then the complex submodule
`n_φ={x : φ(x* x)<∞}` is ultraweakly dense. No faithfulness or normality is assumed. -/
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
