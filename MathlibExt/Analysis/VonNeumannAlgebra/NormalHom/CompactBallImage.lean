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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalHom
public import MathlibExt.Analysis.VonNeumannAlgebra.UltraweakOrder

/-!
# Original normal homomorphisms have compact images of ultraweak norm balls

The source's actual original norm ball is compact in its ultraweak view.
The given actual normal homomorphism is continuous between those views,
so its literal image of that same ball is compact. No weakly closed range,
normal inverse, predual or representation model is an input. This supplies
the compact-ball prerequisite for the actual faithful normal range constructor.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VonNeumannAlgebra.NormalStarAlgHom

noncomputable section

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

/-- The literal image of each original ultraweak norm ball under an actual normal map is compact. -/
theorem ultraweak_ball_image_isCompact (f : NormalStarAlgHom M N) (r : ℝ) :
    IsCompact ((fun x : Ultraweak M =>
      (ultraweakLinearEquiv N).symm (f (ultraweakLinearEquiv M x))) ''
        {x : Ultraweak M | ‖ultraweakLinearEquiv M x‖ ≤ r}) := by
  exact (ultraweakClosedBall_isCompact M r).image f.continuous_ultraweak

end

end VonNeumannAlgebra.NormalStarAlgHom
