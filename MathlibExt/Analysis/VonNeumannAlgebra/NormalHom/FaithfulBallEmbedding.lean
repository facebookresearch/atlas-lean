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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalHom.CompactBallImage
public import Mathlib.Topology.Separation.Hausdorff

/-!
# A faithful normal homomorphism embeds each original ultraweak norm ball

The original source norm ball is actually ultraweak compact. Restricting
the original normal map to that ball gives a continuous injection into
the original Hausdorff target ultraweak space, hence a closed embedding.
This proves inverse continuity on each actual bounded image without a
supplied weakly closed range, normal inverse or predual/model certificate.
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

/-- Restriction of the original faithful normal map to each actual norm ball is a closed embedding. -/
theorem ultraweak_ball_isClosedEmbedding (f : NormalStarAlgHom M N)
    (hf : Function.Injective f) (r : ℝ) :
    Topology.IsClosedEmbedding (fun x : {x : Ultraweak M | ‖ultraweakLinearEquiv M x‖ ≤ r} =>
      f.ultraweakMap x.val) := by
  let B : Set (Ultraweak M) := {x | ‖ultraweakLinearEquiv M x‖ ≤ r}
  let : CompactSpace B := isCompact_iff_compactSpace.mp
    (show IsCompact B from ultraweakClosedBall_isCompact M r)
  have hcontinuous : Continuous (fun x : B => f.ultraweakMap x.val) :=
    f.ultraweakMap.continuous.comp continuous_subtype_val
  apply hcontinuous.isClosedEmbedding
  intro x y hxy
  apply Subtype.ext
  apply (ultraweakLinearEquiv M).injective
  apply hf
  have hvalue := congrArg (ultraweakLinearEquiv N) hxy
  simpa only [f.ultraweakMap_apply, LinearEquiv.apply_symm_apply] using hvalue

end

end VonNeumannAlgebra.NormalStarAlgHom
