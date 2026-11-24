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
public import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Faithful normal homomorphisms identify actual norm balls in their operator range

Injectivity of the original star homomorphism gives its stock C-star
isometry. Its original ultraweak ball image is therefore exactly the
intersection of its actual range with the target original norm ball.
Compactness of the original ball image makes that actual intersection
compact. No range closedness, predual or normal inverse certificate is input.
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

/-- The actual source ball image is exactly its original range intersected with the target norm ball. -/
theorem ultraweak_ball_image_eq_range_inter (f : NormalStarAlgHom M N)
    (hf : Function.Injective f) (r : ℝ) :
    f.ultraweakMap '' {x : Ultraweak M | ‖ultraweakLinearEquiv M x‖ ≤ r} =
      Set.range f.ultraweakMap ∩ {y : Ultraweak N | ‖ultraweakLinearEquiv N y‖ ≤ r} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨Set.mem_range_self x, ?_⟩
    change ‖ultraweakLinearEquiv N (f.ultraweakMap x)‖ ≤ r
    rw [f.ultraweakMap_apply, LinearEquiv.apply_symm_apply]
    change ‖f.toStarAlgHom (ultraweakLinearEquiv M x)‖ ≤ r
    rw [NonUnitalStarAlgHom.norm_map f.toStarAlgHom hf]
    exact hx
  · rintro ⟨⟨x, rfl⟩, hx⟩
    refine ⟨x, ?_, rfl⟩
    change ‖ultraweakLinearEquiv M x‖ ≤ r
    have hnorm : ‖ultraweakLinearEquiv N (f.ultraweakMap x)‖ = ‖ultraweakLinearEquiv M x‖ := by
      rw [f.ultraweakMap_apply, LinearEquiv.apply_symm_apply]
      exact NonUnitalStarAlgHom.norm_map f.toStarAlgHom hf _
    rw [← hnorm]
    exact hx

/-- The original range's intersection with every original target norm ball is actually compact. -/
theorem ultraweak_range_inter_ball_isCompact (f : NormalStarAlgHom M N)
    (hf : Function.Injective f) (r : ℝ) :
    IsCompact (Set.range f.ultraweakMap ∩ {y : Ultraweak N | ‖ultraweakLinearEquiv N y‖ ≤ r}) := by
  rw [← f.ultraweak_ball_image_eq_range_inter hf r]
  exact f.ultraweak_ball_image_isCompact r

end

end VonNeumannAlgebra.NormalStarAlgHom
