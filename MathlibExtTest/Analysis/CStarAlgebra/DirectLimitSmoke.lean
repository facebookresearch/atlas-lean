/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.CStarAlgebra.DirectLimit
import Mathlib.Analysis.CStarAlgebra.ContinuousMap

/-!
# An actual constant nonunital C-star directed system

Identity transition maps on functions vanishing at infinity earn their norm
preservation. The exported constructors supply the direct-limit normed ring
and C-star law on the original quotient. The natural-number index satisfies
the source's directedness and nonemptiness hypotheses.
-/

noncomputable section
open scoped ZeroAtInfty
namespace CStarDirectLimitSmoke

private abbrev Coefficients := C₀(ℝ, ℂ)
private abbrev Family := fun _ : ℕ => Coefficients

private def transition (i j : ℕ) (_h : i ≤ j) : Family i →⋆ₙₐ[ℂ] Family j :=
  NonUnitalStarAlgHom.id ℂ Coefficients

private instance : DirectedSystem Family (transition · · ·) where
  map_self := by
    intro i x
    rfl
  map_map := by
    intro k j i hij hjk x
    rfl

private theorem transitionNorm (i j : ℕ) (h : i ≤ j) (x : Family i) :
    ‖transition i j h x‖ = ‖x‖ := rfl

private abbrev Limit := _root_.DirectLimit Family transition

local instance : NonUnitalNormedRing Limit :=
  DirectLimit.nonUnitalNormedRingOfNormPreserving transition transitionNorm
local instance : CStarRing Limit :=
  DirectLimit.cstar_ring_of_norm_preserving transition transitionNorm

-- The actual stage representative retains the original nonunital norm.
example (a : Coefficients) : ‖(⟦⟨0, a⟩⟧ : Limit)‖ = ‖a‖ :=
  DirectLimit.normedAddCommGroupOfNormPreserving_norm_mk transition transitionNorm 0 a

-- The norm construction includes the zero coefficient without a nonzero norm premise.
example : ‖(⟦⟨0, (0 : Coefficients)⟩⟧ : Limit)‖ = 0 := by
  rw [DirectLimit.normedAddCommGroupOfNormPreserving_norm_mk
    transition transitionNorm, norm_zero]

-- Identity transport identifies genuine representatives at two different stages.
example (a : Coefficients) : (⟦⟨0, a⟩⟧ : Limit) = (⟦⟨1, a⟩⟧ : Limit) :=
  DirectLimit.eq_of_le (f := transition) ⟨0, a⟩ 1 (Nat.zero_le 1)

-- The stock involution and the constructed C-star norm use the same limit carrier.
example (a : Coefficients) :
    star (⟦⟨0, a⟩⟧ : Limit) = (⟦⟨0, star a⟩⟧ : Limit) := rfl

section CStarLaw

-- Select the public star inherited from the actual stock StarRing when
-- reading its C-star field, avoiding two opaque routes to the same operation.
local instance : Star Limit := (StarRing.toStarAddMonoid (R := Limit)).toStar

example (x : Limit) : ‖x‖ * ‖x‖ ≤ ‖star x * x‖ :=
  CStarRing.norm_mul_self_le x

end CStarLaw

end CStarDirectLimitSmoke
