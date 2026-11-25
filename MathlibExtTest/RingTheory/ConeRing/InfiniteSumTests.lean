/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.RingTheory.ConeRing.InfiniteSum
public import Mathlib.Data.Int.Basic

/-!
# Original infinite-sum and finite-support boundary clients
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe uR uS

namespace ConeRing.SourceClients.InfiniteSum

open Matrix.LocallyFinite

/-- The actual original block sum absorbs the same original repeated matrix. -/
theorem actual_absorption {R : Type uR} [Semiring R] (A : ConeRing R) :
    blockSumHom R (A, infinityHom R A) = infinityHom R A := blockSum_infinity A

/-- The actual repeated matrix retains its original ordered right first-inclusion action. -/
theorem original_first_action {R : Type uR} [Semiring R] (A : ConeRing R) :
    infinityHom R A * firstInclusion R = firstInclusion R * A := infinity_mul_firstInclusion A

/-- The actual repeated matrix retains its original ordered left tail-projection action. -/
theorem original_tail_action {R : Type uR} [Semiring R] (A : ConeRing R) :
    tailProjection R * infinityHom R A = infinityHom R A * tailProjection R :=
  tailProjection_mul_infinity A

/-- The repeat of a nonzero original finite projection has infinite total support. -/
theorem repeated_finite_projection_not_finite :
    ¬HasFiniteSupport (infinityHom ℤ (finiteProjection 1)) := by
  intro h
  have hz := (infinityHom_hasFiniteSupport_iff (finiteProjection (R := ℤ) 1)).mp h
  have h0 := congrArg (fun A : ConeRing ℤ => A 0 0) hz
  simp [finiteProjection_apply] at h0

/-- The actual repeat and coefficient map commute across independent coefficient worlds. -/
theorem independent_repeat_square {R : Type uR} {S : Type uS}
    [Semiring R] [Semiring S] (f : R →+* S) (A : ConeRing R) :
    ConeRing.map f (infinityHom R A) = infinityHom S (ConeRing.map f A) := map_infinityHom f A

end ConeRing.SourceClients.InfiniteSum

end
