/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.RingTheory.ConeRing
public import Mathlib.Data.Int.Basic

/-!
# Original cone-module returns and unrestricted coefficient clients
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe uR uS

namespace ConeRing.SourceClients

open Matrix.LocallyFinite

/-- The original right-module return retains both original cone summands. -/
theorem right_regular_return {R : Type uR} [Semiring R] (x y : ConeRing R) :
    directSumRightLinearEquiv R ((directSumRightLinearEquiv R).symm (x, y)) = (x, y) :=
  (directSumRightLinearEquiv R).apply_symm_apply _

/-- The original left-module return retains both original cone summands. -/
theorem left_regular_return {R : Type uR} [Semiring R] (x y : ConeRing R) :
    directSumLeftLinearEquiv R ((directSumLeftLinearEquiv R).symm (x, y)) = (x, y) :=
  (directSumLeftLinearEquiv R).apply_symm_apply _

/-- The actual cone carrier permits arbitrary varying diagonal coefficients. -/
def varyingDiagonal : ConeRing ℤ := diagonal fun n => (n : ℤ)

/-- Every original varying diagonal coefficient remains its original integer. -/
theorem varyingDiagonal_apply (n : ℕ) : varyingDiagonal n n = (n : ℤ) := by
  simp [varyingDiagonal, diagonal_apply]

/-- The actual cone permits an infinite coefficient range. -/
theorem varyingDiagonal_range_infinite :
    (Set.range fun n : ℕ => varyingDiagonal n n).Infinite := by
  apply Set.infinite_range_of_injective
  intro a b h
  simpa only [varyingDiagonal_apply, Int.natCast_inj] using h

/-- Independent coefficient-ring worlds retain the actual scalar naturality square. -/
theorem independent_scalar_square {R : Type uR} {S : Type uS}
    [Semiring R] [Semiring S] (f : R →+* S) (r : R) :
    ConeRing.map f (scalarHom R r) = scalarHom S (f r) := map_scalarHom f r

end ConeRing.SourceClients

end
