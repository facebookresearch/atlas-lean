/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BlockStabilization
public import MathlibExt.KTheory.Ring.StableGeneralLinear.Stabilization

/-!
# Block stabilization in `StableGL`
-/

@[expose] public section

namespace AlgebraicKTheory
namespace StableGL

universe u

variable {R : Type u} [Semiring R]

/-- Adding a finite identity block does not change the stable class. -/
@[simp]
theorem of_blockStabilization {n m : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    StableGL.of
        (Matrix.GeneralLinearGroup.blockStabilization n m R g) =
      StableGL.of g := by
  induction m with
  | zero =>
      rw [Matrix.GeneralLinearGroup.blockStabilization_zero]
  | succ m ih =>
      rw [Matrix.GeneralLinearGroup.blockStabilization_succ,
        StableGL.of_stabilization, ih]

end StableGL
end AlgebraicKTheory

end
