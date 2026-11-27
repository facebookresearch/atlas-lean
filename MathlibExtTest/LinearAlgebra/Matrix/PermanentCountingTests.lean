/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.PermanentCounting

/-!
# Permanent counting tests

Closed checks: the complete bipartite graph `K_{2,2}` has two perfect matchings, so the permanent of
the all-ones `2 × 2` integer matrix is `2`; its determinant over `ZMod 2` is `0`, the parity.
-/

namespace MathlibExt.LinearAlgebra.Matrix.PermanentCounting

open Equiv

example : (Matrix.of fun (_ _ : Fin 2) => if True then (1 : ℤ) else 0).permanent = 2 := by
  rw [permanent_boole_eq_card]
  decide

example : (Matrix.of fun (_ _ : Fin 2) => if True then (1 : ZMod 2) else 0).det = 0 := by
  rw [← card_perfect_matchings_mod_two]
  decide

example (M : Matrix (Fin 3) (Fin 3) ℤ) :
    ((M.permanent : ℤ) : ZMod 2) = (M.map (Int.cast : ℤ → ZMod 2)).det :=
  intCast_permanent_eq_det M

end MathlibExt.LinearAlgebra.Matrix.PermanentCounting
