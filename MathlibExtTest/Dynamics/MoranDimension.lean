/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Dynamics.MoranDimension
import Mathlib.Tactic.NormNum

/-! # Tests for Moran's equality for affine-symmetric iterated function systems -/

namespace MathlibExtTest.Dynamics.MoranDimension

open MathlibExt.Dynamics.MoranDimensionWanted.Dynamics Set

private abbrev Line := EuclideanSpace ℝ (Fin 1)

-- Halving has the singleton attractor {0}. With one map the similarity dimension is zero.
example : dimH ({0} : Set Line) = 0 := by
  let f (_ : Fin 1) (x : Line) := (1 / 2 : ℝ) • x
  have ha : IsAffineSymmetricIFS f (1 / 2) :=
    ⟨by norm_num, by norm_num, fun _ => LinearIsometry.id, fun _ => 0, by simp [f]⟩
  have ho : OpenSetCondition f :=
    ⟨univ, isOpen_univ, univ_nonempty, fun _ => subset_univ _,
      fun i j h => (h (Subsingleton.elim i j)).elim⟩
  have hS : IsAttractor f {0} :=
    ⟨isCompact_singleton, singleton_nonempty _, by simp [f]⟩
  simpa only [Nat.cast_one, Real.log_one, neg_zero, zero_div, ENNReal.ofReal_zero] using
    moran_equality_affine (n := 1) le_rfl f (1 / 2) ha ho hS

-- Duplicating a map gives two identical nonempty open-set images, violating disjointness.
example (g : Line → Line) : ¬ OpenSetCondition (fun _ : Fin 2 => g) := by
  rintro ⟨G, _, ⟨x, hx⟩, _, hdis⟩
  have hd := hdis 0 1 (by decide)
  exact disjoint_left.mp hd (mem_image_of_mem g hx) (mem_image_of_mem g hx)

end MathlibExtTest.Dynamics.MoranDimension
