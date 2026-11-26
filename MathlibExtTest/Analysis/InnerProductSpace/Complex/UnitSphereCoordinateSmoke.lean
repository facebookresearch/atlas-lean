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

import MathlibExt.Analysis.InnerProductSpace.Complex.UnitVector
import Mathlib.Tactic.NormNum

open scoped BigOperators

-- Both coordinates are nonzero; the second is nonreal.
example :
    (WithLp.toLp 2 (fun i : Fin 2 =>
      if i = 0 then (3 / 5 : ℂ) else (4 / 5 : ℂ) * Complex.I) :
      EuclideanSpace ℂ (Fin 2)) ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1 := by
  apply (EuclideanSpace.mem_sphere_zero_one_iff_sum_star_mul_eq_one
    (WithLp.toLp 2 (fun i : Fin 2 =>
      if i = 0 then (3 / 5 : ℂ) else (4 / 5 : ℂ) * Complex.I) :
      EuclideanSpace ℂ (Fin 2))).mpr
  change (∑ i : Fin 2,
    starRingEnd ℂ (if i = 0 then (3 / 5 : ℂ) else (4 / 5 : ℂ) * Complex.I) *
      (if i = 0 then (3 / 5 : ℂ) else (4 / 5 : ℂ) * Complex.I)) = 1
  norm_num [Fin.sum_univ_succ, map_ofNat]
  rw [mul_mul_mul_comm (4 / 5 : ℂ) Complex.I (4 / 5 : ℂ) Complex.I, Complex.I_mul_I]
  norm_num

-- No hidden Nonempty premise: zero-dimensional Euclidean space has no unit vector.
example (x : EuclideanSpace ℂ (Fin 0)) :
    x ∉ Metric.sphere (0 : EuclideanSpace ℂ (Fin 0)) 1 := by
  rw [EuclideanSpace.mem_sphere_zero_one_iff_sum_star_mul_eq_one]
  simp
