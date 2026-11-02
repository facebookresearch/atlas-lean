/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Diffusion.SemigroupMoments

@[expose] public section

open Polynomial
open scoped unitInterval

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.SemigroupMoments

open MathlibExt.Biology.PopulationGenetics.Diffusion.WrightFisherSemigroup

private noncomputable def half : I := ⟨1 / 2, by constructor <;> norm_num⟩

-- The public theorem has exactly the source-bound contract shape.
example {t : ℝ} (ht : 0 ≤ t) (x : I) :
    wfSemigroup t (((X - C (x : ℝ)) ^ 4 : ℝ[X]).toContinuousMapOn I) x ≤
      (3 / 16 : ℝ) * t ^ 2 :=
  wfSemigroup_fourth_increment_le ht x

-- At time zero the centered polynomial itself vanishes at its center.
example (x : I) :
    wfSemigroup 0 (((X - C (x : ℝ)) ^ 4 : ℝ[X]).toContinuousMapOn I) x = 0 := by
  simp

-- Both boundary states and a nonzero horizon exercise the closed state domain.
example :
    wfSemigroup 1 (((X - C (0 : ℝ)) ^ 4 : ℝ[X]).toContinuousMapOn I) (0 : I) ≤
      (3 / 16 : ℝ) := by
  simpa using wfSemigroup_fourth_increment_le (t := (1 : ℝ)) (by norm_num) (0 : I)

example :
    wfSemigroup 2 (((X - C (1 : ℝ)) ^ 4 : ℝ[X]).toContinuousMapOn I) (1 : I) ≤
      (3 / 16 : ℝ) * (2 : ℝ) ^ 2 := by
  simpa using wfSemigroup_fourth_increment_le (t := (2 : ℝ)) (by norm_num) (1 : I)

-- The interior state and a fractional horizon exercise coercions and the exact constant.
example :
    wfSemigroup (1 / 2 : ℝ)
        (((X - C (half : ℝ)) ^ 4 : ℝ[X]).toContinuousMapOn I) half ≤
      (3 / 16 : ℝ) * (1 / 2 : ℝ) ^ 2 := by
  simpa using
    wfSemigroup_fourth_increment_le (t := (1 / 2 : ℝ)) (by norm_num) half

-- The supporting second-increment API is available at the same interior state.
example :
    wfSemigroup 2 (((X - C (half : ℝ)) ^ 2 : ℝ[X]).toContinuousMapOn I) half ≤
      (1 / 4 : ℝ) * (2 : ℝ) := by
  simpa using wfSemigroup_second_increment_le (t := (2 : ℝ)) (by norm_num) half

-- The generator identities used by the comparisons have their intended coefficients.
example (x y : ℝ) :
    (polyGenerator ((X - C x) ^ 2)).eval y = y * (1 - y) := by
  simp [polyGenerator, Polynomial.derivative_pow]
  ring

example (x y : ℝ) :
    (polyGenerator ((X - C x) ^ 4)).eval y =
      6 * y * (1 - y) * (y - x) ^ 2 := by
  simp [polyGenerator, Polynomial.derivative_pow]
  ring

-- The public dynamics theorem exposes the existing semigroup's generator derivative.
example (p : ℝ[X]) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => wfSemigroup s (p.toContinuousMapOn I))
      (wfSemigroup t ((polyGenerator p).toContinuousMapOn I)) t :=
  hasDerivAt_wfSemigroup_toContinuousMapOn p ht

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.SemigroupMoments
