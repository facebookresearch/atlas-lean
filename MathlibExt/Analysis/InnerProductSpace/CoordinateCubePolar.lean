/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import MathlibExt.Analysis.InnerProductSpace.PolarSet
public import MathlibExt.Geometry.Convex.CubeCovering

@[expose] public section

namespace MetaMathlibExt

private theorem inner_le_coordinateAbsSum {n : ℕ}
    (x y : EuclideanSpace ℝ (Fin n)) (hx : ∀ i, |x i| ≤ 1) :
    inner ℝ x y ≤ ∑ i, |y i| := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change ∑ i, y i * x i ≤ ∑ i, |y i|
  apply Finset.sum_le_sum
  intro i _
  calc
    y i * x i = x i * y i := mul_comm _ _
    _ ≤ |x i * y i| := le_abs_self _
    _ = |x i| * |y i| := abs_mul _ _
    _ ≤ 1 * |y i| := mul_le_mul_of_nonneg_right (hx i) (abs_nonneg _)
    _ = |y i| := by simp

private theorem exists_coordinateCube_support {n : ℕ} (y : EuclideanSpace ℝ (Fin n)) :
    ∃ x : EuclideanSpace ℝ (Fin n), (∀ i, |x i| ≤ 1) ∧ inner ℝ x y = ∑ i, |y i| := by
  let x : EuclideanSpace ℝ (Fin n) :=
    WithLp.toLp 2 (fun i => if 0 ≤ y i then (1 : ℝ) else -1)
  refine ⟨x, ?_, ?_⟩
  · intro i
    change |(if 0 ≤ y i then (1 : ℝ) else -1)| ≤ 1
    split <;> simp
  · rw [EuclideanSpace.inner_eq_star_dotProduct]
    change ∑ i, y i * (if 0 ≤ y i then (1 : ℝ) else -1) = ∑ i, |y i|
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : 0 ≤ y i
    · simp [h, abs_of_nonneg h]
    · simp [h, abs_of_neg (lt_of_not_ge h)]

/-- **The polar of the cube is the $\ell^1$ unit ball.** For every $n$, the polar of the
coordinate cube $[-1, 1]^n$ in the Euclidean space $\mathbb{R}^n$, that is the set of all $y$
with $\langle x, y \rangle \le 1$ for every $x$ in the cube, is the closed $\ell^1$ unit ball
$\{y \in \mathbb{R}^n : \sum_i |y_i| \le 1\}$. -/
theorem polarSet_coordinateCube (n : ℕ) :
    polarSet (ConvexCovering.coordinateCube n) =
      {y : EuclideanSpace ℝ (Fin n) | ∑ i, |y i| ≤ 1} := by
  rw [ConvexCovering.coordinateCube_eq_absSet]
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, hxy⟩ := exists_coordinateCube_support y
    change ∑ i, |y i| ≤ 1
    rw [← hxy]
    exact hy x hx
  · intro hy x hx
    exact (inner_le_coordinateAbsSum x y hx).trans hy

end MetaMathlibExt
