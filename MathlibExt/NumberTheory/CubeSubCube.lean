/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Integer cubes that differ by `1` or `2`

For integers `u` and `v`, `u ^ 3 - v ^ 3 = 2` holds only for `(u, v) = (1, -1)`, and
`u ^ 3 - v ^ 3 = 1` holds only for `(u, v) = (1, 0)` and `(u, v) = (0, -1)`
(`MetaMathlibExt.cube_sub_cube_eq_two_or_one_iff`). This is Lemma 5 of Jialai She's paper on
consecutive powerful triplets around cubes. The paper applies it when `x - 1` and `x + 1` are
both cubes, and when `x ^ 3 + 1` or `x ^ 3 - 1` is a cube.

## Proof outline

Factor `u ^ 3 - v ^ 3 = (u - v) * (u ^ 2 + u * v + v ^ 2)`. The second factor is nonnegative,
since twice it is `u ^ 2 + v ^ 2 + (u + v) ^ 2`. So if the difference is a positive `k`, then
`u - v ≥ 1`, and therefore `u ^ 2 + u * v + v ^ 2 ≤ k`. For `k ≤ 2` this gives
`u ^ 2 + v ^ 2 ≤ 4`, so `u` and `v` lie in `[-2, 2]`, and a finite check finishes the proof. The
paper splits the factorization into the cases `u - v = 1` and `u - v = 2` instead.

## Implementation notes

`cube_sub_cube_eq_two_or_one_iff` keeps the full name, the statement and the docstring it had
as a wanted theorem in `WantedExt.NumberTheory.ConsecutivePowerfulTripletsWanted`, which imports
this module.

## References

* Jialai She, *Nonexistence of Consecutive Powerful Triplets Around Cubes with Prime-Square
  Factors*, arXiv:2507.16828v3, Lemma 5 and its proof (<https://arxiv.org/abs/2507.16828>).
-/

@[expose] public section

namespace MetaMathlibExt

/-- If `u ^ 3 - v ^ 3 = k` with `0 < k ≤ 2`, then `u` and `v` lie in `[-2, 2]`. -/
private theorem mem_Icc_of_cube_sub_cube_eq {u v k : ℤ} (hk₀ : 0 < k) (hk₂ : k ≤ 2)
    (h : u ^ 3 - v ^ 3 = k) : u ∈ Set.Icc (-2) 2 ∧ v ∈ Set.Icc (-2) 2 := by
  have hfac : u ^ 3 - v ^ 3 = (u - v) * (u ^ 2 + u * v + v ^ 2) := by ring
  have hq : 0 ≤ u ^ 2 + u * v + v ^ 2 := by
    nlinarith [sq_nonneg (u + v), sq_nonneg u, sq_nonneg v]
  have hd : 1 ≤ u - v := by
    by_contra! hlt
    nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ -(u - v)) hq]
  have hle : u ^ 2 + u * v + v ^ 2 ≤ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hd hq]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith [sq_nonneg (u + v), sq_nonneg u, sq_nonneg v]

/-- **Integer solutions of $u^3 - v^3 = 2$ and $u^3 - v^3 = 1$.** For all integers $u$ and $v$,
$u^3 - v^3 = 2$ if and only if $(u, v) = (1, -1)$, and $u^3 - v^3 = 1$ if and only if
$(u, v) = (1, 0)$ or $(u, v) = (0, -1)$.

Source: Jialai She, *Nonexistence of Consecutive Powerful Triplets Around Cubes
with Prime-Square Factors*, INTEGERS 25 (2025), Article A103, Lemma 5
(`integers-2025-A103-lem-5`). -/
theorem cube_sub_cube_eq_two_or_one_iff (u v : ℤ) :
    (u ^ 3 - v ^ 3 = 2 ↔ (u, v) = (1, -1)) ∧
      (u ^ 3 - v ^ 3 = 1 ↔ (u, v) = (1, 0) ∨ (u, v) = (0, -1)) := by
  refine ⟨⟨fun h => ?_, ?_⟩, ⟨fun h => ?_, ?_⟩⟩
  · obtain ⟨⟨hu₁, hu₂⟩, hv₁, hv₂⟩ := mem_Icc_of_cube_sub_cube_eq (by norm_num) le_rfl h
    interval_cases u <;> interval_cases v <;> simp_all
  · simp only [Prod.mk.injEq]
    rintro ⟨rfl, rfl⟩
    norm_num
  · obtain ⟨⟨hu₁, hu₂⟩, hv₁, hv₂⟩ := mem_Icc_of_cube_sub_cube_eq (by norm_num) (by norm_num) h
    interval_cases u <;> interval_cases v <;> simp_all
  · simp only [Prod.mk.injEq]
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

end MetaMathlibExt
