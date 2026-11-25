/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.IntervalCases
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card

/-!
# Sums of consecutive squares and arithmetic polygons

This module proves strict bounds on the ratio of the spans of a solution to the
sum of consecutive squares equation. It also records the corresponding 3-4-5 triangle.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The sum of consecutive squares equation.** Integers $a$, $b$, $c$ satisfy the sum of
consecutive squares (SoCS) equation when $2\,b(b+1)(2b+1) = a(a+1)(2a+1) + c(c+1)(2c+1)$.

With $P_n = n(n+1)(2n+1)/6$ this is $P_a + P_c = 2P_b$ multiplied by $6$. For $a < b < c$ it is
equivalent to $(a+1)^2 + (a+2)^2 + \dots + b^2 = (b+1)^2 + (b+2)^2 + \dots + c^2$, since
$P_n - P_{n-1} = n^2$. No order or sign condition on $a$, $b$, $c$ is imposed.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, equations (1) and (2). -/
public def SoCSEq (a b c : ℤ) : Prop :=
  2 * (b * (b + 1) * (2 * b + 1))
    = a * (a + 1) * (2 * a + 1) + c * (c + 1) * (2 * c + 1)

/-- **Solutions of the sum of consecutive squares problem.** A triple of integers
$(a, b, c)$ is a SoCS solution when $0 < a + 1 < b < c$ and $(a, b, c)$ satisfies the sum of
consecutive squares equation $2\,b(b+1)(2b+1) = a(a+1)(2a+1) + c(c+1)(2c+1)$, that is,
$(a+1)^2 + \dots + b^2 = (b+1)^2 + \dots + c^2$.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Section 1. -/
public def IsSoCSSolution (a b c : ℤ) : Prop :=
  0 < a + 1 ∧ a + 1 < b ∧ b < c ∧ SoCSEq a b c

/-- **$(2, 4, 5)$ solves the sum of consecutive squares problem.** The triple $(2, 4, 5)$ is a
solution of the sum of consecutive squares problem: $0 < 3 < 4 < 5$ and $3^2 + 4^2 = 5^2$.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Section 1. -/
public theorem isSoCSSolution_two_four_five : IsSoCSSolution 2 4 5 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  unfold SoCSEq
  norm_num

/-- **Bounds on the ratio of the two spans.** For every solution $(a, b, c)$ of the sum of
consecutive squares problem, $1 < (b - a)/(c - b) < 1 + 2^{1/3} + 2^{2/3}$.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Lemma 1
(`integers-2026-A1-lem-1`). -/
public theorem soCS_ratio_bounds (a b c : ℤ) (h : IsSoCSSolution a b c) :
    1 < (b - a : ℝ) / (c - b) ∧
    (b - a : ℝ) / (c - b) < 1 + (2 : ℝ) ^ (1 / 3 : ℝ) + (2 : ℝ) ^ (2 / 3 : ℝ) := by
  obtain ⟨ha, hab, hbc, heq⟩ := h
  have ha₀ : (0 : ℝ) ≤ a := by exact_mod_cast (show 0 ≤ a by omega)
  let x : ℝ := b - a
  let y : ℝ := c - a
  have hx : 0 < x := by
    dsimp [x]
    exact_mod_cast (show 0 < b - a by omega)
  have hy : 0 < y := by
    dsimp [y]
    exact_mod_cast (show 0 < c - a by omega)
  have hgap : (0 : ℝ) < c - b := by exact_mod_cast sub_pos.mpr hbc
  -- Translating the sum-of-squares polynomial by a gives a cubic
  -- with strictly positive linear and quadratic coefficients.
  let u : ℝ := 6 * (a : ℝ) ^ 2 + 6 * a + 1
  let v : ℝ := 6 * (a : ℝ) + 3
  let F (t : ℝ) := u * t + v * t ^ 2 + 2 * t ^ 3
  have hu : 0 < u := by dsimp [u]; positivity
  have hv : 0 < v := by dsimp [v]; positivity
  have hF : F y = 2 * F x := by
    unfold SoCSEq at heq
    have heq' := congrArg (Int.cast : ℤ → ℝ) heq
    push_cast at heq'
    dsimp [F, u, v, x, y]
    linear_combination -heq'
  have mono : MonotoneOn F (Set.Ici 0) := by
    intro s hs t _ hst
    change 0 ≤ s at hs
    dsimp [F]
    gcongr
  -- Doubling the argument more than doubles F.
  have hy₂ : y < 2 * x := by
    by_contra! hle
    have hle' := mono (show 0 ≤ 2 * x by positivity) hy.le hle
    rw [hF] at hle'
    dsimp [F] at hle'
    nlinarith only [hle', mul_pos hv (pow_pos hx 2), pow_pos hx 3]
  refine ⟨(lt_div_iff₀ hgap).2 (by dsimp [y, x] at hy₂; linarith), (div_lt_iff₀ hgap).2 ?_⟩
  -- Scaling by the cube root of two less than doubles the lower-degree terms.
  let k := (2 : ℝ) ^ (1 / 3 : ℝ)
  have hk : 1 < k := Real.one_lt_rpow (by norm_num) (by norm_num)
  have hk₃ : k ^ 3 = 2 := by
    dsimp [k]
    rw [← Real.rpow_mul_natCast (by norm_num)]
    norm_num
  have hpow : (2 : ℝ) ^ (2 / 3 : ℝ) = k ^ 2 := by
    dsimp [k]
    rw [← Real.rpow_mul_natCast (by norm_num)]
    norm_num
  have hk₁ : k < 2 := Real.rpow_lt_self_of_one_lt (by norm_num) (by norm_num)
  have hk₂ : k ^ 2 < 2 := by
    rw [← hpow]
    exact Real.rpow_lt_self_of_one_lt (by norm_num) (by norm_num)
  have hkx : k * x < y := by
    by_contra! hle
    have hle' := mono hy.le (show 0 ≤ k * x by positivity) hle
    rw [hF] at hle'
    dsimp [F] at hle'
    rw [mul_pow, mul_pow, hk₃] at hle'
    nlinarith only [hle', mul_pos (mul_pos hu hx) (sub_pos.mpr hk₁),
      mul_pos (mul_pos hv (pow_pos hx 2)) (sub_pos.mpr hk₂)]
  rw [hpow]
  change x < (1 + k + k ^ 2) * ((c : ℝ) - b)
  calc
    x = (1 + k + k ^ 2) * (k * x - x) := by linear_combination -x * hk₃
    _ < (1 + k + k ^ 2) * ((c : ℝ) - b) := by
      apply mul_lt_mul_of_pos_left _ (by positivity)
      dsimp [y, x] at hkx ⊢
      linarith

/-! ### Arithmetic polygons -/

/-- An *arithmetic polygon* with side lengths `a + 1, …, a + N`, encoded as an
`N`-periodic vertex sequence `v : ℕ → ℂ` with the special vertex `O = v 0`;
side `k` joins `v k` to `v (k + 1)`. The conditions follow Definition 1 of the
paper: the polygon has at least three pairwise distinct vertices; (1) going
around from `O`, side `k` has length `a + 1 + k`; (2) for each side some line
perpendicular to it passes through `O` and one endpoint of that side, i.e.
`O - v k` or `O - v (k + 1)` is orthogonal to `v (k + 1) - v k` (automatic for
the two sides at `O`); (3) no vertex has angle `0` or `π`, i.e. consecutive
sides are never parallel. Self-intersecting polygons are allowed, as in the
paper.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Definition 1. -/
public def IsArithmeticPolygon (a N : ℕ) (v : ℕ → ℂ) : Prop :=
  3 ≤ N ∧ Function.Periodic v N ∧ Set.InjOn v (Set.Iio N) ∧
    (∀ k < N, ‖v (k + 1) - v k‖ = (a + 1 + k : ℝ)) ∧
    (∀ k < N, (starRingEnd ℂ (v (k + 1) - v k) * (v 0 - v k)).re = 0 ∨
      (starRingEnd ℂ (v (k + 1) - v k) * (v 0 - v (k + 1))).re = 0) ∧
    (∀ k < N, (starRingEnd ℂ (v (k + 1) - v k) * (v (k + 2) - v (k + 1))).im ≠ 0)

/-- The closed polygon with vertices `v 0, …, v (N - 1)` (side `k` joining
`v k` to `v (k + 1)`, with `v N = v 0` for the periodic sequences used here) is
*not self-intersecting*: two distinct sides meet at most in a common endpoint.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Section 3 (non-self-intersecting polygons,
Remark 3 and
Theorem 6). -/
public def IsSimpleClosedPolygon (N : ℕ) (v : ℕ → ℂ) : Prop :=
  ∀ i < N, ∀ j < N, i ≠ j →
    segment ℝ (v i) (v (i + 1)) ∩ segment ℝ (v j) (v (j + 1)) ⊆
      ({v i, v (i + 1)} : Set ℂ) ∩ {v j, v (j + 1)}

/-- The number `μ(P)` of interior angles greater than `π` of a closed polygon:
the number of vertices `v (k + 1)`, `k < N`, at which the turn
`Im(conj (v (k + 1) - v k) * (v (k + 2) - v (k + 1)))` has sign opposite to the
orientation given by the shoelace sum `∑ Im(conj (v i) * v (i + 1))`. For a
non-self-intersecting polygon these are exactly the reflex vertices.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Section 3 (definition of `µ` before
Theorem 7). -/
public noncomputable def polygonReflexCount (N : ℕ) (v : ℕ → ℂ) : ℕ :=
  {k : ℕ | k < N ∧
    (starRingEnd ℂ (v (k + 1) - v k) * (v (k + 2) - v (k + 1))).im *
      (∑ i ∈ Finset.range N, (starRingEnd ℂ (v i) * v (i + 1)).im) < 0}.ncard

/-- Characteristic example: the `3`-`4`-`5` right triangle with `O` at the
origin (sides `3`, `4`, `5` in order) is a non-self-intersecting arithmetic
polygon with `a = 2` and no reflex angle.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Section 1 and proof of Theorem 4. -/
public theorem exists_isArithmeticPolygon_two_three :
    ∃ v : ℕ → ℂ, IsArithmeticPolygon 2 3 v ∧ IsSimpleClosedPolygon 3 v ∧
      polygonReflexCount 3 v = 0 := by
  let v : ℕ → ℂ := fun k => ![0, 3, 3 + 4 * Complex.I] ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩
  have h0 : v 0 = 0 := rfl
  have h1 : v 1 = 3 := rfl
  have h2 : v 2 = 3 + 4 * Complex.I := rfl
  have h3 : v 3 = 0 := rfl
  have h4 : v 4 = 3 := rfl
  have h5 : (25 : ℝ) = 5 ^ 2 := by norm_num
  refine ⟨v, ⟨le_rfl, fun k => by simp [v], ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i hi j hj h
    simp only [Set.mem_Iio] at hi hj
    interval_cases i <;> interval_cases j <;>
      simp [h0, h1, h2, Complex.ext_iff] at h ⊢
  · intro k hk
    interval_cases k
    · simp [h0, h1]; norm_num
    · simp [h1, h2]; norm_num
    · rw [h3, h2, zero_sub, norm_neg, Complex.norm_def, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.re_ofNat, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.im_ofNat, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im,
        Complex.mul_im, zero_add, Nat.cast_ofNat]
      norm_num
      rw [h5, Real.sqrt_sq (by norm_num)]
  · intro k hk
    interval_cases k <;> simp [h0, h1, h2, h3]
  · intro k hk
    interval_cases k <;> simp [h0, h1, h2, h3, h4]
  · intro i hi j hj hij
    interval_cases i <;> interval_cases j <;> (try exact absurd rfl hij) <;>
    · rintro z ⟨hz1, hz2⟩
      rw [segment_eq_image'] at hz1 hz2
      obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hz1
      obtain ⟨t, ⟨ht0, ht1⟩, he⟩ := hz2
      norm_num [h0, h1, h2, h3, Complex.ext_iff] at he ⊢
      obtain ⟨ha, hb⟩ := he
      first
        | (have hs : s = 0 := by linarith
           subst hs; norm_num)
        | (have hs : s = 1 := by linarith
           subst hs; norm_num)
  · unfold polygonReflexCount
    convert Set.ncard_empty ℕ using 2
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_lt]
    intro hk
    interval_cases k <;> simp [Finset.sum_range_succ, h0, h1, h2, h3, h4]

end

end MetaMathlibExt
