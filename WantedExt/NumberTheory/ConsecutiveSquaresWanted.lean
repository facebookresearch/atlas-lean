/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
import Mathlib.Tactic.IntervalCases
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Topology.MetricSpace.Isometry

namespace MetaMathlibExt

@[expose] public section

/-- The Sum of Consecutive Squares (SoCS) equation
`(a+1)^2 + ⋯ + b^2 = (b+1)^2 + ⋯ + c^2`, written in cleared square-pyramidal
form `2 * P b = P a + P c` with `6 * P x = x * (x + 1) * (2 * x + 1)`.

Verified verbatim against the primary source (arXiv:2411.08398, the TeX
source of the published article): equation (1) there is
`(a+1)^2 + (a+2)^2 + ⋯ + b^2 = (b+1)^2 + (b+2)^2 + ⋯ + c^2`, restated with
`P_n = n(n+1)(2n+1)/6` as `P_b - P_a = P_c - P_b`, i.e. equation (2)
`P_a + P_c = 2 P_b`, under the range `0 < a + 1 < b < c`. The form used here
is (2) multiplied through by `6`.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, equations (1) and (2). -/
public def SoCSEq (a b c : ℤ) : Prop :=
  2 * (b * (b + 1) * (2 * b + 1))
    = a * (a + 1) * (2 * a + 1) + c * (c + 1) * (2 * c + 1)

/-- A solution of the Sum of Consecutive Squares Problem in the paper's
range `0 < a + 1 < b < c`.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Section 1. -/
public def IsSoCSSolution (a b c : ℤ) : Prop :=
  0 < a + 1 ∧ a + 1 < b ∧ b < c ∧ SoCSEq a b c

/-- Characteristic example: `(2, 4, 5)` is a SoCS solution, since
`3^2 + 4^2 = 5^2`.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Section 1. -/
public theorem isSoCSSolution_two_four_five : IsSoCSSolution 2 4 5 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  unfold SoCSEq
  norm_num

/-- Bounds on the ratio `(b - a) / (c - b)` for SoCS solutions:
`1 < (b - a) / (c - b) < 1 + 2^{1/3} + 2^{2/3}`.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Lemma 1
(`integers-2026-A1-lem-1`). -/
public theorem_wanted soCS_ratio_bounds (a b c : ℤ) (h : IsSoCSSolution a b c) :
    1 < (b - a : ℝ) / (c - b) ∧
    (b - a : ℝ) / (c - b) < 1 + (2 : ℝ) ^ (1 / 3 : ℝ) + (2 : ℝ) ^ (2 / 3 : ℝ)

/-- For a SoCS solution `(a, b, c)`, the Pell-type parameter
`A = 3 * (b - c)^2 * (12 * (b - a)^2 * (c - b)^2 - (a - 2b + c)^4)` is
positive and is not a square.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Corollary 1
(`integers-2026-A1-cor-1`), verified against arXiv:2411.08398 (the formula
is garbled in the statement extraction). -/
public theorem_wanted soCS_pell_param_pos_nonsquare (a b c : ℤ)
    (h : IsSoCSSolution a b c) :
    0 < 3 * (b - c) ^ 2 * (12 * (b - a) ^ 2 * (c - b) ^ 2 - (a - 2 * b + c) ^ 4) ∧
    ¬ IsSquare (3 * (b - c) ^ 2 * (12 * (b - a) ^ 2 * (c - b) ^ 2 - (a - 2 * b + c) ^ 4))

/-- From any SoCS solution `(a, b, c)` one obtains an infinite family of
integer solutions of the SoCS equation, all lying in the plane
`(b - c) * x + (c - a) * y + (a - b) * z = 0`, with `z - x ≡ c - a (mod 2)`.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Proposition 1
(`integers-2026-A1-prop-1`). -/
public theorem_wanted soCS_infinite_family_plane (a b c : ℤ)
    (h : IsSoCSSolution a b c) :
    ∃ f : ℕ → ℤ × ℤ × ℤ, Function.Injective f ∧
      ∀ n, SoCSEq (f n).1 (f n).2.1 (f n).2.2 ∧
        (b - c) * (f n).1 + (c - a) * (f n).2.1 + (a - b) * (f n).2.2 = 0 ∧
        (f n).2.2 - (f n).1 ≡ c - a [ZMOD 2]

/-- For each odd `N ≥ 3` there is a SoCS solution `(a, b, c)` with
`c - a = N`, and an infinite family of SoCS solutions with odd span, all
lying in the plane `(b - c) * x + (c - a) * y + (a - b) * z = 0` determined
by that solution (the plane through `(a, b, c)` and the line `x = y = z`, as
in Proposition 1). Partial scope: the paper additionally states that this
plane is unique for each `N`; that uniqueness clause is not encoded here.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Theorem 2
(`integers-2026-A1-thm-2`), verified against arXiv:2411.08398. -/
public theorem_wanted soCS_odd_span (N : ℤ) (hN : Odd N) (h3 : 3 ≤ N) :
    ∃ a b c : ℤ, IsSoCSSolution a b c ∧ c - a = N ∧
    ∃ f : ℕ → ℤ × ℤ × ℤ, Function.Injective f ∧
      ∀ n, IsSoCSSolution (f n).1 (f n).2.1 (f n).2.2 ∧
        Odd ((f n).2.2 - (f n).1) ∧
        (b - c) * (f n).1 + (c - a) * (f n).2.1 + (a - b) * (f n).2.2 = 0

/-- There are infinitely many SoCS solutions with `c - a` even.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Theorem 3
(`integers-2026-A1-thm-3`). -/
public theorem_wanted soCS_even_span_infinite :
    {t : ℤ × ℤ × ℤ | IsSoCSSolution t.1 t.2.1 t.2.2 ∧ Even (t.2.2 - t.1)}.Infinite

/-- For each `N > 1` there are at most `2 * (N - 1)` SoCS solutions with
`c - a = N`.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Theorem 5
(`integers-2026-A1-thm-5`). -/
public theorem_wanted soCS_card_le (N : ℤ) (hN : 1 < N)
    (s : Finset (ℤ × ℤ × ℤ))
    (hs : ∀ t ∈ s, IsSoCSSolution t.1 t.2.1 t.2.2 ∧ t.2.2 - t.1 = N) :
    s.card ≤ 2 * (N - 1).toNat

/-- No finite collection of planes in `ℝ^3` contains all SoCS solutions:
for every finite set of affine planes `u * x + v * y + w * z = t` with
nonzero normal vector, some SoCS solution lies outside all of them.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Corollary 2
(`integers-2026-A1-cor-2`); the proof text appended to the extracted
statement is not part of the claim. -/
public theorem_wanted soCS_not_finite_planes
    (S : Finset (ℝ × ℝ × ℝ × ℝ))
    (hS : ∀ p ∈ S, (p.1, p.2.1, p.2.2.1) ≠ 0) :
    ∃ a b c : ℤ, IsSoCSSolution a b c ∧
      ∀ p ∈ S, p.1 * (a : ℝ) + p.2.1 * (b : ℝ) + p.2.2.1 * (c : ℝ) ≠ p.2.2.2

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
      simp; norm_num
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
      simp [h0, h1, h2, h3, Complex.ext_iff] at he ⊢
      obtain ⟨ha, hb⟩ := he
      first
        | (have hs : s = 0 := by linarith
           subst hs; norm_num)
        | (have hs : s = 1 := by linarith
           subst hs; norm_num)
  · unfold polygonReflexCount
    convert Set.ncard_empty ℕ
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_lt]
    intro hk
    simp [Finset.sum_range_succ, h0, h1, h2, h3]
    interval_cases k <;> simp [h0, h1, h2, h3, h4]

/-- Arithmetic polygons with side lengths `a + 1, …, a + N` exist exactly when
the SoCS Problem has a solution `(a, b, a + N)` (the correspondence sends a
polygon to its solution, and it is surjective); and the correspondence is
many-to-one: some solution comes from two arithmetic polygons that are not
congruent (no isometry of the plane maps one vertex sequence onto the other).

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Theorem 1 (`integers-2026-A1-thm-1`). -/
public theorem_wanted arithmeticPolygon_correspondence :
    (∀ a N : ℕ, (∃ v, IsArithmeticPolygon a N v) ↔ ∃ b : ℤ, IsSoCSSolution a b (a + N)) ∧
    ∃ (a N : ℕ) (v w : ℕ → ℂ), IsArithmeticPolygon a N v ∧ IsArithmeticPolygon a N w ∧
      ¬ ∃ f : ℂ ≃ᵢ ℂ, ∀ k, w k = f (v k)

/-- Up to rigid transformations (isometries of the plane, reflections included,
as in the paper's proof) there are exactly two convex arithmetic polygons. A
polygon is convex when it is not self-intersecting and has no interior angle
greater than `π` (angles equal to `π` are already excluded by Definition 1).

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Theorem 4 (`integers-2026-A1-thm-4`). -/
public theorem_wanted convex_arithmeticPolygon_two_classes :
    ∃ (a₁ N₁ : ℕ) (v₁ : ℕ → ℂ) (a₂ N₂ : ℕ) (v₂ : ℕ → ℂ),
      (IsArithmeticPolygon a₁ N₁ v₁ ∧ IsSimpleClosedPolygon N₁ v₁ ∧
        polygonReflexCount N₁ v₁ = 0) ∧
      (IsArithmeticPolygon a₂ N₂ v₂ ∧ IsSimpleClosedPolygon N₂ v₂ ∧
        polygonReflexCount N₂ v₂ = 0) ∧
      ¬ (a₁ = a₂ ∧ N₁ = N₂ ∧ ∃ f : ℂ ≃ᵢ ℂ, ∀ k, v₂ k = f (v₁ k)) ∧
      ∀ (a N : ℕ) (v : ℕ → ℂ), IsArithmeticPolygon a N v → IsSimpleClosedPolygon N v →
        polygonReflexCount N v = 0 →
        (a = a₁ ∧ N = N₁ ∧ ∃ f : ℂ ≃ᵢ ℂ, ∀ k, v k = f (v₁ k)) ∨
        (a = a₂ ∧ N = N₂ ∧ ∃ f : ℂ ≃ᵢ ℂ, ∀ k, v k = f (v₂ k))

/-- Chainsaw process: every SoCS solution `(a, b, a + N)` comes from an
arithmetic polygon with side lengths `a + 1, …, a + N` that is not
self-intersecting.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Theorem 6 (`integers-2026-A1-thm-6`). -/
public theorem_wanted exists_simple_arithmeticPolygon (a N : ℕ) (b : ℤ)
    (h : IsSoCSSolution a b (a + N)) :
    ∃ v, IsArithmeticPolygon a N v ∧ IsSimpleClosedPolygon N v

/-- An arithmetic polygon with `N` sides and at most `ν` interior angles
greater than `π` has `N ≤ 8 + 3π²(ν + 2)²`. Stated for non-self-intersecting
polygons, where interior angles are defined (the paper's proof uses the
interior angle sum `π(N - 2)`), and for `ν ∈ ℕ` (negative `ν` is vacuous).

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Theorem 7 (`integers-2026-A1-thm-7`). -/
public theorem_wanted arithmeticPolygon_sides_le_of_reflexCount_le (a N : ℕ) (v : ℕ → ℂ)
    (hv : IsArithmeticPolygon a N v) (hs : IsSimpleClosedPolygon N v) (ν : ℕ)
    (hμ : polygonReflexCount N v ≤ ν) :
    (N : ℝ) ≤ 8 + 3 * Real.pi ^ 2 * (ν + 2) ^ 2

end

end MetaMathlibExt
