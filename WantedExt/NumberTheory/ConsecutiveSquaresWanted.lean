/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Topology.MetricSpace.Isometry
public import MathlibExt.NumberTheory.ConsecutiveSquares

namespace MetaMathlibExt

@[expose] public section

/-- **The Pell-type parameter is a positive nonsquare.** For every solution $(a, b, c)$ of the
sum of consecutive squares problem, the integer
$A = 3(b - c)^2\bigl(12(b - a)^2(c - b)^2 - (a - 2b + c)^4\bigr)$ is positive and is not a
perfect square.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Corollary 1
(`integers-2026-A1-cor-1`), verified against arXiv:2411.08398 (the formula
is garbled in the statement extraction). -/
public theorem_wanted soCS_pell_param_pos_nonsquare (a b c : ℤ)
    (h : IsSoCSSolution a b c) :
    0 < 3 * (b - c) ^ 2 * (12 * (b - a) ^ 2 * (c - b) ^ 2 - (a - 2 * b + c) ^ 4) ∧
    ¬ IsSquare (3 * (b - c) ^ 2 * (12 * (b - a) ^ 2 * (c - b) ^ 2 - (a - 2 * b + c) ^ 4))

/-- **Infinite families of solutions in a plane.** Let $(a, b, c)$ be a solution of the sum of
consecutive squares problem. Then there are infinitely many distinct integer triples $(x, y, z)$
satisfying the sum of consecutive squares equation
$2\,y(y+1)(2y+1) = x(x+1)(2x+1) + z(z+1)(2z+1)$, with no order or sign condition, such that
$(b - c)x + (c - a)y + (a - b)z = 0$ and $z - x \equiv c - a \pmod 2$.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Proposition 1
(`integers-2026-A1-prop-1`). -/
public theorem_wanted soCS_infinite_family_plane (a b c : ℤ)
    (h : IsSoCSSolution a b c) :
    ∃ f : ℕ → ℤ × ℤ × ℤ, Function.Injective f ∧
      ∀ n, SoCSEq (f n).1 (f n).2.1 (f n).2.2 ∧
        (b - c) * (f n).1 + (c - a) * (f n).2.1 + (a - b) * (f n).2.2 = 0 ∧
        (f n).2.2 - (f n).1 ≡ c - a [ZMOD 2]

/-- **Solutions with odd span $c - a$.** For every odd integer $N \ge 3$ there is a solution
$(a, b, c)$ of the sum of consecutive squares problem with $c - a = N$, together with infinitely
many distinct solutions $(x, y, z)$ of that problem with $z - x$ odd, all lying in the plane
$(b - c)x + (c - a)y + (a - b)z = 0$, which passes through $(a, b, c)$ and contains the line
$x = y = z$.

The paper also states that this plane is unique for each $N$; that uniqueness clause is not part
of this statement.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Theorem 2
(`integers-2026-A1-thm-2`), verified against arXiv:2411.08398. -/
public theorem_wanted soCS_odd_span (N : ℤ) (hN : Odd N) (h3 : 3 ≤ N) :
    ∃ a b c : ℤ, IsSoCSSolution a b c ∧ c - a = N ∧
    ∃ f : ℕ → ℤ × ℤ × ℤ, Function.Injective f ∧
      ∀ n, IsSoCSSolution (f n).1 (f n).2.1 (f n).2.2 ∧
        Odd ((f n).2.2 - (f n).1) ∧
        (b - c) * (f n).1 + (c - a) * (f n).2.1 + (a - b) * (f n).2.2 = 0

/-- **No finitely many planes contain all solutions.** Let $S$ be a finite set of affine planes
$ux + vy + wz = t$ in $\mathbb{R}^3$, with $u, v, w, t$ real and $(u, v, w) \ne (0, 0, 0)$. Then
some solution $(a, b, c)$ of the sum of consecutive squares problem lies on none of the planes in
$S$, that is, $ua + vb + wc \ne t$ for every plane in $S$.

Source: Anderson, Woodall and Zaharescu, *Arithmetic Polygons and Sums of
Consecutive Squares*, INTEGERS 26 (2026), Article A1, Corollary 2
(`integers-2026-A1-cor-2`); the proof text appended to the extracted
statement is not part of the claim. -/
public theorem_wanted soCS_not_finite_planes
    (S : Finset (ℝ × ℝ × ℝ × ℝ))
    (hS : ∀ p ∈ S, (p.1, p.2.1, p.2.2.1) ≠ 0) :
    ∃ a b c : ℤ, IsSoCSSolution a b c ∧
      ∀ p ∈ S, p.1 * (a : ℝ) + p.2.1 * (b : ℝ) + p.2.2.1 * (c : ℝ) ≠ p.2.2.2

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
