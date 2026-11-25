/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rational right triangles with sides sums of unit fractions

For each positive integer `k`, the pairwise sums of `1/(6k)`, `1/(3k)`, and `1/(2k)`
are the sides of a `3, 4, 5` triangle scaled by `1/(6k)`.
-/

namespace MathlibExt.NumberTheory.PrimitivePythagoreanFormsWanted

/-- **Infinitely many rational right triangles with sides sums of unit fractions.** There are
infinitely many triples $(X, Y, Z)$ of positive rational numbers with $X^2 + Y^2 = Z^2$ such
that each of $X$, $Y$ and $Z$ has the form $1/u + 1/v$ for some positive integers $u$ and $v$.

Source: Yangcheng Li and Yong Zhang, "Primitive Pythagorean Triangles
with Sides of Certain Forms", Theorem 3. -/
public theorem rational_right_triangles_reciprocal_sums_infinite :
    Set.Infinite
      {(X, Y, Z) : ℚ × ℚ × ℚ |
        0 < X ∧ 0 < Y ∧ 0 < Z ∧ X ^ 2 + Y ^ 2 = Z ^ 2 ∧
          ∃ x y p q r s : ℕ,
            0 < x ∧ 0 < y ∧ 0 < p ∧ 0 < q ∧ 0 < r ∧ 0 < s ∧
              X = 1 / (x : ℚ) + 1 / (y : ℚ) ∧
                Y = 1 / (p : ℚ) + 1 / (q : ℚ) ∧
                  Z = 1 / (r : ℚ) + 1 / (s : ℚ)} := by
  let triangle (n : ℕ) : ℚ × ℚ × ℚ :=
    let k := (n : ℚ) + 1
    (1 / (2 * k), 2 / (3 * k), 5 / (6 * k))
  have hinj : Function.Injective triangle := by
    intro m n h
    simpa [triangle, one_div] using congrArg Prod.fst h
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨n, rfl⟩
  dsimp [triangle]
  refine ⟨by positivity, by positivity, by positivity, ?_, ?_⟩
  · field_simp
    ring
  · let k := n + 1
    refine ⟨6 * k, 3 * k, 6 * k, 2 * k, 3 * k, 2 * k, ?_⟩
    refine ⟨by positivity, by positivity, by positivity, by positivity, by positivity,
      by positivity, ?_, ?_, ?_⟩
    all_goals
      push_cast [k]
      field_simp
      ring

end MathlibExt.NumberTheory.PrimitivePythagoreanFormsWanted
