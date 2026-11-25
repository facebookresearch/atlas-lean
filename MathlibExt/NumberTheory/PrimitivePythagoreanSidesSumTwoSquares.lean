/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Primitive Pythagorean triples with sides sums of two squares

With `t = (n + 2) * (n + 3)`, the consecutive Euclidean parameters `t²` and `t² + 1`
give infinitely many primitive triples whose three sides are sums of two positive squares.
The choice of `t` makes the odd leg a sum of squares via
`2t² + 1 = (k(k + 2))² + ((k - 1)(k + 1))²` for `k = n + 2`.
-/

namespace MathlibExt.NumberTheory.PrimitivePythagoreanFormsWanted

/-- **Infinitely many primitive Pythagorean triples with sides sums of two squares.** There are
infinitely many triples $(X, Y, Z)$ of natural numbers with $X^2 + Y^2 = Z^2$ and
$\gcd(X, Y) = 1$ such that each of $X$, $Y$ and $Z$ is a sum of two squares of positive
integers.

Source: Yangcheng Li and Yong Zhang, "Primitive Pythagorean Triangles
with Sides of Certain Forms", Theorem 1. -/
public theorem primitive_pythagorean_sides_sum_two_squares_infinite :
    Set.Infinite
      {(X, Y, Z) : ℕ × ℕ × ℕ |
        X ^ 2 + Y ^ 2 = Z ^ 2 ∧ Nat.Coprime X Y ∧
          ∃ x y p q r s : ℕ,
            0 < x ∧ 0 < y ∧ 0 < p ∧ 0 < q ∧ 0 < r ∧ 0 < s ∧
              X = x ^ 2 + y ^ 2 ∧ Y = p ^ 2 + q ^ 2 ∧
                Z = r ^ 2 + s ^ 2} := by
  let t (n : ℕ) := (n + 2) * (n + 3)
  let triangle (n : ℕ) : ℕ × ℕ × ℕ :=
    let a := t n ^ 2
    (2 * a + 1, 2 * a * (a + 1), a ^ 2 + (a + 1) ^ 2)
  have hmono : StrictMono (fun n => (triangle n).1) := by
    intro i j hij
    dsimp [triangle, t]
    gcongr
  apply (Set.infinite_range_of_injective (f := triangle)
    (fun _ _ h => hmono.injective (congrArg Prod.fst h))).mono
  rintro _ ⟨n, rfl⟩
  dsimp only [triangle, Set.mem_ofPred_eq]
  refine ⟨by ring, ?_, ?_⟩
  · -- The square of the odd leg is one more than twice the even leg.
    apply (Nat.coprime_pow_left_iff (by decide : 0 < 2) _ _).mp
    rw [show (2 * t n ^ 2 + 1) ^ 2 = 2 * (2 * t n ^ 2 * (t n ^ 2 + 1)) + 1 by ring,
      Nat.coprime_mul_right_add_left]
    exact Nat.coprime_one_left _
  · have ht : 1 < t n := by dsimp [t]; nlinarith
    have hsub : 0 < t n - 1 := Nat.sub_pos_of_lt ht
    refine ⟨(n + 2) * (n + 4), (n + 1) * (n + 3), t n * (t n - 1), t n * (t n + 1),
      t n ^ 2, t n ^ 2 + 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    all_goals try positivity
    · dsimp [t]
      ring
    · cases t n <;> simp
      ring

end MathlibExt.NumberTheory.PrimitivePythagoreanFormsWanted
