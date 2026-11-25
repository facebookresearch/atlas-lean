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
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Primitive Pythagorean triples with a square leg

Applying Euclid's formula twice gives infinitely many primitive triples with a square second leg
and two positive square summands for each of the other sides. For even `t ≥ 2`, use the parameters
`t⁴ + 1` and `2t²`, whose squares differ by `(t⁴ - 1)²`.
-/

namespace MathlibExt.NumberTheory.PrimitivePythagoreanFormsWanted

/-- **Infinitely many primitive Pythagorean triples with a square leg.** There are infinitely
many triples $(X, Y, Z)$ of natural numbers with $X^2 + Y^2 = Z^2$ and $\gcd(X, Y) = 1$ such that
$X$ and $Z$ are each a sum of two squares of positive integers and $Y$ is the square of a
positive integer.

Source: Yangcheng Li and Yong Zhang, "Primitive Pythagorean Triangles
with Sides of Certain Forms", Corollary 1. -/
public theorem primitive_pythagorean_sides_square_middle_infinite :
    Set.Infinite
      {(X, Y, Z) : ℕ × ℕ × ℕ |
        X ^ 2 + Y ^ 2 = Z ^ 2 ∧ Nat.Coprime X Y ∧
          ∃ x y p r s : ℕ,
            0 < x ∧ 0 < y ∧ 0 < p ∧ 0 < r ∧ 0 < s ∧
              X = x ^ 2 + y ^ 2 ∧ Y = p ^ 2 ∧ Z = r ^ 2 + s ^ 2} := by
  let t (n : ℕ) := 2 * (n + 1)
  let triangle (n : ℕ) : ℕ × ℕ × ℕ :=
    let k := t n
    (4 * k ^ 2 * (k ^ 4 + 1), (k ^ 4 - 1) ^ 2, (k ^ 4 + 1) ^ 2 + (2 * k ^ 2) ^ 2)
  have hmono : StrictMono (fun n => (triangle n).1) := by
    intro i j hij
    dsimp [triangle, t]
    gcongr
  apply (Set.infinite_range_of_injective (f := triangle)
    (fun _ _ h => hmono.injective (congrArg Prod.fst h))).mono
  rintro _ ⟨n, rfl⟩
  dsimp only [triangle, Set.mem_ofPred_eq]
  have ht : 1 < t n := by dsimp [t]; omega
  have hpow : 1 < t n ^ 4 := one_lt_pow₀ ht (by decide)
  refine ⟨?_, ?_, ?_⟩
  · zify [hpow.le]
    ring
  · -- The square root of the second leg is coprime to both factors of the first leg.
    have hprev : Nat.Coprime (t n ^ 4) (t n ^ 4 - 1) :=
      (Nat.coprime_self_sub_right hpow.le).2 (Nat.coprime_one_right _)
    have hfactor : Nat.Coprime (4 * t n ^ 2) (t n ^ 4 - 1) :=
      hprev.coprime_dvd_left ⟨(n + 1) ^ 2, by dsimp [t]; ring⟩
    have htwo : Nat.Coprime 2 (t n ^ 4 - 1) :=
      hfactor.coprime_dvd_left ⟨2 * t n ^ 2, by ring⟩
    apply Nat.Coprime.pow_right
    apply Nat.Coprime.mul_left hfactor
    rw [show t n ^ 4 + 1 = 2 + (t n ^ 4 - 1) by omega, Nat.coprime_add_self_left]
    exact htwo
  · refine ⟨2 * t n ^ 3, 2 * t n, t n ^ 4 - 1, t n ^ 4 + 1, 2 * t n ^ 2,
      ?_, ?_, Nat.sub_pos_of_lt hpow, ?_, ?_, by ring, rfl, rfl⟩
    all_goals positivity

end MathlibExt.NumberTheory.PrimitivePythagoreanFormsWanted
