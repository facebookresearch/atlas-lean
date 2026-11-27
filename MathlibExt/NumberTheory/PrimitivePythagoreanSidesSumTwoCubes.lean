/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Primitive Pythagorean triangles with sides of certain forms

The source is Yangcheng Li and Yong Zhang, "Primitive Pythagorean
Triangles with Sides of Certain Forms", *INTEGERS* 24 (2024), Article
A31 (<https://math.colgate.edu/~integers/y31/y31.pdf>).

Ordered triples `(X, Y, Z)` have legs `X, Y` and hypotenuse `Z`. For an
integer Pythagorean triple, `Nat.Coprime X Y` is the primitivity
condition used here.

This module constructs infinitely many primitive triples whose three sides are
sums of two positive cubes. For `t = 6n + 4`, the Euclidean
parameters `t⁶` and `27` give the odd leg `t¹² - 729`. Its two cube bases are
`t(t³ - 9)` and `3(t³ - 3)`.
-/

set_option autoImplicit false

namespace MathlibExt.NumberTheory.PrimitivePythagoreanFormsWanted

/-- **Infinitely many primitive Pythagorean triples with sides sums of two cubes.** There are
infinitely many triples $(X, Y, Z)$ of natural numbers with $X^2 + Y^2 = Z^2$ and
$\gcd(X, Y) = 1$ such that each of $X$, $Y$ and $Z$ is a sum of two cubes of positive
integers.

Source: Yangcheng Li and Yong Zhang, "Primitive Pythagorean Triangles
with Sides of Certain Forms", Theorem 2. -/
public theorem primitive_pythagorean_sides_sum_two_cubes_infinite :
    Set.Infinite
      {(X, Y, Z) : ℕ × ℕ × ℕ |
        X ^ 2 + Y ^ 2 = Z ^ 2 ∧ Nat.Coprime X Y ∧
          ∃ x y p q r s : ℕ,
            0 < x ∧ 0 < y ∧ 0 < p ∧ 0 < q ∧ 0 < r ∧ 0 < s ∧
              X = x ^ 3 + y ^ 3 ∧ Y = p ^ 3 + q ^ 3 ∧
                Z = r ^ 3 + s ^ 3} := by
  let t (n : ℕ) := 6 * n + 4
  let triangle (n : ℕ) : ℕ × ℕ × ℕ :=
    let k := t n
    (k ^ 12 - 3 ^ 6, 2 * (3 * k ^ 2) ^ 3, k ^ 12 + 3 ^ 6)
  have hmono : StrictMono (fun n => (triangle n).2.2) := by
    intro i j hij
    dsimp [triangle, t]
    gcongr
  apply (Set.infinite_range_of_injective (f := triangle)
    (fun _ _ h => hmono.injective (congrArg (fun p => p.2.2) h))).mono
  rintro _ ⟨n, rfl⟩
  dsimp only [triangle, Set.mem_ofPred_eq]
  set k := t n with hk
  have hk4 : 4 ≤ k := by rw [hk]; dsimp [t]; omega
  have hpow : 3 ^ 6 ≤ k ^ 12 :=
    (by decide : 3 ^ 6 ≤ (4 : ℕ) ^ 12).trans (Nat.pow_le_pow_left hk4 _)
  refine ⟨?_, ?_, ?_⟩
  · zify [hpow]
    ring
  · -- The odd leg is coprime to every factor of the even leg.
    have hk3 : k.Coprime 3 := by
      rw [hk, show t n = (2 * n + 1) * 3 + 1 by dsimp [t]; ring,
        Nat.coprime_mul_right_add_left]
      decide
    have hcop : (k ^ 12).Coprime (3 ^ 6) := (hk3.pow_left 12).pow_right 6
    have htwo : (k ^ 12 - 3 ^ 6).Coprime 2 := by
      have heven : Even k := ⟨3 * n + 2, by rw [hk]; dsimp [t]; ring⟩
      exact (Nat.Even.sub_odd hpow (heven.pow_of_ne_zero (by decide)) (by decide)).coprime_two_right
    have hthree : (k ^ 12 - 3 ^ 6).Coprime 3 :=
      ((Nat.coprime_sub_self_left hpow).mpr hcop).coprime_dvd_right (by decide)
    have hparam : (k ^ 12 - 3 ^ 6).Coprime k :=
      ((Nat.coprime_self_sub_left hpow).mpr hcop.symm).coprime_dvd_right
        (dvd_pow_self _ (by decide))
    exact htwo.mul_right ((hthree.mul_right (hparam.pow_right 2)).pow_right 3)
  · have h9 : 9 < k ^ 3 :=
      (by decide : 9 < (4 : ℕ) ^ 3).trans_le (Nat.pow_le_pow_left hk4 _)
    have h3 : 3 < k ^ 3 := (by decide : 3 < 9).trans h9
    have hkpos : 0 < k := by omega
    have hsub9 : 0 < k ^ 3 - 9 := Nat.sub_pos_of_lt h9
    have hsub3 : 0 < k ^ 3 - 3 := Nat.sub_pos_of_lt h3
    refine ⟨k * (k ^ 3 - 9), 3 * (k ^ 3 - 3), 3 * k ^ 2, 3 * k ^ 2, k ^ 4, 3 ^ 2,
      by positivity, by positivity, by positivity, by positivity, by positivity, by decide,
      ?_, by ring, by ring⟩
    zify [hpow, h9.le, h3.le]
    ring

end MathlibExt.NumberTheory.PrimitivePythagoreanFormsWanted
