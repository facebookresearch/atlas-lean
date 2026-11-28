/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Ring.Identities
import Mathlib.Basic.Finite.Sum
import Mathlib.Data.Rat.Lemmas
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Tactic.Choose
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Triples with square elementary symmetric functions

Quotients of nonzero sums of two rational squares are sums of two rational squares.
Applying this to the roots of a cubic gives two-square representations for each entry of a
rational triple with square elementary symmetric functions. A common square factor scales
the triple to an integer solution. Choudhry's family (3.3) gives an explicit integer triple
with this square property for every pair of integer parameters. For a triple of integer squares,
only the sum and the sum of pairwise products need to be checked: the product is already a square.

## References

* Ajai Choudhry, *Three Integers Whose Sum, Product, and the Sum of the Products of the Integers,
  Taken Two at a Time, Are Perfect Squares*, INTEGERS 26 (2026), Article A35, pp. 1–15,
  Lemmas 1–3 and Theorem 1, family (3.3). https://math.colgate.edu/~integers/aa35/aa35.pdf
-/

@[expose] public section

namespace MathlibExt.NumberTheory.ThreeIntegersSymmetricSquaresWanted

/-- **Sums of two rational squares.** A rational number $q$ is a sum of two squares when
$q = x^2 + y^2$ for some rational numbers $x$ and $y$. -/
def IsSumTwoSquaresℚ (q : ℚ) : Prop :=
  ∃ x y : ℚ, q = x ^ 2 + y ^ 2

/-- **Quotients of sums of two rational squares.** If $\alpha$ and $\beta$ are nonzero rational
numbers that are each a sum of two squares of rational numbers, then $\alpha / \beta$ is also a
sum of two squares of rational numbers.

Source: Ajai Choudhry, "Three Integers Whose Sum, Product, and the Sum of the Products of the
Integers, Taken Two at a Time, Are Perfect Squares", Lemma 1. -/
theorem sum_two_squares_div_sum_two_squaresℚ
    {α β : ℚ} (hα : α ≠ 0) (hβ : β ≠ 0)
    (hα₂ : IsSumTwoSquaresℚ α) (hβ₂ : IsSumTwoSquaresℚ β) :
    IsSumTwoSquaresℚ (α / β) := by
  obtain ⟨a, b, rfl⟩ := hα₂
  obtain ⟨c, d, hcd⟩ := hβ₂
  refine ⟨(a * c - b * d) / β, (a * d + b * c) / β, ?_⟩
  rw [div_pow, div_pow, ← add_div, ← sq_add_sq_mul_sq_add_sq, ← hcd, sq β,
    mul_div_mul_right _ _ hβ]

/-- **Integer triples with square elementary symmetric functions.** Integers $a$, $b$ and $c$
have square elementary symmetric functions when $a + b + c$, $ab + bc + ca$ and $abc$ are each
the square of an integer. -/
def HasSquareElementarySymmetricFunctions (a b c : ℤ) : Prop :=
  IsSquare (a + b + c) ∧
    IsSquare (a * b + b * c + c * a) ∧
    IsSquare (a * b * c)

/-- **Square entries reduce the symmetric-square condition to two checks.** If $a$, $b$ and $c$
are squares of integers, then all three elementary symmetric functions of $a$, $b$ and $c$ are
squares of integers if and only if both $a + b + c$ and $ab + bc + ca$ are squares of integers. -/
theorem hasSquareElementarySymmetricFunctions_iff_of_isSquare {a b c : ℤ}
    (ha : IsSquare a) (hb : IsSquare b) (hc : IsSquare c) :
    HasSquareElementarySymmetricFunctions a b c ↔
      IsSquare (a + b + c) ∧ IsSquare (a * b + b * c + c * a) := by
  constructor
  · rintro ⟨hsum, hpairs, _⟩
    exact ⟨hsum, hpairs⟩
  · rintro ⟨hsum, hpairs⟩
    exact ⟨hsum, hpairs, (ha.mul hb).mul hc⟩

/-- **Pairwise products preserve square symmetric functions.** If $a$, $b$, $c$ are integers
such that each of $a + b + c$, $ab + bc + ca$ and $abc$ is the square of an integer, then the
same holds for the triple $ab$, $bc$, $ca$.

Source: Ajai Choudhry, "Three Integers Whose Sum, Product, and the Sum of the Products of the
Integers, Taken Two at a Time, Are Perfect Squares", Lemma 2. -/
theorem hasSquareElementarySymmetricFunctions_pairwise_products
    {a b c : ℤ}
    (h : HasSquareElementarySymmetricFunctions a b c) :
    HasSquareElementarySymmetricFunctions (a * b) (b * c) (c * a) := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩⟩ := h
  refine ⟨⟨y, hy⟩, ⟨z * x, ?_⟩, ⟨a * b * c, by ring⟩⟩
  calc (a * b) * (b * c) + (b * c) * (c * a) + (c * a) * (a * b)
      = (a * b * c) * (a + b + c) := by ring
    _ = (z * z) * (x * x) := by rw [hz, hx]
    _ = (z * x) * (z * x) := by ring

/-- **Rationals with square elementary symmetric functions.** Rational numbers $a$, $b$, $c$
have square elementary symmetric functions when each of $a + b + c$, $ab + bc + ca$ and $abc$
is the square of a rational number. -/
def HasSquareElementarySymmetricFunctionsℚ (a b c : ℚ) : Prop :=
  IsSquare (a + b + c) ∧
    IsSquare (a * b + b * c + c * a) ∧
    IsSquare (a * b * c)

/-- **Sums of two integer squares.** An integer $z$ is a sum of two squares when $z = x^2 + y^2$
for some integers $x$ and $y$. -/
def IsSumTwoSquaresℤ (z : ℤ) : Prop :=
  ∃ x y : ℤ, z = x ^ 2 + y ^ 2

private theorem isSumTwoSquares_of_root {a b c f g h x : ℚ}
    (hf : a + b + c = f * f) (hg : a * b + b * c + c * a = g * g) (hh : a * b * c = h * h)
    (hx : (x - a) * (x - b) * (x - c) = 0) : IsSumTwoSquaresℚ x := by
  by_cases hzero : x = 0
  · exact ⟨0, 0, by simp [hzero]⟩
  have hd : x ^ 2 + g ^ 2 ≠ 0 :=
    (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hzero) (sq_nonneg g)).ne'
  have heq : x * (x ^ 2 + g ^ 2) = (x * f) ^ 2 + h ^ 2 := by
    linear_combination hx + x ^ 2 * hf - x * hg + hh
  rw [← mul_div_cancel_right₀ x hd, heq]
  exact sum_two_squares_div_sum_two_squaresℚ (heq ▸ mul_ne_zero hzero hd) hd
    ⟨x * f, h, rfl⟩ ⟨x, g, rfl⟩

-- Clear both coordinates of every representation with one denominator.
private theorem scale_sums_of_squares {s : Finset ℚ} (hs : ∀ x ∈ s, IsSumTwoSquaresℚ x) :
    ∃ d : ℚ, d ≠ 0 ∧ ∀ x ∈ s, ∃ z : ℤ, (z : ℚ) = d ^ 2 * x ∧ IsSumTwoSquaresℤ z := by
  choose u v huv using fun x : s => hs x x.property
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (Sum.elim u v)
  refine ⟨(d.val : ℚ), by exact_mod_cast nonZeroDivisors.coe_ne_zero d, ?_⟩
  intro x hx
  let i : s := ⟨x, hx⟩
  obtain ⟨U, hU⟩ := hd (Sum.inl i)
  obtain ⟨V, hV⟩ := hd (Sum.inr i)
  simp only [eq_intCast, zsmul_eq_mul, Sum.elim_inl, Sum.elim_inr] at hU hV
  refine ⟨U ^ 2 + V ^ 2, ?_, U, V, rfl⟩
  push_cast
  rw [hU, hV]
  linear_combination -(d.val : ℚ) ^ 2 * huv i

/-- **Rational solutions are sums of two squares and rescale to integer solutions.** Let $a$, $b$,
$c$ be rational numbers such that $a + b + c$, $ab + bc + ca$ and $abc$ are squares of rational
numbers. Then each of $a$, $b$ and $c$ is a sum of two squares of rational numbers. Moreover,
there is a nonzero rational number $k$ such that $A = ka$, $B = kb$ and $C = kc$ are integers,
$A + B + C$, $AB + BC + CA$ and $ABC$ are squares of integers, and each of $A$, $B$ and $C$ is a
sum of two squares of integers.

Source: Ajai Choudhry, "Three Integers Whose Sum, Product, and the Sum of the Products of the
Integers, Taken Two at a Time, Are Perfect Squares", Lemma 3. -/
theorem isSumTwoSquaresℚ_of_hasSquareElementarySymmetricFunctionsℚ_and_scaling
    {a b c : ℚ}
    (h : HasSquareElementarySymmetricFunctionsℚ a b c) :
    IsSumTwoSquaresℚ a ∧
      IsSumTwoSquaresℚ b ∧
      IsSumTwoSquaresℚ c ∧
      ∃ (k : ℚ) (A B C : ℤ),
        k ≠ 0 ∧
          (A : ℚ) = k * a ∧
          (B : ℚ) = k * b ∧
          (C : ℚ) = k * c ∧
          HasSquareElementarySymmetricFunctions A B C ∧
          IsSumTwoSquaresℤ A ∧
          IsSumTwoSquaresℤ B ∧
          IsSumTwoSquaresℤ C := by
  obtain ⟨⟨f, hf⟩, ⟨g, hg⟩, ⟨t, ht⟩⟩ := h
  have reps (x : ℚ) (hx : x ∈ ({a, b, c} : Finset ℚ)) : IsSumTwoSquaresℚ x := by
    apply isSumTwoSquares_of_root hf hg ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> simp
  refine ⟨reps a (by simp), reps b (by simp), reps c (by simp), ?_⟩
  obtain ⟨d, hd, scaled⟩ := scale_sums_of_squares reps
  obtain ⟨A, hA, sA⟩ := scaled a (by simp)
  obtain ⟨B, hB, sB⟩ := scaled b (by simp)
  obtain ⟨C, hC, sC⟩ := scaled c (by simp)
  refine ⟨d ^ 2, A, B, C, pow_ne_zero _ hd, hA, hB, hC, ?_, sA, sB, sC⟩
  -- The three symmetric functions are homogeneous of degrees one, two and three.
  refine ⟨Rat.isSquare_intCast_iff.mp ⟨d * f, ?_⟩,
    Rat.isSquare_intCast_iff.mp ⟨d ^ 2 * g, ?_⟩,
    Rat.isSquare_intCast_iff.mp ⟨d ^ 3 * t, ?_⟩⟩
  all_goals push_cast; rw [hA, hB, hC]
  · linear_combination d ^ 2 * hf
  · linear_combination d ^ 4 * hg
  · linear_combination d ^ 6 * ht

/-- **Choudhry's family (3.3) of integer triples with square symmetric functions.** For all
integers $s$ and $t$, put $a = t^2 (s^2 - t^2)^2 (s^2 + t^2)$, $b = s^2 (s^2 - t^2)^2 (s^2 + t^2)$
and $c = 4 s^4 t^4$. Then each of $a + b + c$, $ab + bc + ca$ and $abc$ is the square of an
integer.

Source: Ajai Choudhry, "Three Integers Whose Sum, Product, and the Sum of the Products of the
Integers, Taken Two at a Time, Are Perfect Squares", Theorem 1, family (3.3). -/
theorem hasSquareElementarySymmetricFunctions_family33
    (s t : ℤ) :
    HasSquareElementarySymmetricFunctions
      (t ^ 2 * (s ^ 2 - t ^ 2) ^ 2 * (s ^ 2 + t ^ 2))
      (s ^ 2 * (s ^ 2 - t ^ 2) ^ 2 * (s ^ 2 + t ^ 2))
      (4 * s ^ 4 * t ^ 4) := by
  refine ⟨⟨s ^ 4 + t ^ 4, ?_⟩,
    ⟨s * t * (s ^ 2 - t ^ 2) * (s ^ 2 + t ^ 2) ^ 2, ?_⟩,
    ⟨2 * s ^ 3 * t ^ 3 * (s ^ 2 - t ^ 2) ^ 2 * (s ^ 2 + t ^ 2), ?_⟩⟩ <;> ring

end MathlibExt.NumberTheory.ThreeIntegersSymmetricSquaresWanted
