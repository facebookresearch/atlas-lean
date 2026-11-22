/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Monochromatic pairs with square sum (Erdős Problem 439)

Erdős Problem 439: in every finite colouring of the integers, must there be `x ≠ y` of the same
colour with `x + y` a square? What about a `k`-th power?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Nat.Defs

@[expose] public section

namespace MathlibExt.Combinatorics.MonochromaticSquareSumErdosProblem439Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #439, https://www.erdosproblems.com/439 (status
PROVED). UnsolvedMath record UM-30006870 (`EP-439`), dataset ulamai/UnsolvedMath v1.8.0.

Colourings are maps `ℕ → Fin r` and `x, y` are positive integers, as in the page's restatement (the
graph on `ℕ` joining `m` and `n` when `m + n` is a square has chromatic number `ℵ₀`); this implies
the statement for colourings of `ℤ`, which restrict to the positive integers. The `k`-th power
question is stated for every `k ≥ 2`. formal-conjectures has no statement of this problem.
-/

/-- Erdős Problem 439, first question: in every colouring of the positive integers with finitely
many colours there are `x ≠ y` of the same colour with `x + y` a perfect square. -/
def monochromaticSquareSum : Prop :=
  ∀ r : ℕ, ∀ c : ℕ → Fin r, ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x ≠ y ∧ c x = c y ∧ IsSquare (x + y)

/-- Erdős Problem 439, second question: for every `k ≥ 2`, in every colouring of the positive
integers with finitely many colours there are `x ≠ y` of the same colour with `x + y` a `k`-th
power. -/
def monochromaticPowerSum : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ r : ℕ, ∀ c : ℕ → Fin r,
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x ≠ y ∧ c x = c y ∧ ∃ z : ℕ, x + y = z ^ k

/--
Resolved true: Khalfalah and Szemerédi proved that every finite colouring of the integers has `x ≠
y` of the same colour with `x + y` a square, the case `f(z) = z²` of their theorem (Erdős, Sárközy
and Sós had done 2 and 3 colours); erdosproblems.com/439 lists the problem as proved and restates it
for the graph on `ℕ`. Source: T. F. Bloom, Erdős Problems, Problem #439,
https://www.erdosproblems.com/439 (status PROVED); resolution: A. Khalfalah and E. Szemerédi, On the
number of monochromatic solutions of x + y = z², Combin. Probab. Comput. (2006), 213-227, main
theorem (a conjecture of Erdős, Roth, Sárközy and Sós): for every nonconstant f ∈ ℤ[z] with 2 ∣ f(z)
for some z ∈ ℤ, every finite colouring of the integers has x ≠ y of the same colour with x + y =
f(z) (abstract; erdosproblems.com/439), https://doi.org/10.1017/S0963548305007169.
-/
public theorem_wanted monochromaticSquareSum_holds : monochromaticSquareSum

/--
Resolved true: the theorem of Khalfalah and Szemerédi covers `x + y = f(z)` for every nonconstant `f
∈ ℤ[z]` such that `f(z)` is even for some integer `z`; `f(z) = z^k` with `k ≥ 2` qualifies, since
`f(2) = 2^k` (erdosproblems.com/439). Source: T. F. Bloom, Erdős Problems, Problem #439,
https://www.erdosproblems.com/439 (status PROVED); resolution: A. Khalfalah and E. Szemerédi, On the
number of monochromatic solutions of x + y = z², Combin. Probab. Comput. (2006), 213-227, main
theorem (a conjecture of Erdős, Roth, Sárközy and Sós): for every nonconstant f ∈ ℤ[z] with 2 ∣ f(z)
for some z ∈ ℤ, every finite colouring of the integers has x ≠ y of the same colour with x + y =
f(z) (abstract; erdosproblems.com/439), https://doi.org/10.1017/S0963548305007169.
-/
public theorem_wanted monochromaticPowerSum_holds : monochromaticPowerSum

end MathlibExt.Combinatorics.MonochromaticSquareSumErdosProblem439Wanted
