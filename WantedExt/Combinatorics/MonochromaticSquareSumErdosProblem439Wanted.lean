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

/-- **Erdős Problem 439 for squares.** The statement that for every colouring of the positive
integers with finitely many colours there are distinct positive integers $x$ and $y$ of the same
colour such that $x + y$ is a perfect square. -/
def monochromaticSquareSum : Prop :=
  ∀ r : ℕ, ∀ c : ℕ → Fin r, ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x ≠ y ∧ c x = c y ∧ IsSquare (x + y)

/-- **Erdős Problem 439 for $k$-th powers.** The statement that for every integer $k \ge 2$ and
every colouring of the positive integers with finitely many colours there are distinct positive
integers $x$ and $y$ of the same colour such that $x + y = z^k$ for some natural number $z$. -/
def monochromaticPowerSum : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ r : ℕ, ∀ c : ℕ → Fin r,
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x ≠ y ∧ c x = c y ∧ ∃ z : ℕ, x + y = z ^ k

/--
**Erdős Problem 439 for squares is true.** For every colouring of the positive integers with
finitely many colours there are distinct positive integers $x$ and $y$ of the same colour such
that $x + y$ is a perfect square.

This is the case $f(z) = z^2$ of a theorem of Khalfalah and Szemerédi on monochromatic
solutions of $x + y = f(z)$; Erdős, Sárközy and Sós had proved the cases of $2$ and $3$ colours.

Source: T. F. Bloom, Erdős Problems, Problem #439,
https://www.erdosproblems.com/439 (status PROVED); resolution: A. Khalfalah and E. Szemerédi, On the
number of monochromatic solutions of x + y = z², Combin. Probab. Comput. (2006), 213-227, main
theorem (a conjecture of Erdős, Roth, Sárközy and Sós): for every nonconstant f ∈ ℤ[z] with 2 ∣ f(z)
for some z ∈ ℤ, every finite colouring of the integers has x ≠ y of the same colour with x + y =
f(z) (abstract; erdosproblems.com/439), https://doi.org/10.1017/S0963548305007169.
-/
public theorem_wanted monochromaticSquareSum_holds : monochromaticSquareSum

/--
**Erdős Problem 439 for $k$-th powers is true.** For every integer $k \ge 2$ and every colouring
of the positive integers with finitely many colours there are distinct positive integers $x$ and
$y$ of the same colour such that $x + y = z^k$ for some natural number $z$.

Khalfalah and Szemerédi proved the corresponding statement for $x + y = f(z)$ for every
nonconstant polynomial $f$ with integer coefficients such that $f(z)$ is even for some integer
$z$; the polynomial $f(z) = z^k$ qualifies, since $f(2) = 2^k$.

Source: T. F. Bloom, Erdős Problems, Problem #439,
https://www.erdosproblems.com/439 (status PROVED); resolution: A. Khalfalah and E. Szemerédi, On the
number of monochromatic solutions of x + y = z², Combin. Probab. Comput. (2006), 213-227, main
theorem (a conjecture of Erdős, Roth, Sárközy and Sós): for every nonconstant f ∈ ℤ[z] with 2 ∣ f(z)
for some z ∈ ℤ, every finite colouring of the integers has x ≠ y of the same colour with x + y =
f(z) (abstract; erdosproblems.com/439), https://doi.org/10.1017/S0963548305007169.
-/
public theorem_wanted monochromaticPowerSum_holds : monochromaticPowerSum

end MathlibExt.Combinatorics.MonochromaticSquareSumErdosProblem439Wanted
