/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Amato's products of Pythagorean triples

Amato's product preserves rational Pythagorean triples with nonzero first coordinate.
This module also gives the cathetus parameters and the product on rational pairs.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Amato's cathetus parameter set.** For a natural number $x$, let $n$ be the exponent of $2$
in $x$ (taken to be $0$ for $x = 0$). The set $C(x)$ consists of the natural numbers $d$ with
$d \le x$ and $d \mid x^2$ such that, if $x$ is even, $d = 2^s l$ for some natural numbers $s$ and
$l$ with $1 \le s \le n - 1$ and $l \mid x^2$.

This is the definition as printed in the source: for odd $x$ it is
$D(x) = \{d \in \mathbb{N} : d \le x,\ d \mid x^2\}$, and for even $x = 2^n k$ with $k$ odd it is
$D(x) \cap P(x)$ with $P(x) = \{2^s l : l \mid x^2,\ s \in \{1, \dots, n - 1\}\}$.

Source: Roberto Amato, *Groups and Monoid in the Set of Pythagorean Triples*, INTEGERS 24 (2024),
Article A5, Theorem 1 (quoting [1]) (`integers-2024-A5-thm-1`). -/
def amatoCathetusParams (x : ℕ) : Set ℕ :=
  {d | d ≤ x ∧ d ∣ x ^ 2 ∧
    (Even x → ∃ s l : ℕ, 1 ≤ s ∧ s ≤ padicValNat 2 x - 1 ∧ l ∣ x ^ 2 ∧ d = 2 ^ s * l)}

/-- **Amato's parameter set for the cathetus $3$ contains $1$.** We have $1 \in C(3)$, where
$C(x)$ is Amato's cathetus parameter set.

The parameter $d = 1$ generates the triple $(3, 4, 5)$.

Source: Roberto Amato, *Groups and Monoid in the Set of Pythagorean Triples*, INTEGERS 24 (2024),
Article A5, Theorem 1 (quoting [1]) (`integers-2024-A5-thm-1`). -/
theorem one_mem_amatoCathetusParams_three : 1 ∈ amatoCathetusParams 3 :=
  ⟨by norm_num, by norm_num, fun h => absurd h (by decide)⟩

/-- **$2$ is an Amato parameter for the cathetus $4$.** The number $2$ belongs to Amato's parameter
set $C(4)$ for the cathetus $4$.

With $x = 4$ and $d = 2$, the formulas $x^2 / (2d) \mp d / 2$ give $3$ and $5$, so $2$ generates
the triple $(4, 3, 5)$.

Source: Roberto Amato, *Groups and Monoid in the Set of Pythagorean Triples*, INTEGERS 24 (2024),
Article A5, Theorem 1 (quoting [1]) (`integers-2024-A5-thm-1`). -/
theorem two_mem_amatoCathetusParams_four : 2 ∈ amatoCathetusParams 4 := by
  have h4 : padicValNat 2 4 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.padicValNat_def, Nat.multiplicity_prime_pow]
  refine ⟨by norm_num, by norm_num, fun _ => ⟨1, 1, le_refl 1, ?_, one_dvd _, by norm_num⟩⟩
  rw [h4]

/-- **Amato's product of triples.** For a commutative ring $R$, the product of two triples
$(x, y, z)$ and $(x', y', z')$ in $R^3$ is
$$(x, y, z) \star (x', y', z') = (x x',\ y z' + z y',\ y z' + z y' + (z - y)(z' - y')).$$

This is the source's product (4); its operation (12) on integral triples is the same formula.

Source: Roberto Amato, *Groups and Monoid in the Set of Pythagorean Triples*, INTEGERS 24 (2024),
Article A5, Lemma 1, (4) (`integers-2024-A5-lem-1`). -/
def pythagoreanTripleMul {R : Type*} [CommRing R] (u v : R × R × R) : R × R × R :=
  (u.1 * v.1, u.2.1 * v.2.2 + u.2.2 * v.2.1,
    u.2.1 * v.2.2 + u.2.2 * v.2.1 + (u.2.2 - u.2.1) * (v.2.2 - v.2.1))

/-- **Amato's product of $(3, 4, 5)$ with itself.** For integer triples,
$(3, 4, 5) \star (3, 4, 5) = (9, 40, 41)$, where $\star$ is Amato's product of triples.

Source: Roberto Amato, *Groups and Monoid in the Set of Pythagorean Triples*, INTEGERS 24 (2024),
Article A5, Lemma 1, (4) (`integers-2024-A5-lem-1`). -/
theorem pythagoreanTripleMul_three_four_five :
    pythagoreanTripleMul ((3, 4, 5) : ℤ × ℤ × ℤ) (3, 4, 5) = (9, 40, 41) := by
  norm_num [pythagoreanTripleMul]

/-- **Right identity for Amato's product.** For every commutative ring $R$ and every triple
$u \in R^3$, we have $u \star (1, 0, 1) = u$, where $\star$ is Amato's product of triples.

Source: Roberto Amato, *Groups and Monoid in the Set of Pythagorean Triples*, INTEGERS 24 (2024),
Article A5, Theorem 3, (7)-(8) (`integers-2024-A5-thm-3`). -/
theorem pythagoreanTripleMul_one {R : Type*} [CommRing R] (u : R × R × R) :
    pythagoreanTripleMul u (1, 0, 1) = u := by
  obtain ⟨x, y, z⟩ := u
  simp only [pythagoreanTripleMul, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

/-- **Rational Pythagorean triples.** The set $E$ consists of the triples $(x, y, z)$ of rational
numbers with $x \ne 0$ and $x^2 + y^2 = z^2$.

Source: Roberto Amato, *Groups and Monoid in the Set of Pythagorean Triples*, INTEGERS 24 (2024),
Article A5, Section 2, definition of `E` (`integers-2024-A5-lem-1`). -/
def ratPythagoreanTriples : Set (ℚ × ℚ × ℚ) :=
  {v | v.1 ≠ 0 ∧ v.1 ^ 2 + v.2.1 ^ 2 = v.2.2 ^ 2}

/-- **$(3, 4, 5)$ is a rational Pythagorean triple.** The triple $(3, 4, 5)$ belongs to the set $E$
of rational triples $(x, y, z)$ with $x \neq 0$ and $x^2 + y^2 = z^2$.

Source: Roberto Amato, *Groups and Monoid in the Set of Pythagorean Triples*, INTEGERS 24 (2024),
Article A5, Section 2, definition of `E` (`integers-2024-A5-lem-1`). -/
theorem three_four_five_mem_ratPythagoreanTriples :
    ((3, 4, 5) : ℚ × ℚ × ℚ) ∈ ratPythagoreanTriples :=
  ⟨by norm_num, by norm_num⟩

/-- **Amato's product preserves rational Pythagorean triples.** Let $E$ be the set of rational
triples $(x, y, z)$ with $x \ne 0$ and $x^2 + y^2 = z^2$, and let $\star$ be Amato's product of
triples. If $u \in E$ and $v \in E$, then $u \star v \in E$; that is, $\star$ is a binary
operation on $E$.

The source's fraction representation $(a/b, c/d, e/f)$ with $a, b, d, f \ne 0$ describes the
same set $E$.

Source: Roberto Amato, *Groups and Monoid in the Set of Pythagorean Triples*, INTEGERS 24 (2024),
Article A5, Lemma 1 (`integers-2024-A5-lem-1`). -/
theorem pythagoreanTripleMul_mem_ratPythagoreanTriples (u v : ℚ × ℚ × ℚ)
    (hu : u ∈ ratPythagoreanTriples) (hv : v ∈ ratPythagoreanTriples) :
    pythagoreanTripleMul u v ∈ ratPythagoreanTriples := by
  refine ⟨mul_ne_zero hu.1 hv.1, ?_⟩
  dsimp only [pythagoreanTripleMul]
  rw [mul_pow, eq_sub_of_add_eq hu.2, eq_sub_of_add_eq hv.2]
  ring

/-- **Amato's product on rational points of the unit circle.** For rational pairs $(x, y)$ and
$(x', y')$, the product is
$(x, y) \odot (x', y') = (x x' / (1 + y y'), (y + y') / (1 + y y'))$, where division by $0$
gives $0$; so the product is $(0, 0)$ when $1 + y y' = 0$.

For points $(a/c, b/c)$ and $(d/f, e/f)$ with $c, f \neq 0$ this reads
$(ad / (cf + eb), (bf + ec) / (cf + eb))$, the form (14)(I) of the source.

Source: Roberto Amato, *Groups and Monoid in the Set of Pythagorean Triples*, INTEGERS 24 (2024),
Article A5, Theorem 4, (14)(I) (`integers-2024-A5-thm-4`). -/
def unitCircleRatMul (p q : ℚ × ℚ) : ℚ × ℚ :=
  (p.1 * q.1 / (1 + p.2 * q.2), (p.2 + q.2) / (1 + p.2 * q.2))

/-- **Squaring $(3/5, 4/5)$ under Amato's product.** For Amato's product
$(x, y) \odot (x', y') = (x x' / (1 + y y'), (y + y') / (1 + y y'))$ on $\mathbb{Q}^2$, we have
$(3/5, 4/5) \odot (3/5, 4/5) = (9/41, 40/41)$.

Source: Roberto Amato, *Groups and Monoid in the Set of Pythagorean Triples*, INTEGERS 24 (2024),
Article A5, Theorem 4, (14)(I) (`integers-2024-A5-thm-4`). -/
theorem unitCircleRatMul_three_four_five :
    unitCircleRatMul (3 / 5, 4 / 5) (3 / 5, 4 / 5) = (9 / 41, 40 / 41) := by
  norm_num [unitCircleRatMul]

end

end MetaMathlibExt
