/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.IntPythagoreanTriples
public import MathlibExt.NumberTheory.PythagoreanTripleGroupsPythagoreanCathetusProduct

namespace MetaMathlibExt

@[expose] public section

/-- **Group laws for Amato's product on rational Pythagorean triples.** Let $E$ be the set of
rational triples $(x, y, z)$ with $x \ne 0$ and $x^2 + y^2 = z^2$, and let $\star$ be Amato's
product of triples. Then $(1, 0, 1) \in E$; $(u \star v) \star w = u \star (v \star w)$ for all
$u, v, w \in E$; $u \star v = v \star u$ for all $u, v \in E$; $u \star (1, 0, 1) = u$ for every
$u \in E$; every $u \in E$ has some $v \in E$ with $u \star v = (1, 0, 1)$; and $E$ is infinite.

Together with the closure of $E$ under $\star$ (stated separately), this makes $E$ an infinite
commutative group under $\star$ with identity $(1, 0, 1)$.

Source: Roberto Amato, *Groups and Monoid in the Set of Pythagorean Triples*, INTEGERS 24 (2024),
Article A5, Theorem 3 (`integers-2024-A5-thm-3`). -/
public theorem_wanted ratPythagoreanTriples_commGroup :
    ((1, 0, 1) : ℚ × ℚ × ℚ) ∈ ratPythagoreanTriples ∧
      (∀ u ∈ ratPythagoreanTriples, ∀ v ∈ ratPythagoreanTriples, ∀ w ∈ ratPythagoreanTriples,
        pythagoreanTripleMul (pythagoreanTripleMul u v) w =
          pythagoreanTripleMul u (pythagoreanTripleMul v w)) ∧
      (∀ u ∈ ratPythagoreanTriples, ∀ v ∈ ratPythagoreanTriples,
        pythagoreanTripleMul u v = pythagoreanTripleMul v u) ∧
      (∀ u ∈ ratPythagoreanTriples, pythagoreanTripleMul u (1, 0, 1) = u) ∧
      (∀ u ∈ ratPythagoreanTriples, ∃ v ∈ ratPythagoreanTriples,
        pythagoreanTripleMul u v = (1, 0, 1)) ∧
      ratPythagoreanTriples.Infinite

/-- **Amato's group law on rational points of the unit circle.** Let
$P = \{(x, y) \in \mathbb{Q}^2 : x \neq 0,\ x^2 + y^2 = 1\}$ and let $\odot$ be Amato's product
$(x, y) \odot (x', y') = (x x' / (1 + y y'), (y + y') / (1 + y y'))$. Then $(1, 0) \in P$; for all
$p, q \in P$ we have $p \odot q \in P$; $\odot$ is associative and commutative on $P$; for every
$(x, y) \in P$ we have $(x, y) \odot (1, 0) = (x, y)$ and $(x, y) \odot (x, -y) = (1, 0)$; and $P$
is infinite.

$P$ is the set of points $(a/c, b/c)$ coming from primitive Pythagorean triples $(a, b, c)$ with
$a \neq 0$: writing a rational point of the unit circle over its reduced common denominator gives
a primitive triple. Rules (II) and (III) of (14) in the source concern fraction representatives
and hold automatically in $\mathbb{Q}$.

Source: Roberto Amato, *Groups and Monoid in the Set of Pythagorean Triples*, INTEGERS 24 (2024),
Article A5, Theorem 4 (`integers-2024-A5-thm-4`). -/
public theorem_wanted unitCircleRat_commGroup :
    let P : Set (ℚ × ℚ) := {p | p.1 ≠ 0 ∧ p.1 ^ 2 + p.2 ^ 2 = 1}
    (1, 0) ∈ P ∧
      (∀ p ∈ P, ∀ q ∈ P, unitCircleRatMul p q ∈ P) ∧
      (∀ p ∈ P, ∀ q ∈ P, ∀ r ∈ P,
        unitCircleRatMul (unitCircleRatMul p q) r = unitCircleRatMul p (unitCircleRatMul q r)) ∧
      (∀ p ∈ P, ∀ q ∈ P, unitCircleRatMul p q = unitCircleRatMul q p) ∧
      (∀ p ∈ P, unitCircleRatMul p (1, 0) = p) ∧
      (∀ p ∈ P, unitCircleRatMul p (p.1, -p.2) = (1, 0)) ∧
      P.Infinite

end

end MetaMathlibExt
