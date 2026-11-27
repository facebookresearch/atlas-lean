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
public import MathlibExt.NumberTheory.UnitCircleRatCommGroup

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

end

end MetaMathlibExt
