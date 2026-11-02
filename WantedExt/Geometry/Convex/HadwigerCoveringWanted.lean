/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Convex.Illumination
import Batteries.Util.ProofWanted

/-!
# Known Hadwiger covering and illumination statements with unproved Lean payloads

These twelve private `ProofWanted` records supply no proof of their payloads.
They import only canonical geometry, not an open conjecture or its Results.
-/

@[expose] public section

namespace ConvexCovering

/-- **Two equivalent formulations of Hadwiger's covering conjecture.** The following statements
are equivalent: for every $n \ge 1$, every convex body $K \subseteq \mathbb{R}^n$ is covered by at
most $2^n$ homothets $v_i + r_i K$ with $v_i \in \mathbb{R}^n$ and $0 < r_i < 1$; and for every
$n \ge 1$, every convex body $K \subseteq \mathbb{R}^n$ is covered by $2^n$ translates of its
interior $\operatorname{int} K$, repetitions allowed.

Source: Bezdek and Khan, arXiv:1602.06040v2, introduction; Arman, Kaire and Prymak,
arXiv:2510.25968v3, introduction. The left side is the explicit closed formulation,
not an assumed OpenConjectures declaration. -/
theorem_wanted homothetInteriorTranslateFormulationsEquivalent :
    (∀ n : ℕ, 0 < n → ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsConvexBody K →
      ∃ q : ℕ, q ≤ 2 ^ n ∧ CoveredBySmallerPositiveHomothets K q) ↔
      ∀ n : ℕ, 0 < n → UniformInteriorTranslateBound n (2 ^ n)

/-- **Papadoperakis's bound for Hadwiger's covering problem in dimension 3.** Every convex body
$K \subseteq \mathbb{R}^3$ is covered by $16$ translates of its interior $\operatorname{int} K$,
repetitions allowed.

Source: Papadoperakis (1999), reported in Arman, Bondarenko and Prymak,
arXiv:2404.00547v1, introduction. -/
theorem_wanted papadoperakis1999UpperBound : UniformInteriorTranslateBound 3 16

/-- **Prymak's bound for Hadwiger's covering problem in dimension 3.** Every convex body
$K \subseteq \mathbb{R}^3$ is covered by $14$ translates of its interior $\operatorname{int} K$,
repetitions allowed.

Source: Prymak (2023), arXiv:2112.10698; reported in Arman, Bondarenko and Prymak,
arXiv:2404.00547v1, introduction. -/
theorem_wanted prymak2023UpperBound : UniformInteriorTranslateBound 3 14

/-- **Lassak's theorem for centrally symmetric bodies in dimension 3.** The number $8$ is the least
natural number $q$ such that every centrally symmetric convex body $K \subseteq \mathbb{R}^3$ is
covered by $q$ translates of its interior $\operatorname{int} K$, repetitions allowed. Here $K$ is
centrally symmetric when there is a point $c$ with $x \in K$ if and only if $2c - x \in K$.

Source: Lassak (1984), reported in Arman, Bondarenko and Prymak,
arXiv:2404.00547v1, introduction. -/
theorem_wanted lassak1984SymmetricExactValue :
  IsLeast {q : ℕ | UniformSymmetricInteriorTranslateBound 3 q} 8

/-- **Directional and exterior-point illumination are equivalent.** Let $n \ge 1$, let
$K \subseteq \mathbb{R}^n$ be a convex body and let $q$ be a natural number. Then some $q$ unit
vectors $v_1, \dots, v_q$ illuminate $K$ if and only if some $q$ points $p_1, \dots, p_q$ outside
$K$ illuminate $K$. Here the vectors illuminate $K$ when every boundary point $x$ of $K$ has an $i$
and a $t > 0$ with $x + t v_i$ in the interior of $K$, and the points illuminate $K$ when every
boundary point $x$ of $K$ has an $i$ and a $t > 1$ with $p_i + t (x - p_i)$ in the interior of $K$.

Source: Bezdek and Khan, arXiv:1602.06040v2, introduction. -/
theorem_wanted directionalExternalFormulationsEquivalent :
    ∀ n : ℕ, 0 < n → ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsConvexBody K →
      ∀ q : ℕ, IlluminatedByDirections K q ↔ IlluminatedByExternalPoints K q

/-- **Directional illumination is equivalent to covering by smaller homothets.** Let $n \ge 1$,
let $K \subseteq \mathbb{R}^n$ be a convex body and let $q$ be a natural number. Then some $q$
unit vectors illuminate $K$ if and only if $K$ is covered by $q$ homothets
$v_1 + r_1 K, \dots, v_q + r_q K$ with $v_i \in \mathbb{R}^n$ and $0 < r_i < 1$, repetitions
allowed.

Source: Bezdek and Khan, arXiv:1602.06040v2, introduction. -/
theorem_wanted directionalHomothetFormulationsEquivalent :
    ∀ n : ℕ, 0 < n → ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsConvexBody K →
      ∀ q : ℕ, IlluminatedByDirections K q ↔ CoveredBySmallerPositiveHomothets K q

/-- **Directional illumination is equivalent to covering by interior translates.** Let $n \ge 1$,
let $K \subseteq \mathbb{R}^n$ be a convex body and let $q$ be a natural number. Then some $q$ unit
vectors illuminate $K$ if and only if $K$ is covered by $q$ translates
$v_1 + \operatorname{int} K, \dots, v_q + \operatorname{int} K$ of its interior, repetitions
allowed.

Source: Arman, Kaire and Prymak, arXiv:2510.25968v3, introduction. -/
theorem_wanted directionalInteriorFormulationsEquivalent :
    ∀ n : ℕ, 0 < n → ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsConvexBody K →
      ∀ q : ℕ, IlluminatedByDirections K q ↔ CoveredByInteriorTranslates K q

/-- **Directional and exterior-point illumination numbers are equal.** For every $n \ge 1$ and
every convex body $K \subseteq \mathbb{R}^n$, the directional illumination number of $K$ equals
its exterior-point illumination number. These are the least $q$ such that some $q$ unit vectors,
respectively some $q$ points outside $K$, illuminate $K$, with the value $\infty$ when no finite
family does.

Source: Bezdek and Khan, arXiv:1602.06040v2, introduction; follows from its finite-count
equivalence, whose Lean proof is also requested here. -/
theorem_wanted directionalExternalIlluminationNumbersEqual (n : ℕ) (hn : 0 < n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsConvexBody K) :
    directionalIlluminationNumber K = externalPointIlluminationNumber K

/-- **Directional illumination number equals the interior-translate covering number.** For every
$n \ge 1$ and every convex body $K \subseteq \mathbb{R}^n$, the directional illumination number of
$K$ equals the least $q$ such that $K$ is covered by $q$ translates of its interior
$\operatorname{int} K$. Both sides take the value $\infty$ when no finite family exists.

Source: Arman, Kaire and Prymak, arXiv:2510.25968v3, introduction; follows from the
finite-count equivalence, whose Lean proof is also requested here. -/
theorem_wanted directionalInteriorCoveringNumbersEqual (n : ℕ) (hn : 0 < n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsConvexBody K) :
    directionalIlluminationNumber K = translateCoveringNumber K (interior K)

/-- **Every convex body has a finite illumination number.** For every $n \ge 1$ and every convex
body $K \subseteq \mathbb{R}^n$ there is a least natural number $q$ such that some $q$ unit vectors
$v_1, \dots, v_q$ illuminate $K$: every boundary point $x$ of $K$ has an $i$ and a $t > 0$ with
$x + t v_i$ in the interior of $K$.

Source: Arman, Kaire and Prymak, arXiv:2510.25968v3, introduction's illumination-number
definition; finite existence is the standard compact-convex-body qualification. -/
theorem_wanted illuminationFiniteMinimum :
    ∀ n : ℕ, 0 < n → ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsConvexBody K →
      ∃ q : ℕ, IsLeast {q : ℕ | IlluminatedByDirections K q} q

/-- **Uniform covering by interior translates and uniform directional illumination.** For
integers $n \ge 1$ and $q \ge 0$, every convex body in $\mathbb{R}^n$ (a compact convex set with
nonempty interior) can be covered by $q$ translates of its interior if and only if every convex
body $K$ in $\mathbb{R}^n$ is illuminated by $q$ directions: there are unit vectors
$v_1, \dots, v_q$ such that each boundary point $x$ of $K$ has some $i$ and some $t > 0$ with
$x + t v_i$ in the interior of $K$.

Source: Arman, Kaire and Prymak, arXiv:2510.25968v3, introduction; follows from the
finite-count equivalence, whose Lean proof is also requested here. -/
theorem_wanted uniformDirectionalIlluminationInterpretation (n : ℕ) (hn : 0 < n) (q : ℕ) :
    UniformInteriorTranslateBound n q ↔
      ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsConvexBody K → IlluminatedByDirections K q

/-- **Uniform covering of symmetric bodies and uniform illumination by external points.** For
integers $n \ge 1$ and $q \ge 0$, every centrally symmetric convex body in $\mathbb{R}^n$ (a
compact convex set with nonempty interior that is symmetric about some point) can be covered by
$q$ translates of its interior if and only if every centrally symmetric convex body $K$ in
$\mathbb{R}^n$ is illuminated by $q$ external points: there are points $p_1, \dots, p_q$ outside
$K$ such that each boundary point $x$ of $K$ has some $i$ and some $t > 1$ with
$p_i + t(x - p_i)$ in the interior of $K$.

Source: Arman, Kaire and Prymak, arXiv:2510.25968v3, introduction, and Bezdek and Khan,
arXiv:1602.06040v2, introduction; follows from the two finite-count equivalences. -/
theorem_wanted uniformSymmetricExternalIlluminationInterpretation (n : ℕ) (hn : 0 < n) (q : ℕ) :
    UniformSymmetricInteriorTranslateBound n q ↔
      ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsConvexBody K → IsCentrallySymmetric K →
        IlluminatedByExternalPoints K q

end ConvexCovering
