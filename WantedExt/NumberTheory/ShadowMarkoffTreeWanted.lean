/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Convex.Hull
public import MathlibExt.NumberTheory.ShadowMarkoffTree

/-!
# Positivity on a shadow Markoff tree

Nathan Bonin's *Conditions of Positivity on a Shadow Markoff Tree* characterizes the
initial triples that give a nonnegative tree.
-/

namespace MetaMathlibExt

/-- **Nonnegativity on a shadow Markoff tree is governed by finitely many points.** There is a
finite set $V \subseteq \mathbb{Q}^3$ such that for every
$v = (\alpha, \beta, \gamma) \in \mathbb{Z}^3$ the following are equivalent: every state $(x, y)$
of the shadow Markoff tree of $v$, the tree of the initial triple
$(1 + \alpha\varepsilon, 1 + \beta\varepsilon, 1 + \gamma\varepsilon)$ with $\varepsilon^2 = 0$,
has all coordinates of its classical part $x$ and of its shadow part $y$ nonnegative; and $v = tw$
for some rational $t \ge 0$ and some point $w$ of the convex hull of $V$ in $\mathbb{Q}^3$.

In projective terms, the source describes the points $(\alpha : \beta : \gamma)$ with a
nonnegative tree as a convex polygon in an affine chart of the rational projective plane; the
statement above asserts only that some finite set $V$ exists.

Source: Nathan Bonin, *Conditions of Positivity on a Shadow Markoff Tree*, Journal of Integer
Sequences 27 (2024), Article 24.8.3, Theorem 2 (`jis-2024-24.8.3-thm-2`). -/
public theorem_wanted exists_polygon_shadowMarkoffTree_nonneg_iff :
    ∃ V : Finset (Fin 3 → ℚ), ∀ v : Fin 3 → ℤ,
      (∀ s ∈ shadowMarkoffTree v, 0 ≤ s.1 ∧ 0 ≤ s.2) ↔
        ∃ t : ℚ, 0 ≤ t ∧ ∃ p ∈ convexHull ℚ (V : Set (Fin 3 → ℚ)), (fun i => (v i : ℚ)) = t • p

end MetaMathlibExt
