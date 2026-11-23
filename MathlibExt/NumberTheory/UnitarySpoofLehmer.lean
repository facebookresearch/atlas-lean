/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
public import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Tactic.LinearCombination

/-!
# Lehmer's lemma for unitary spoof factorizations

The two unitary Lehmer equations give a factorization identity for the two added bases.
-/

namespace MetaMathlibExt

/-- **Lehmer's lemma for unitary spoof factorizations.** Let $F$ be a finite multiset of integers,
write $E = \prod_{f \in F} f$ and $P = \prod_{f \in F} (f - 1)$, and let $k$, $\alpha$, $x$ and $y$
be integers with $\alpha = \pm 1$. If $k P = E + \alpha$ and $k P (x - 1)(y - 1) = E x y - 1$,
then $(\alpha x - E - \alpha)(\alpha y - E - \alpha) - (E^2 + \alpha E - \alpha) = 0$.

The second equation says that $F \cdot x \cdot y$ satisfies the unitary $k$-Lehmer equation
(Equation (3)). The paper takes $F$ with positive entries and $k \ge 2$; the identity holds for
every finite multiset of integers and every integer $k$.

Source: Elchin Hasanalizade, *Some Remarks on a Paper of Molnar and Singh*, INTEGERS 26 (2026),
Article A100, Theorem 3 (`integers-2026-A100-thm-3`). -/
public theorem unitary_spoof_lehmer_lemma (F : Multiset ℤ) (k α x y : ℤ)
    (hα : α = 1 ∨ α = -1)
    (hF : k * (F.map fun f => f - 1).prod = F.prod + α)
    (hxy : k * ((F.map fun f => f - 1).prod * (x - 1) * (y - 1)) = F.prod * x * y - 1) :
    (α * x - F.prod - α) * (α * y - F.prod - α) - (F.prod ^ 2 + α * F.prod - α) = 0 := by
  rw [← mul_assoc, ← mul_assoc, hF] at hxy
  rcases hα with rfl | rfl
  · linear_combination hxy
  · linear_combination -hxy

end MetaMathlibExt
