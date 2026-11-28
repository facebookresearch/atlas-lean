/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.InclExclLikeSumBounds

/-!
# Extrema of the floor inclusion-exclusion-like sum

This module proves `MetaMathlibExt.inclExclLikeSum_floor_extrema`: for `n ≥ 2` the
inclusion-exclusion-like sum with the floor function satisfies
`-2 ^ (n - 2) ≤ g₁ x ≤ 2 ^ (n - 2) - 1` for every `x`, with the minimum attained at
`(1 / 2, …, 1 / 2)` and the maximum at `(1 / 2 - 1 / n ^ 2, …, 1 / 2 - 1 / n ^ 2)`.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Lemma 5.
-/

namespace MetaMathlibExt

/-- **Extrema of the floor inclusion-exclusion-like sum.** Let $n \ge 2$ and let $g_1$ be the
inclusion-exclusion-like sum $g^{(F)}$ in $n$ real variables with $F$ the floor function. Then
$-2^{n-2} \le g_1(x) \le 2^{n-2} - 1$ for every $x \in \mathbb{R}^n$; the minimum $-2^{n-2}$ is
attained at the point with all coordinates $1/2$, and the maximum $2^{n-2} - 1$ at the point with
all coordinates $1/2 - 1/n^2$.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Lemma 5. -/
public theorem inclExclLikeSum_floor_extrema {n : ℕ} (hn : 2 ≤ n) :
    (∀ x : Fin n → ℝ, -2 ^ (n - 2) ≤ inclExclLikeSum Int.floor x ∧
      inclExclLikeSum Int.floor x ≤ 2 ^ (n - 2) - 1) ∧
      inclExclLikeSum Int.floor (fun _ : Fin n => (1 / 2 : ℝ)) = -2 ^ (n - 2) ∧
      inclExclLikeSum Int.floor (fun _ : Fin n => 1 / 2 - 1 / (n : ℝ) ^ 2) = 2 ^ (n - 2) - 1 := by
  obtain ⟨hall, hhalf, hlow, -⟩ := inclExclLikeSum_bounds_summary hn
  exact ⟨fun x => (hall x).1, hhalf.1, hlow.1⟩

end MetaMathlibExt
