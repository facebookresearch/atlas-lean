/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.ColoredCompositionsDyckPolygons
import MathlibExt.Combinatorics.Enumerative.ColoredCompositionPartialBell
import MathlibExt.Combinatorics.Enumerative.ColoredDyckPathPartialBell
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Polygon partitions and colored compositions

We prove `succ_mul_coloredPolygonDissectionCount_eq`: for a coloring sequence `γ` and
`1 ≤ k ≤ n`, the number $p_{n,k}(\gamma)$ of colored partitions of a rooted convex $(n+2)$-gon
into $k$ polygons and the number $c_{n,k}(\gamma)$ of colored compositions of $n$ with $k$ parts
satisfy $(n+1)\, p_{n,k}(\gamma) = \binom{n+k}{k}\, c_{n,k}(\gamma)$. This is Theorem 4.1 of
Gil, Hoover, and Shearer, *Bijections between colored compositions, Dyck paths, and polygon
partitions* (arXiv:2403.04575v1), published in the Journal of Integer Sequences 27 (2024),
Article 24.5.2.

## Proof

The paper remarks that the identity follows from the partial Bell formulas for the three counts,
and gives a bijective proof through rooted trees with a marked leaf. Here it is derived from the
formulas for compositions and Dyck paths. The Hoggatt–Lind formula
`coloredCompositionCount_eq_partialBell` and the Mansour–Sun formula
`coloredDyckPathCount_eq_partialBell` express $c_{n,k}(\gamma)$ and the colored Dyck path count
$d_{n,k}(\gamma)$ through the same partial Bell polynomial, so
$(n+1)\, d_{n,k}(\gamma) = \binom{n+1}{k}\, c_{n,k}(\gamma)$. Multiplying the Dyck path and polygon
partition identity $\binom{n+k}{k}\, d_{n,k}(\gamma) = \binom{n+1}{k}\, p_{n,k}(\gamma)$
(`choose_mul_coloredDyckPathCount_eq`) by $n + 1$ and cancelling the positive factor
$\binom{n+1}{k}$ gives the result.
-/

namespace MetaMathlibExt

namespace succ_mul_coloredPolygonDissectionCount_eq

/-- Colored Dyck paths and colored compositions:
$(n+1)\, d_{n,k}(\gamma) = \binom{n+1}{k}\, c_{n,k}(\gamma)$ for $n \ge 1$ and $k \le n + 1$, since
both counts are multiples of the same partial Bell polynomial. -/
private theorem succ_mul_coloredDyckPathCount_eq (γ : ℕ → ℕ) {n k : ℕ} (hn : 1 ≤ n)
    (hk : k ≤ n + 1) :
    (n + 1) * coloredDyckPathCount γ n k = (n + 1).choose k * coloredCompositionCount γ n k := by
  have hf : ((n + 1).choose k : ℚ) * k.factorial * (n + 1 - k).factorial =
      (n + 1) * n.factorial := by
    exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hk).trans (Nat.factorial_succ n)
  have h₁ : ((n + 1 - k).factorial : ℚ) ≠ 0 := by positivity
  have h₂ : (n.factorial : ℚ) ≠ 0 := by positivity
  have hq : ((n + 1 : ℕ) : ℚ) * coloredDyckPathCount γ n k =
      ((n + 1).choose k : ℚ) * coloredCompositionCount γ n k := by
    rw [coloredDyckPathCount_eq_partialBell γ hn, coloredCompositionCount_eq_partialBell γ hn]
    field_simp
    push_cast
    linear_combination (partialBellPolynomial n k fun j => (j.factorial : ℚ) * γ j) * hf.symm
  exact_mod_cast hq

end succ_mul_coloredPolygonDissectionCount_eq

open succ_mul_coloredPolygonDissectionCount_eq in
/-- **Polygon partitions and colored compositions.** For every coloring sequence
$\gamma : \mathbb{N} \to \mathbb{N}$ and all natural numbers $n$ and $k$ with $1 \le k \le n$, the
colored polygon dissection count $p_{n,k}(\gamma)$ and the colored composition count
$c_{n,k}(\gamma)$ satisfy
$$(n+1)\, p_{n,k}(\gamma) = \binom{n+k}{k}\, c_{n,k}(\gamma).$$

Source: Gil, Hoover, and Shearer, *Bijections Between Colored Compositions, Dyck
Paths, and Polygon Partitions*, Journal of Integer Sequences 27 (2024), Article
24.5.2, Theorem 8 (`jis-2024-24.5.2-thm-8`). -/
public theorem succ_mul_coloredPolygonDissectionCount_eq (γ : ℕ → ℕ) {n k : ℕ}
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    (n + 1) * coloredPolygonDissectionCount γ n k =
      (n + k).choose k * coloredCompositionCount γ n k := by
  have hk' : k ≤ n + 1 := by omega
  apply Nat.eq_of_mul_eq_mul_left (Nat.choose_pos hk')
  calc (n + 1).choose k * ((n + 1) * coloredPolygonDissectionCount γ n k)
      = (n + 1) * ((n + 1).choose k * coloredPolygonDissectionCount γ n k) := by ring
    _ = (n + 1) * ((n + k).choose k * coloredDyckPathCount γ n k) := by
      rw [choose_mul_coloredDyckPathCount_eq γ hk hkn]
    _ = (n + k).choose k * ((n + 1) * coloredDyckPathCount γ n k) := by ring
    _ = (n + k).choose k * ((n + 1).choose k * coloredCompositionCount γ n k) := by
      rw [succ_mul_coloredDyckPathCount_eq γ (hk.trans hkn) hk']
    _ = (n + 1).choose k * ((n + k).choose k * coloredCompositionCount γ n k) := by ring

end MetaMathlibExt
