/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.WeightedDavenportZModProdSelf

namespace MetaMathlibExt

/-- For $n = m$ the weight bound is $\lceil m/(m-1) \rceil - 1 = 1$, so the only admissible weight
set is $\{1\}$. The theorem then gives the ordinary Davenport constant
$D(\mathbb{Z}/m\mathbb{Z} \times \mathbb{Z}/m\mathbb{Z}) = 2m - 1$ for every $m \ge 2$. -/
example (m : ℕ) (hm : 2 ≤ m) :
    weightedDavenport {1} (ZMod m × ZMod m) = ((2 * m - 1 : ℕ) : ℕ∞) := by
  have hceil : m ⌈/⌉ (m - 1) = 2 := by
    apply le_antisymm
    · rw [ceilDiv_le_iff_le_mul (by omega)]
      omega
    · exact Nat.succ_le_of_lt ((gc_mul_ceilDiv (by omega)).lt_iff_lt.mpr (by omega))
  refine weightedDavenport_zmod_prod_self_of_dvd m m hm hm dvd_rfl {1} ?_ ?_
  · simp [Nat.div_self (by omega : 0 < m)]
  · simp [hceil]

/-- All weights up to the bound $\lceil 12/3 \rceil - 1 = 3$ on
$\mathbb{Z}/12\mathbb{Z} \times \mathbb{Z}/12\mathbb{Z}$, with $m = 4$, give the threshold $7$. -/
example : weightedDavenport (Finset.Icc 1 3) (ZMod 12 × ZMod 12) = 7 :=
  (weightedDavenport_zmod_prod_self_of_dvd 4 12 (by decide) (by decide) (by decide)
    (Finset.Icc 1 3) (by decide) (by decide)).trans (by decide)

/-- For the composite divisor $m = 6$ of $12$ the single weight $12/6 = 2$ gives the
threshold $11$. -/
example : weightedDavenport {2} (ZMod 12 × ZMod 12) = 11 :=
  (weightedDavenport_zmod_prod_self_of_dvd 6 12 (by decide) (by decide) (by decide)
    {2} (by decide) (by decide)).trans (by decide)

end MetaMathlibExt
