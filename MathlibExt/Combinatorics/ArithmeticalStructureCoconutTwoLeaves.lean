/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Fin
public import MathlibExt.Combinatorics.ArithmeticalStructureCoconutCount

/-!
# Arithmetical structures on coconut trees with two leaves

We specialize the coconut tree counting formula to two leaves, expressing the count as a
Catalan-number term plus a ballot-weighted sum of smooth counts.
-/

namespace MetaMathlibExt

/-- **Number of arithmetical structures on coconut trees with two leaves.** For $p \ge 2$, the
number of arithmetical structures on the coconut tree $CT(p, 2)$ is
$$2 C_p - C_{p-1} + \sum_{i=3}^{p+2} B(p - 1, p + 2 - i)\, N(i - 2),$$
where $C_n$ is the $n$-th Catalan number, $B(n, k)$ is the ballot number and $N(q)$ is the number
of smooth arithmetical structures on $CT(q, 2)$.

Source: Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical
Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Corollary 2
(`integers-2025-A82-cor-2`). -/
public theorem ncard_arithmeticalStructure_coconutTree_two {p : ℕ} (hp : 2 ≤ p) :
    Set.ncard {x : (Fin p ⊕ Fin 2 → ℕ) × (Fin p ⊕ Fin 2 → ℕ) |
      IsArithmeticalStructure (coconutTree p 2) x.1 x.2}
      = 2 * catalan p - catalan (p - 1) + ∑ i ∈ Finset.Icc 3 (p + 2),
          ballotNumber (p - 1) (p + 2 - i) *
            Set.ncard {z : (Fin (i - 2) ⊕ Fin 2 → ℕ) × (Fin (i - 2) ⊕ Fin 2 → ℕ) |
              IsSmoothCoconut (i - 2) 2 z.1 z.2} := by
  have hcat : catalan (p - 1) ≤ catalan p := by
    calc
      catalan (p - 1) ≤ catalan ((p - 1) + 1) := by
        rw [catalan_succ, Fin.sum_univ_succ]
        simp only [Fin.val_zero, Nat.sub_zero, catalan_zero, one_mul]
        exact Nat.le_add_right _ _
      _ = catalan p := by rw [show p - 1 + 1 = p by omega]
  rw [ncard_arithmeticalStructure_coconutTree (by omega) (by decide)]
  simp [Finset.sum_range_succ, coconutCountTerm, Nat.choose,
    show p + 2 - 1 = p + 1 by omega, show p + 1 - 2 = p - 1 by omega]
  omega

end MetaMathlibExt
