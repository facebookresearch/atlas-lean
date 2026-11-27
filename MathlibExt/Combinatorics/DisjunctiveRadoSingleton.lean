/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Order.Bounds.Defs
public import MathlibExt.Combinatorics.DisjunctiveRado
import Mathlib.Data.Fintype.Card

/-!
# The singleton Rado number at the all-ones solution

For the target constant $a + m - 3$, assigning $1$ to every variable gives a monochromatic
solution for every coloring of $\{1\}$. No smaller positive bound is possible.

## References

* Srashti Dwivedi and Amitabha Tripathi, *On the Two-Color Disjunctive Rado Number for the
  Equations $\sum_{i=1}^{m-2} x_i + a x_{m-1} - x_m = c_j$, $j = 1, 2$*, INTEGERS 25 (2025),
  Article A108, pp. 1–11, Proposition 2.
* Srashti Dwivedi and Amitabha Tripathi, *On the Two-Color Rado Number for
  $\sum_{i=1}^{m-2} x_i + a x_{m-1} - x_m = c$*, INTEGERS 22 (2022), Article A90,
  pp. 1–16, Table 1 and the constant-solution argument in the proof of Theorem 7.
  This is reference [5] in the 2025 paper, which cites it as “Proposition 1”.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.DisjunctiveRadoWanted

-- Retain the source's hypothesis `m ≤ a`, although the all-ones solution does not need it.
set_option linter.unusedVariables false in
/-- **Proposition 2** (quoted): for `4 ≤ m ≤ a`, the Rado number of
`∑_{i=1}^{m-2} x_i + a x_{m-1} - x_m = a + m - 3` is `1`.

Source: Srashti Dwivedi and Amitabha Tripathi, "On the Two-Color Disjunctive
Rado Number for the Equations `∑_{i=1}^{m-2} x_i + a x_{m-1} - x_m = c_j`,
`j = 1, 2`", INTEGERS 25 (2025), Article A108, Proposition 2 (from
[5, Proposition 1]). -/
theorem isLeast_disjRadoSet_eq_one (a m : ℕ) (hm : 4 ≤ m) (hma : m ≤ a) :
    IsLeast (disjRadoSet m a {(a : ℤ) + m - 3}) 1 := by
  unfold disjRadoSet
  refine ⟨⟨le_rfl, ?_⟩, fun _ hR => hR.1⟩
  unfold radoGood
  intro col
  have hone : (1 : ℕ) ∈ Finset.Icc 1 1 := Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩
  refine ⟨_, Finset.mem_singleton_self _, fun _ => 1, 1, 1,
    fun _ => hone, hone, hone, fun _ => rfl, rfl, ?_⟩
  simp only [Nat.cast_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  omega

end MathlibExt.Combinatorics.DisjunctiveRadoWanted
