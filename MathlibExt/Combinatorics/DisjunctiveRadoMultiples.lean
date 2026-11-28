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
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Disjunctive Rado numbers for multiples of $a + m - 3$

For $4 \le m \le a$ and $1 < k_j \le a + m - 2$ for $j = 1, 2$, the two-color disjunctive
Rado number of $\sum_{i=1}^{m-2} x_i + a x_{m-1} - x_m = k_j(a + m - 3)$, $j = 1, 2$,
is $\min\{k_1, k_2\}$.

## References

* Srashti Dwivedi and Amitabha Tripathi, *On the Two-Color Disjunctive Rado Number for the
  Equations $\sum_{i=1}^{m-2} x_i + a x_{m-1} - x_m = c_j$, $j = 1, 2$*, INTEGERS 25 (2025),
  Article A108, pp. 1–11, Theorem 5 (p. 4).
* The constant-tuple construction follows `isLeast_disjRadoSet_eq_one` in
  `MathlibExt.Combinatorics.DisjunctiveRadoSingleton`, with the tuple set to the smaller multiplier.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.DisjunctiveRadoWanted

/-- **Theorem 5**: for `4 ≤ m ≤ a` and `c_j = k_j (a + m - 3)` with
`1 < k_j ≤ a + m - 2`, `R(c₁, c₂) = min {k₁, k₂}`.

Source: Srashti Dwivedi and Amitabha Tripathi, "On the Two-Color Disjunctive
Rado Number for the Equations `∑_{i=1}^{m-2} x_i + a x_{m-1} - x_m = c_j`,
`j = 1, 2`", INTEGERS 25 (2025), Article A108, Theorem 5. -/
theorem isLeast_disjRadoSet_multiples (a m k₁ k₂ : ℕ) (hm : 4 ≤ m) (hma : m ≤ a)
    (hk₁ : 1 < k₁) (hk₁' : k₁ ≤ a + m - 2) (hk₂ : 1 < k₂) (hk₂' : k₂ ≤ a + m - 2) :
    IsLeast (disjRadoSet m a {(k₁ : ℤ) * (a + m - 3), (k₂ : ℤ) * (a + m - 3)}) (min k₁ k₂) := by
  let k := min k₁ k₂
  let d : ℤ := (a : ℤ) + m - 3
  have hm₂ : ((m - 2 : ℕ) : ℤ) = (m : ℤ) - 2 := Int.ofNat_sub (by omega)
  have hk : 1 ≤ k := le_min hk₁.le hk₂.le
  have hkBound : (k : ℤ) ≤ d + 1 := by
    have h : k ≤ a + m - 2 := by simpa [k] using min_le_min hk₁' hk₂'
    dsimp [d]
    omega
  have ha : 4 ≤ (a : ℤ) := by omega
  have hd : 0 ≤ d := by dsimp [d]; omega
  change IsLeast (disjRadoSet m a {(k₁ : ℤ) * d, (k₂ : ℤ) * d}) k
  refine ⟨⟨hk, ?_⟩, ?_⟩
  · -- The constant tuple at `k` works for every coloring.
    intro col
    have hc : (k : ℤ) * d ∈ ({(k₁ : ℤ) * d, (k₂ : ℤ) * d} : Finset ℤ) := by
      rcases min_choice k₁ k₂ with h | h <;> simp [k, h]
    have hmem : k ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨hk, le_rfl⟩
    refine ⟨_, hc, fun _ => k, k, k, fun _ => hmem, hmem, hmem, fun _ => rfl, rfl, ?_⟩
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hm₂, d]
    ring
  · -- Below `k`, even without the color restrictions, neither target can be reached.
    intro R hR
    by_contra! hRk
    obtain ⟨c, hc, x, y, z, hx, hy, hz, _, _, he⟩ := hR.2 (fun _ => false)
    have hsum : ∑ i, (x i : ℤ) ≤ ((m : ℤ) - 2) * R := calc
      ∑ i, (x i : ℤ) ≤ ∑ _i : Fin (m - 2), (R : ℤ) :=
        Finset.sum_le_sum fun i _ => Int.ofNat_le.mpr (Finset.mem_Icc.mp (hx i)).2
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hm₂]
    have hy' : (a : ℤ) * y ≤ (a : ℤ) * R :=
      Int.mul_le_mul_of_nonneg_left (Int.ofNat_le.mpr (Finset.mem_Icc.mp hy).2) (by omega)
    have hz' : (1 : ℤ) ≤ z := Int.ofNat_le.mpr (Finset.mem_Icc.mp hz).1
    have hleft : c ≤ (d + 1) * (R : ℤ) - 1 := calc
      c = (∑ i, (x i : ℤ)) + (a : ℤ) * y - z := he.symm
      _ ≤ ((m : ℤ) - 2) * R + (a : ℤ) * R - 1 := sub_le_sub (add_le_add hsum hy') hz'
      _ = _ := by dsimp [d]; ring
    have hsmall : (d + 1) * (R : ℤ) - 1 < (k : ℤ) * d := calc
      (d + 1) * (R : ℤ) - 1 ≤ (d + 1) * ((k : ℤ) - 1) - 1 :=
        sub_le_sub_right (Int.mul_le_mul_of_nonneg_left (by omega) (by omega)) 1
      _ = (k : ℤ) * d + ((k : ℤ) - (d + 1)) - 1 := by ring
      _ < _ := by omega
    have htarget : (k : ℤ) * d ≤ c := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact Int.mul_le_mul_of_nonneg_right (Int.ofNat_le.mpr (min_le_left k₁ k₂)) hd
      · exact Int.mul_le_mul_of_nonneg_right (Int.ofNat_le.mpr (min_le_right k₁ k₂)) hd
    exact (not_lt_of_ge htarget) (lt_of_le_of_lt hleft hsmall)

end MathlibExt.Combinatorics.DisjunctiveRadoWanted
