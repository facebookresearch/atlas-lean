/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.FixedPerimeterDistinctArmLeg
public import MathlibExt.Combinatorics.Enumerative.Partition.FixedPerimeterResidueArmLeg
import Mathlib.Data.Nat.Choose.Basic

/-!
# Refined equality for fixed perimeter partitions

The refined identity in Chen–Hernandez–Shields–Swisher, Theorem 1, follows from
binomial symmetry when the counts are positive, and from vanishing otherwise.
-/

namespace MetaMathlibExt

/-- **Refined equality of distinct-part and residue counts.** Let $d$, $a$, $m$ and $k$ be natural
numbers with $d \ge 1$, $1 \le a \le d + 1$, $m \ge 1$ and $k \ge 1$. Write $h_d^{(a)}(m, k)$ for
the number of partitions into $d$-distinct parts, all at least $a$, with largest part $m$ and $k$
parts, and $f_d^{(a)}(m, k)$ for the number of partitions into parts congruent to $a$ modulo
$d + 1$ with largest part $m$ and $k$ parts. Then
$h_d^{(a)}(m, k) = f_d^{(a)}(a + (d + 1)(k - 1), j)$, where $j = \max(m + 1 - a - d(k - 1), 0)$.

In the source the second argument is $m + 1 - a - d(k - 1)$; it is replaced by $0$ when it is not
positive, and then both sides vanish.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Theorem 1. -/
public theorem perimeterDistinctArmLegCount_eq_perimeterResidueArmLegCount
    {d a m k : ℕ} (hd : 0 < d) (ha : 1 ≤ a) (had : a ≤ d + 1) (hm : 0 < m) (hk : 0 < k) :
    perimeterDistinctArmLegCount d a m k =
      perimeterResidueArmLegCount d a (a + (d + 1) * (k - 1)) (m + 1 - a - d * (k - 1)) := by
  let m' := a + (d + 1) * (k - 1)
  let j := m + 1 - a - d * (k - 1)
  change perimeterDistinctArmLegCount d a m k = perimeterResidueArmLegCount d a m' j
  have ham' : a ≤ m' := Nat.le_add_right ..
  have hm' : 0 < m' := lt_of_lt_of_le ha ham'
  have hdistinct := perimeterDistinctArmLegCount_ne_zero_iff_and_eq_choose hd ha hm hk had
  by_cases h : a + d * (k - 1) ≤ m
  · have hj : 0 < j := by dsimp [j]; omega
    have hmod : m' ≡ a [MOD d + 1] := by simp [m']
    have hdiv : (m' - a) / (d + 1) = k - 1 := by
      simp [m', Nat.mul_div_cancel_left _ (Nat.succ_pos d)]
    have hmul : (d - 1) * (k - 1) + (k - 1) = d * (k - 1) := by
      calc
        _ = (d - 1 + 1) * (k - 1) := by rw [Nat.add_mul, Nat.one_mul]
        _ = _ := by rw [Nat.sub_add_cancel hd]
    have htop : m - a - (d - 1) * (k - 1) = (k - 1) + (j - 1) := by
      dsimp [j]
      omega
    have hresidue := perimeterResidueArmLegCount_ne_zero_iff_and_eq_choose hd ha hm' hj had
    rw [hdistinct.2 h, hresidue.2 ham' hmod, hdiv, Nat.add_sub_assoc hj, htop]
    exact Nat.choose_symm_add
  · have hj : j = 0 := by dsimp [j]; omega
    rw [not_ne_iff.mp (fun hn => h (hdistinct.1.mp hn)), hj]
    symm
    simp only [perimeterResidueArmLegCount, Finset.card_eq_zero]
    apply Finset.filter_eq_empty_iff.mpr
    rintro s - ⟨hsup, hcard, -⟩
    rw [Multiset.card_eq_zero.mp hcard, Multiset.sup_zero] at hsup
    exact hm'.ne' hsup.symm

end MetaMathlibExt
