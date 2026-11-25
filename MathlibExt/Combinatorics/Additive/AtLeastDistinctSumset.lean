/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.Finset.Sym
public import MathlibExt.Combinatorics.Additive.RestrictedSignedSumset

/-!
# Sums with at least `r` distinct terms

For a finite subset `A` of an additive commutative monoid, `atLeastDistinctSumset h r A` is the
set `h^{(≥ r)} A` of sums of `h` elements of `A`, repetitions allowed, in which at least `r`
distinct elements occur. The main result,
`MetaMathlibExt.atLeastDistinctSumset_eq_nsmul_add_restrictedSumset`, is the decomposition
`h^{(≥ r)} A = (h - r) A + r^∧ A` into an iterated sumset and a restricted sumset (Bhanja,
*Sumsets with a Minimum Number of Distinct Terms*, Lemma 2).

## Main statements

* `MetaMathlibExt.atLeastDistinctSumset_eq_nsmul_add_restrictedSumset`
-/

namespace MetaMathlibExt

open scoped Pointwise

@[expose] public section

/-- **Sums with at least $r$ distinct terms.** Let $G$ be an additive commutative monoid, $A$ a
finite subset of $G$ and $h, r$ natural numbers. The sumset $h^{(\ge r)}A$ is the set of all sums
of $h$ elements of $A$, repetitions allowed, in which at least $r$ distinct elements occur, that
is, the elements $\sum_{a \in B} x_a a$ with $B \subseteq A$, $|B| \ge r$, positive integers
$x_a$ and $\sum_{a \in B} x_a = h$.

For $r = 1$ and $h \ge 1$ it is the $h$-fold sumset $hA$; for $r = h$ it is the restricted
sumset $h^{\wedge}A$ of sums of $h$ distinct elements of $A$.

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Section 1, Definition 1. -/
def atLeastDistinctSumset {G : Type*} [AddCommMonoid G] [DecidableEq G] (h r : ℕ)
    (A : Finset G) : Finset G :=
  ((A.sym h).filter fun s : Sym G h => r ≤ (s : Multiset G).toFinset.card).image
    fun s : Sym G h => (s : Multiset G).sum

end

/-- An element lies in the iterated sumset `n • A` exactly when it is the sum of a multiset of
`n` elements of `A`. -/
private theorem mem_nsmul_iff_exists_multiset {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (A : Finset G) (n : ℕ) (x : G) :
    x ∈ n • A ↔ ∃ m : Multiset G, Multiset.card m = n ∧ (∀ a ∈ m, a ∈ A) ∧ m.sum = x := by
  induction n generalizing x with
  | zero =>
    simp only [zero_nsmul, Finset.mem_zero, Multiset.card_eq_zero]
    constructor
    · rintro rfl
      exact ⟨0, rfl, by simp, Multiset.sum_zero⟩
    · rintro ⟨m, rfl, -, rfl⟩
      exact Multiset.sum_zero
  | succ n ih =>
    rw [succ_nsmul, Finset.mem_add]
    constructor
    · rintro ⟨y, hy, a, ha, rfl⟩
      obtain ⟨m, hm, hmA, rfl⟩ := (ih y).1 hy
      refine ⟨a ::ₘ m, by simp [hm], ?_, by simp [add_comm]⟩
      intro b hb
      rcases Multiset.mem_cons.1 hb with rfl | hb
      · exact ha
      · exact hmA b hb
    · rintro ⟨m, hm, hmA, rfl⟩
      obtain ⟨a, t, rfl, ht⟩ := Multiset.card_eq_succ_iff.1 hm
      refine ⟨t.sum, (ih _).2 ⟨t, ht, fun b hb => hmA b (Multiset.mem_cons_of_mem hb), rfl⟩,
        a, hmA a (Multiset.mem_cons_self a t), ?_⟩
      simp [add_comm]

set_option linter.unusedVariables false in
/-- **Decomposition of sums with at least $r$ distinct terms.** Let $G$ be an abelian group, $A$
a nonempty finite subset of $G$, and $r, h$ natural numbers with $1 \le r \le |A|$ and $r \le h$.
Write $h^{(\ge r)}A$ for the set of sums of $h$ elements of $A$, repetitions allowed, in which at
least $r$ distinct elements occur, $(h - r)A$ for the set of sums of $h - r$ elements of $A$,
repetitions allowed (so $0A = \{0\}$), and $r^{\wedge}A$ for the restricted sumset of sums of
$r$ distinct elements of $A$. Then $h^{(\ge r)}A = (h - r)A + r^{\wedge}A$.

Source: Jagannath Bhanja, *Sumsets with a Minimum Number of Distinct Terms*, INTEGERS 25 (2025),
Article A12, Lemma 2, equation (5) (`integers-2025-A12-lem-2`). -/
public theorem atLeastDistinctSumset_eq_nsmul_add_restrictedSumset {G : Type*}
    [AddCommGroup G] [DecidableEq G] (A : Finset G) (hA : A.Nonempty) (r h : ℕ) (hr : 1 ≤ r)
    (hrk : r ≤ A.card) (hrh : r ≤ h) :
    atLeastDistinctSumset h r A = (h - r) • A + restrictedSumset r A := by
  ext x
  simp only [atLeastDistinctSumset, restrictedSumset, Finset.mem_image, Finset.mem_filter,
    Finset.mem_sym_iff, Finset.mem_add, Finset.mem_powersetCard, mem_nsmul_iff_exists_multiset]
  constructor
  · rintro ⟨s, ⟨hsA, hr⟩, rfl⟩
    -- Pick `r` distinct terms of the sum; the remaining terms form a sum of `h - r` terms.
    obtain ⟨B, hBs, hB⟩ := Finset.exists_subset_card_eq hr
    have hle : B.val ≤ (s : Multiset G) :=
      (Multiset.le_iff_subset B.nodup).2 fun a ha => Multiset.mem_toFinset.1 (hBs ha)
    refine ⟨((s : Multiset G) - B.val).sum, ⟨(s : Multiset G) - B.val, ?_, ?_, rfl⟩,
      ∑ a ∈ B, a, ⟨B, ⟨?_, hB⟩, rfl⟩, ?_⟩
    · rw [Multiset.card_sub hle, Sym.card_coe, Finset.card_val, hB]
    · intro a ha
      exact hsA a (Multiset.mem_of_le (Multiset.sub_le_self _ _) ha)
    · intro a ha
      exact hsA a (Multiset.mem_toFinset.1 (hBs ha))
    · rw [Finset.sum_eq_multiset_sum, Multiset.map_id', ← Multiset.sum_add,
        tsub_add_cancel_of_le hle]
  · rintro ⟨y, ⟨m, hm, hmA, rfl⟩, z, ⟨B, ⟨hBA, hB⟩, rfl⟩, rfl⟩
    -- Append the `r` distinct elements of `B` to the `h - r` terms of `m`.
    refine ⟨⟨m + B.val, by rw [Multiset.card_add, hm, Finset.card_val, hB]; omega⟩, ⟨?_, ?_⟩, ?_⟩
    · intro a ha
      rcases Multiset.mem_add.1 (Sym.mem_mk _ _ _ |>.1 ha) with ha | ha
      · exact hmA a ha
      · exact hBA ha
    · calc r = B.card := hB.symm
        _ ≤ (m + B.val).toFinset.card := by
          apply Finset.card_le_card
          rw [Multiset.toFinset_add, Finset.val_toFinset]
          exact Finset.subset_union_right
    · rw [Sym.coe_mk, Multiset.sum_add, Finset.sum_eq_multiset_sum, Multiset.map_id']

end MetaMathlibExt
