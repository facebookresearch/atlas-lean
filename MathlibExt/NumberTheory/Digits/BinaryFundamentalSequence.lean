/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Colex

/-!
# Binary fundamental sequences

We characterize the powers of two as the unique strictly increasing positive sequence for which
every natural number has a unique finite subset-sum representation.
-/

namespace MetaMathlibExt

/-- **Powers of two are the only binary fundamental sequence.** Let
$H \colon \mathbb{N} \to \mathbb{N}$ be a strictly increasing sequence of positive integers. Then
every natural number (including $0$) equals $\sum_{k \in s} H_k$ for exactly one finite set
$s \subseteq \mathbb{N}$ if and only if $H_k = 2^k$ for all $k$.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 1 (`integers-2025-A25-lem-1`). -/
public theorem bijective_finset_sum_iff_eq_two_pow {H : ℕ → ℕ} (hpos : ∀ k, 0 < H k)
    (hmono : StrictMono H) :
    Function.Bijective (fun s : Finset ℕ => ∑ k ∈ s, H k) ↔ ∀ k, H k = 2 ^ k := by
  constructor
  · rintro ⟨hinj, hsurj⟩ n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      apply le_antisymm
      · by_contra! hlt
        obtain ⟨s, hsum⟩ := hsurj (2 ^ n)
        have hs : ∀ k ∈ s, k < n := by
          intro k hk
          have hweight : H k ≤ 2 ^ n :=
            (Finset.single_le_sum (fun j _ => (hpos j).le) hk).trans_eq hsum
          exact hmono.lt_iff_lt.mp (hweight.trans_lt hlt)
        have hbound : (∑ k ∈ s, H k) < 2 ^ n := calc
          ∑ k ∈ s, H k = ∑ k ∈ s, 2 ^ k := Finset.sum_congr rfl (fun k hk => ih k (hs k hk))
          _ < _ := Nat.geomSum_lt (by decide) hs
        exact hbound.ne hsum
      · by_contra! hlt
        let s := (H n).bitIndices.toFinset
        have hs : ∀ k ∈ s, k < n := by
          intro k hk
          have hweight := Nat.two_pow_le_of_mem_bitIndices (List.mem_toFinset.mp hk)
          exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (hweight.trans_lt hlt)
        have heq : s = {n} := hinj (by
          calc
            ∑ k ∈ s, H k = ∑ k ∈ s, 2 ^ k := Finset.sum_congr rfl (fun k hk => ih k (hs k hk))
            _ = H n := Finset.sum_toFinset_bitIndices_two_pow (H n)
            _ = ∑ k ∈ ({n} : Finset ℕ), H k := (Finset.sum_singleton H n).symm)
        exact (lt_irrefl n) (hs n (by simp [heq]))
  · intro h
    simp_rw [h, ← Finset.equivBitIndices_symm_apply]
    exact Finset.equivBitIndices.symm.bijective

end MetaMathlibExt
