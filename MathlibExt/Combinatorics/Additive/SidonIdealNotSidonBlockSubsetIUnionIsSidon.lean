/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Order.SetNotation
public import MathlibExt.Combinatorics.Additive.SidonIdeal
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring

/-!
# A block not covered by few Sidon sets

For `n ≥ 1` and `C ≥ 1`, the block `Block(n, C, M, K)` with `M = C * 2 ^ n + 1` and
`K = (n - 1) * C(n, 2) + 1` is not contained in the union of any `n - 1` Sidon subsets of `ℕ`.
-/

namespace MetaMathlibExt

@[expose] public section

private theorem collision_for_fixed_l {n C M K : ℕ} (hn : 0 < n)
    {S : Fin (n - 1) → Set ℕ}
    (hSub : sidonBlock n C M K ⊆ ⋃ j, S j)
    {l : ℕ} (hl1 : 1 ≤ l) (hlK : l ≤ K) :
    ∃ j, ∃ k1 k2, k1 < k2 ∧ k2 < n ∧
      M ^ l + C * 2 ^ k1 ∈ S j ∧ M ^ l + C * 2 ^ k2 ∈ S j := by
  have hex : ∀ k : Fin n, ∃ j, M ^ l + C * 2 ^ (k.val) ∈ S j := by
    intro k
    have hmem : M ^ l + C * 2 ^ (k.val) ∈ sidonBlock n C M K :=
      ⟨k.val, k.isLt, l, hl1, hlK, rfl⟩
    have hmem2 := hSub hmem
    simp only [Set.mem_iUnion] at hmem2
    exact hmem2
  choose g hg using hex
  have hcard : Fintype.card (Fin (n - 1)) < Fintype.card (Fin n) := by
    rw [Fintype.card_fin, Fintype.card_fin]
    omega
  have hnot : ¬ Function.Injective g := Fintype.not_injective_of_card_lt g hcard
  rw [Function.not_injective_iff] at hnot
  obtain ⟨a, b, hab, hne⟩ := hnot
  have hvalne : a.val ≠ b.val := fun h => hne (Fin.val_inj.mp h)
  rcases lt_or_gt_of_ne hvalne with hlt' | hgt'
  · refine ⟨g a, a.val, b.val, hlt', b.isLt, hg a, ?_⟩
    rw [hab]
    exact hg b
  · refine ⟨g a, b.val, a.val, hgt', a.isLt, ?_, hg a⟩
    rw [hab]
    exact hg b

private theorem pair_eq_of_set_eq {p q r s : ℕ} (hpq : p < q) (hrs : r < s)
    (h : ({p, q} : Finset ℕ) = {r, s}) : p = r ∧ q = s := by
  have hp_mem : p ∈ ({r, s} : Finset ℕ) := h ▸ Finset.mem_insert_self p {q}
  have hq_mem : q ∈ ({r, s} : Finset ℕ) :=
    h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp_mem hq_mem
  rcases hp_mem with hpr | hps <;> rcases hq_mem with hqr | hqs
  · omega
  · exact ⟨hpr, hqs⟩
  · omega
  · omega

/-- **A block not covered by few Sidon sets.** Let $n \ge 1$ and $C \ge 1$ be natural
numbers, and put $M = C \cdot 2^n + 1$ and $K = (n - 1)\binom{n}{2} + 1$. Then the block
$\mathrm{Block}(n, C, M, K) = \{M^l + C \cdot 2^k : 0 \le k < n,\ 1 \le l \le K\}$ is not
contained in the union of any $n - 1$ Sidon subsets of $\mathbb{N}$.

Source: Andrzej Nowik, *On the Sidon Ideal*, INTEGERS 25 (2025), Article A91,
Lemma 3 (`integers-2025-A91-lem-3`). -/
public theorem not_sidonBlock_subset_iUnion_isSidon {n C : ℕ} (hn : 0 < n)
    (hC : 0 < C) :
    ¬ ∃ S : Fin (n - 1) → Set ℕ, (∀ j, (S j).IsSidon) ∧
      sidonBlock n C (C * 2 ^ n + 1) ((n - 1) * n.choose 2 + 1) ⊆ ⋃ j, S j := by
  rintro ⟨S, hSidon, hSub⟩
  by_cases hn1 : n = 1
  · subst hn1
    have hK : (1 - 1) * Nat.choose 1 2 + 1 = 1 := by simp
    rw [hK] at hSub
    have hmem : (C * 2 ^ 1 + 1) + C ∈ sidonBlock 1 C (C * 2 ^ 1 + 1) 1 := by
      rw [sidonBlock_one_one]
      rfl
    have hmem2 := hSub hmem
    simp only [Set.mem_iUnion] at hmem2
    obtain ⟨j, _⟩ := hmem2
    exact Fin.elim0 j
  · set M : ℕ := C * 2 ^ n + 1 with hM
    set K : ℕ := (n - 1) * n.choose 2 + 1 with hK
    have hM2 : 2 ≤ M := by
      have : 0 < C * 2 ^ n := Nat.mul_pos hC (Nat.two_pow_pos n)
      omega
    have key : ∀ i : Fin K, ∃ j, ∃ k1 k2, k1 < k2 ∧ k2 < n ∧
        M ^ (i.val + 1) + C * 2 ^ k1 ∈ S j ∧ M ^ (i.val + 1) + C * 2 ^ k2 ∈ S j := by
      intro i
      have hl1 : 1 ≤ i.val + 1 := Nat.le_add_left 1 i.val
      have hlK : i.val + 1 ≤ K := Nat.succ_le_of_lt i.isLt
      exact collision_for_fixed_l hn hSub hl1 hlK
    choose j k1 k2 hlt hlt2 hmem1 hmem2 using key
    let F : Fin K → Fin (n - 1) × Finset ℕ := fun i => (j i, {k1 i, k2 i})
    let t : Finset (Fin (n - 1) × Finset ℕ) :=
      Finset.univ ×ˢ (Finset.range n).powersetCard 2
    have hmaps : Set.MapsTo F ↑(Finset.univ : Finset (Fin K)) ↑t := by
      intro i _
      simp only [F, t, Finset.mem_coe,
        Finset.mem_product, Finset.mem_univ, true_and]
      rw [Finset.mem_powersetCard]
      constructor
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [Finset.mem_range]
        rcases hx with rfl | rfl
        · exact lt_trans (hlt i) (hlt2 i)
        · exact hlt2 i
      · exact Finset.card_pair (ne_of_lt (hlt i))
    have hcard : t.card < (Finset.univ : Finset (Fin K)).card := by
      rw [Finset.card_product, Finset.card_univ, Fintype.card_fin,
        Finset.card_powersetCard, Finset.card_range, Finset.card_univ,
        Fintype.card_fin]
      rw [hK]
      exact Nat.lt_succ_self _
    obtain ⟨i1, _, i2, _, hne, heq⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
    simp only [F] at heq
    have hj : j i1 = j i2 := congrArg Prod.fst heq
    have hset : ({k1 i1, k2 i1} : Finset ℕ) = {k1 i2, k2 i2} :=
      congrArg Prod.snd heq
    have hpair := pair_eq_of_set_eq (hlt i1) (hlt i2) hset
    have hlne : i1.val + 1 ≠ i2.val + 1 := by
      intro hcon
      apply hne
      exact Fin.val_inj.mp (Nat.succ_inj.mp hcon)
    have h21 : M ^ (i2.val + 1) + C * 2 ^ k1 i1 ∈ S (j i1) := by
      rw [hpair.1, hj]
      exact hmem1 i2
    have h22 : M ^ (i2.val + 1) + C * 2 ^ k2 i1 ∈ S (j i1) := by
      rw [hpair.2, hj]
      exact hmem2 i2
    have h11 := hmem1 i1
    have h12 := hmem2 i1
    have hsum : M ^ (i1.val + 1) + C * 2 ^ k1 i1 +
        (M ^ (i2.val + 1) + C * 2 ^ k2 i1) =
        M ^ (i1.val + 1) + C * 2 ^ k2 i1 +
        (M ^ (i2.val + 1) + C * 2 ^ k1 i1) := by ring
    have hsid := hSidon (j i1) _ h11 _ h22 _ h12 _ h21 hsum
    rcases hsid with ⟨hac, -⟩ | ⟨had, -⟩
    · have hCpow : C * 2 ^ k1 i1 = C * 2 ^ k2 i1 := by omega
      have hpow : (2 : ℕ) ^ k1 i1 = 2 ^ k2 i1 :=
        Nat.mul_left_cancel hC hCpow
      have hkk : k1 i1 = k2 i1 :=
        Nat.pow_right_injective (le_refl 2) hpow
      exact (ne_of_lt (hlt i1)) hkk
    · have hMl : M ^ (i1.val + 1) = M ^ (i2.val + 1) := by omega
      have hll : i1.val + 1 = i2.val + 1 := Nat.pow_right_injective hM2 hMl
      exact hlne hll

end

end MetaMathlibExt
