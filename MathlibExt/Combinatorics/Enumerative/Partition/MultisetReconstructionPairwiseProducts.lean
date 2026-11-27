/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Multiset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Multiset
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Ring

/-!
# Reconstructing partitions from pairwise products

Li's theorem states that the pairwise products determine a partition of a fixed positive integer.
The common total and products give equal power sums at exponents `2 ^ k`. For large enough
exponents, these sums distinguish the multiplicity of the largest part.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.Partition
namespace MultisetReconstructionPairwiseProductsWanted

/-- **Pairwise products of a multiset.** If a multiset $s$ of natural numbers consists of
$x_1, \dots, x_k$, listed with multiplicity, then the pairwise products of $s$ form the multiset
of the products $x_i x_j$ over all pairs of indices $1 \le i < j \le k$; equal elements at
different positions give separate products, and the result is empty when $k < 2$.

Applied to the parts of a partition $\lambda$, this gives the parts of the partition
$\mathrm{pre}_2(\lambda)$ of Li's note on multiset reconstruction. -/
def pairwiseProducts (s : Multiset ℕ) : Multiset ℕ :=
  (s.powersetCard 2).map Multiset.prod

open Multiset

private def powerSum (s : Multiset ℕ) (e : ℕ) : ℕ :=
  (s.map (· ^ e)).sum

private theorem pairwiseProducts_cons (a : ℕ) (s : Multiset ℕ) :
    pairwiseProducts (a ::ₘ s) = pairwiseProducts s + s.map (a * ·) := by
  simp [pairwiseProducts, powersetCard_cons, powersetCard_one, map_map]

private theorem powerSum_sq (s : Multiset ℕ) (e : ℕ) :
    powerSum s e ^ 2 = powerSum s (e * 2) + 2 * powerSum (pairwiseProducts s) e := by
  induction s using Multiset.induction_on with
  | empty => simp [powerSum, pairwiseProducts, powersetCard_zero_right]
  | cons a s ih =>
    simp only [pairwiseProducts_cons, powerSum, map_cons, sum_cons, Multiset.map_add, sum_add,
      map_map, Function.comp_def, mul_pow, sum_map_mul_left, pow_mul] at *
    rw [add_sq, ih]
    ring

-- Bernoulli's inequality makes one copy of the next part outweigh all smaller parts.
private theorem exists_dominating_power (b c : ℕ) :
    ∃ k : ℕ, c * b ^ (2 ^ k) < (b + 1) ^ (2 ^ k) := by
  by_cases hb : b = 0
  · exact ⟨0, by simp [hb]⟩
  refine ⟨c * b, ?_⟩
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (pow_ne_zero (c * b) (by decide : 2 ≠ 0))
  rw [hd]
  have hlarge : c * b < d + 1 := Nat.lt_two_pow_self.trans_eq hd
  calc
    c * b ^ (d + 1) = (c * b) * b ^ d := by ring
    _ < (d + 1) * b ^ d := Nat.mul_lt_mul_of_pos_right hlarge (pow_pos (Nat.pos_of_ne_zero hb) _)
    _ ≤ (b + 1) ^ (d + 1) := by
      have h := pow_add_mul_le_add_pow (a := b) (b := 1) (Nat.zero_le _) (Nat.zero_le _) (d + 1)
      simpa using (Nat.le_add_left _ _).trans h

private theorem powerSum_le (s : Multiset ℕ) (b e : ℕ) (hs : ∀ x ∈ s, x ≤ b) :
    powerSum s e ≤ s.card * b ^ e := by
  unfold powerSum
  convert! sum_le_card_nsmul (s.map (· ^ e)) (b ^ e) _ using 1
  · simp
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hy
    exact Nat.pow_le_pow_left (hs x hx) e

private theorem eq_of_dyadic_powerSums (b : ℕ) (s t : Multiset ℕ)
    (hs : ∀ x ∈ s, 0 < x ∧ x ≤ b) (ht : ∀ x ∈ t, 0 < x ∧ x ≤ b)
    (h : ∀ k : ℕ, powerSum s (2 ^ k) = powerSum t (2 ^ k)) : s = t := by
  induction b generalizing s t with
  | zero =>
    have empty (u : Multiset ℕ) (hu : ∀ x ∈ u, 0 < x ∧ x ≤ 0) : u = 0 :=
      eq_zero_of_forall_notMem fun x hx => (hu x hx).2.not_gt (hu x hx).1
    rw [empty s hs, empty t ht]
  | succ b ih =>
    let rest (u : Multiset ℕ) := u.filter (· ≠ b + 1)
    have split (u : Multiset ℕ) : rest u + replicate (u.count (b + 1)) (b + 1) = u := by
      rw [add_comm, ← filter_eq']
      exact filter_add_not (· = b + 1) u
    have bounds (u : Multiset ℕ) (hu : ∀ x ∈ u, 0 < x ∧ x ≤ b + 1) :
        ∀ x ∈ rest u, 0 < x ∧ x ≤ b := by
      intro x hx
      obtain ⟨hxu, hne⟩ := mem_filter.mp hx
      have := hu x hxu
      exact ⟨this.1, by omega⟩
    have expansion (u : Multiset ℕ) (e : ℕ) :
        powerSum u e = powerSum (rest u) e + u.count (b + 1) * (b + 1) ^ e := by
      conv_lhs => rw [← split u]
      simp [powerSum]
    obtain ⟨k, hk⟩ := exists_dominating_power b ((rest s).card + (rest t).card)
    let e := 2 ^ k
    have recover (u : Multiset ℕ) (hu : ∀ x ∈ rest u, 0 < x ∧ x ≤ b)
        (hc : (rest u).card ≤ (rest s).card + (rest t).card) :
        powerSum u e / (b + 1) ^ e = u.count (b + 1) := by
      have hsmall : powerSum (rest u) e < (b + 1) ^ e :=
        (powerSum_le _ _ _ fun x hx => (hu x hx).2).trans_lt
          ((Nat.mul_le_mul_right _ hc).trans_lt hk)
      rw [expansion, Nat.add_mul_div_right _ _ (pow_pos (Nat.succ_pos b) e),
        Nat.div_eq_of_lt hsmall, zero_add]
    have counts : s.count (b + 1) = t.count (b + 1) := by
      rw [← recover s (bounds s hs) (by omega), ← recover t (bounds t ht) (by omega), h k]
    have tails : rest s = rest t := by
      apply ih _ _ (bounds s hs) (bounds t ht)
      intro j
      have hj := h j
      rwa [expansion s, expansion t, counts, Nat.add_right_cancel_iff] at hj
    rw [← split s, ← split t, tails, counts]

set_option linter.unusedVariables false in
/-- **Li's theorem: partitions are determined by their pairwise products.** Let $n$ be a positive
integer and let $\lambda$ and $\mu$ be partitions of $n$. The pairwise products of the parts of
$\lambda$ and the pairwise products of the parts of $\mu$ form the same multiset if and only if
$\lambda = \mu$.

Source: Stella Jiahui Li, "A Note on Multiset Reconstruction from
Pairwise Products and Total Sum", Theorem 1. -/
theorem partition_pairwiseProducts_eq_iff
    {n : ℕ} (hn : 0 < n) (lam mu : Nat.Partition n) :
    pairwiseProducts lam.parts = pairwiseProducts mu.parts ↔ lam = mu := by
  refine ⟨fun hpre => Nat.Partition.ext ?_, fun h => h ▸ rfl⟩
  apply eq_of_dyadic_powerSums n _ _
    (fun _ hx => ⟨lam.parts_pos hx, Nat.Partition.le_of_mem_parts hx⟩)
    (fun _ hx => ⟨mu.parts_pos hx, Nat.Partition.le_of_mem_parts hx⟩)
  intro k
  induction k with
  | zero => simp [powerSum, lam.parts_sum, mu.parts_sum]
  | succ k ih =>
    have hl := powerSum_sq lam.parts (2 ^ k)
    have hm := powerSum_sq mu.parts (2 ^ k)
    rw [hpre, ih] at hl
    rw [pow_succ]
    omega

set_option linter.unusedVariables false in
/-- **Li's lemma: reconstruction from the largest part and pairwise products.** Let $n$ be a
positive integer and let $\lambda$ and $\mu$ be partitions of $n$ with a common largest part,
that is, some $a$ is a part of both $\lambda$ and $\mu$ and no part of either exceeds $a$. If the
pairwise products of the parts of $\lambda$ and the pairwise products of the parts of $\mu$ form
the same multiset, then $\lambda = \mu$.

Source: Stella Jiahui Li, "A Note on Multiset Reconstruction from
Pairwise Products and Total Sum", Lemma 1. -/
theorem partition_eq_of_pairwiseProducts_eq_of_max_eq
    {n : ℕ} (hn : 0 < n) (lam mu : Nat.Partition n)
    (hmax : ∃ a : ℕ, a ∈ lam.parts ∧ a ∈ mu.parts ∧
      (∀ x ∈ lam.parts, x ≤ a) ∧ (∀ x ∈ mu.parts, x ≤ a))
    (hpre : pairwiseProducts lam.parts = pairwiseProducts mu.parts) :
    lam = mu :=
  (partition_pairwiseProducts_eq_iff hn lam mu).mp hpre

end MultisetReconstructionPairwiseProductsWanted
end MathlibExt.Combinatorics.Enumerative.Partition
