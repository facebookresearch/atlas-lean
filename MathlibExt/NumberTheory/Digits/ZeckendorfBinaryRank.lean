/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Fib.Zeckendorf
import all MathlibExt.NumberTheory.Digits.ZeckendorfFundamentalSequence

/-!
# Binary rank of Zeckendorf supports

We count binary words without adjacent ones below a given bound by the highest bit at which
they differ from that bound. At such a bit, the higher bits are fixed and the lower bits are
counted by a restricted Zeckendorf bijection.

## References

* Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS **25** (2025),
  Article A25, pp. 1–45, Lemma 2 (pp. 4–5).
* Édouard Zeckendorf, *Représentation des nombres naturels par une somme des nombres de
  Fibonacci ou de nombres de Lucas*, Bulletin de la Société Royale des Sciences de Liège
  **41** (1972), pp. 179–182. Chang credits this result for the Fibonacci representation
  theorem used to count each class.
* Sungkon Chang, *The weak converse of Zeckendorf’s theorem*, Research in Number Theory
  **7** (2021), Article 48. The 2025 paper cites its Theorem 16 and Lemmas 3 and 37 for
  the fundamental-sequence framework in Lemma 1.
-/

namespace MetaMathlibExt

open Finset
open bijective_nonadjacent_finset_sum_iff_eq_fib

private def lowerSupports (k : ℕ) : Finset (Finset ℕ) :=
  (range k).powerset.filter (fun s => ∀ i ∈ s, i + 1 ∉ s)

private theorem fibSum_lt_iff {s : Support} {k : ℕ} :
    weightSum (fun i => Nat.fib (i + 2)) s < Nat.fib (k + 2) ↔ s.1 ⊆ range k := by
  constructor
  · intro h i hi
    exact mem_range.mpr (Nat.fib_add_two_strictMono.lt_iff_lt.mp
      ((single_le_sum (fun j _ => Nat.zero_le (Nat.fib (j + 2))) hi).trans_lt h))
  · intro h
    have hhead (i : ℕ) (hi : i ∈ (indices s.1 ++ [0]).head?) : i < k + 2 := by
      rcases List.mem_append.mp (List.mem_of_mem_head? hi) with hi | hi
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
        exact Nat.add_lt_add_right (mem_range.mp (h ((mem_sort _).mp hj))) 2
      · obtain rfl := List.mem_singleton.mp hi
        omega
    change (∑ i ∈ s.1, Nat.fib (i + 2)) < Nat.fib (k + 2)
    rw [Finset.sum, ← s.1.sort_eq (· ≥ ·), Multiset.map_coe, Multiset.sum_coe]
    simpa only [indices, List.map_map, Function.comp_def] using (indices_rep s).sum_fib_lt hhead

private theorem card_lowerSupports (k : ℕ) : (lowerSupports k).card = Nat.fib (k + 2) := by
  rw [← card_range (Nat.fib (k + 2))]
  refine card_nbij (fun s => ∑ i ∈ s, Nat.fib (i + 2)) ?_ ?_ ?_
  · intro s hs
    obtain ⟨hlo, hgap⟩ := mem_filter.mp hs
    exact mem_range.mpr ((fibSum_lt_iff (s := ⟨s, hgap⟩)).mpr (mem_powerset.mp hlo))
  · intro s hs t ht hst
    exact congrArg Subtype.val (fib_bijective.injective
      (a₁ := ⟨s, (mem_filter.mp hs).2⟩) (a₂ := ⟨t, (mem_filter.mp ht).2⟩) hst)
  · intro n hn
    obtain ⟨s, hs⟩ := fib_bijective.surjective n
    refine ⟨s.1, mem_filter.mpr ⟨mem_powerset.mpr (fibSum_lt_iff.mp ?_), s.2⟩, hs⟩
    rw [hs]
    exact mem_range.mp hn

private theorem land_shiftRight_eq_zero_iff (n : ℕ) :
    n &&& (n >>> 1) = 0 ↔ ∀ i ∈ n.bitIndices.toFinset, i + 1 ∉ n.bitIndices.toFinset := by
  simp only [List.mem_toFinset, Nat.mem_bitIndices]
  constructor
  · intro h i hi hnext
    have hz : (n &&& (n >>> 1)).testBit i = false := by rw [h]; simp
    simp [Nat.testBit_shiftRight, Nat.add_comm, hi, hnext] at hz
  · intro h
    apply Nat.zero_of_testBit_eq_false
    intro i
    rw [Nat.testBit_land, Nat.testBit_shiftRight, Nat.add_comm 1 i]
    cases hi : n.testBit i with
    | false => simp
    | true => simpa using h i hi

private theorem mem_admissibleIndices (A : Finset ℕ) (k : ℕ) :
    (let J := A.filter (fun j => j + 1 ∈ A)
     k ∈ if h : J.Nonempty then A.filter (fun i => J.max' h ≤ i) else A) ↔
    k ∈ A ∧ ∀ j ∈ A, j + 1 ∈ A → j ≤ k := by
  let J := A.filter (fun j => j + 1 ∈ A)
  change (k ∈ if h : J.Nonempty then A.filter (fun i => J.max' h ≤ i) else A) ↔ _
  by_cases hJ : J.Nonempty
  · rw [dite_eq_left hJ, mem_filter]
    refine and_congr_right fun _ => ⟨?_, ?_⟩
    · exact fun h j hj hj' => (le_max' J j (mem_filter.mpr ⟨hj, hj'⟩)).trans h
    · intro h
      obtain ⟨hj, hj'⟩ := mem_filter.mp (max'_mem J hJ)
      exact h _ hj hj'
  · rw [dite_eq_right hJ]
    exact ⟨fun hk => ⟨hk, fun j hj hj' => (hJ ⟨j, mem_filter.mpr ⟨hj, hj'⟩⟩).elim⟩,
      And.left⟩

-- Reconstruct a support with zero at `k` from the free lower bits and the fixed upper bits.
private def branchSupport (A : Finset ℕ) (k : ℕ) (s : Finset ℕ) : Finset ℕ :=
  s ∪ A.filter (k < ·)

private theorem branchSupport_bits {A s : Finset ℕ} {k : ℕ} (hs : s ⊆ range k) :
    k ∉ branchSupport A k s ∧
      (branchSupport A k s).filter (k < ·) = A.filter (k < ·) ∧
      (branchSupport A k s).filter (· < k) = s := by
  have hlo (i : ℕ) (hi : i ∈ s) : i < k := mem_range.mp (hs hi)
  refine ⟨by simpa [branchSupport] using fun hi => (lt_irrefl k) (hlo _ hi), ?_, ?_⟩
  · ext i
    by_cases hi : k < i
    · have hnot : i ∉ s := fun hm => hi.asymm (hlo i hm)
      simp [branchSupport, hi, hnot]
    · simp [branchSupport, hi]
  · ext i
    by_cases hi : i < k
    · simp [branchSupport, hi, hi.asymm]
    · simp [hi, mt (hlo i) hi]

private theorem branchSupport_nonadjacent {A s : Finset ℕ} {k : ℕ}
    (hs : s ⊆ range k) (hgap : ∀ i ∈ s, i + 1 ∉ s)
    (hupper : ∀ j ∈ A, j + 1 ∈ A → j ≤ k) :
    ∀ i ∈ branchSupport A k s, i + 1 ∉ branchSupport A k s := by
  intro i hi hi'
  simp only [branchSupport, mem_union, mem_filter] at hi hi'
  rcases hi with hi | ⟨hi, hki⟩ <;> rcases hi' with hi' | ⟨hi', hki'⟩
  · exact hgap i hi hi'
  · have := mem_range.mp (hs hi)
    omega
  · have := mem_range.mp (hs hi')
    omega
  · exact (not_le_of_gt hki) (hupper i hi hi')

/-- **Duality formula for binary expansions without adjacent ones.** For $x \in \mathbb{N}$ let
$z(x)$ be the number of $n < x$ whose binary expansion has no two adjacent digits equal to $1$.
For a finite set $A \subseteq \mathbb{N}$, put $\bar A = A$ if there is no $j$ with
$j, j + 1 \in A$, and otherwise $\bar A = \{k \in A : k \ge j\}$, where $j$ is the largest index
with $j, j + 1 \in A$. Then $z\bigl(\sum_{k \in A} 2^k\bigr) = \sum_{k \in \bar A} F_{k+2}$,
where $F_0 = 0$, $F_1 = 1$ and $F_{n+2} = F_{n+1} + F_n$ are the Fibonacci numbers.

Source: Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25,
Lemma 2 (`integers-2025-A25-lem-2`). -/
public theorem card_zeckendorfBinary_lt_sum_two_pow (A : Finset ℕ) :
    let J := A.filter (fun j => j + 1 ∈ A)
    let Abar := if h : J.Nonempty then A.filter (fun k => J.max' h ≤ k) else A
    ((Finset.range (∑ k ∈ A, 2 ^ k)).filter (fun n => n &&& (n >>> 1) = 0)).card =
      ∑ k ∈ Abar, Nat.fib (k + 2) := by
  intro J Abar
  have hbar (k : ℕ) : k ∈ Abar ↔ k ∈ A ∧ ∀ j ∈ A, j + 1 ∈ A → j ≤ k :=
    mem_admissibleIndices A k
  simp_rw [← card_lowerSupports]
  rw [← card_sigma]
  symm
  refine card_nbij (fun p => ∑ i ∈ branchSupport A p.1 p.2, 2 ^ i) ?_ ?_ ?_
  · intro ⟨k, s⟩ hp
    obtain ⟨hk, hs⟩ := mem_sigma.mp hp
    obtain ⟨hs, hgap⟩ := mem_filter.mp hs
    have hlo := mem_powerset.mp hs
    obtain ⟨hkA, hupper⟩ := (hbar k).mp hk
    obtain ⟨hk0, htop, _⟩ := branchSupport_bits (A := A) hlo
    refine mem_filter.mpr ⟨mem_range.mpr ?_, (land_shiftRight_eq_zero_iff _).mpr ?_⟩
    · rw [geomSum_lt_geomSum_iff_toColex_lt_toColex (by decide : 2 ≤ (2 : ℕ)),
        Finset.Colex.lt_iff_exists_filter_lt]
      exact ⟨k, mem_sdiff.mpr ⟨hkA, hk0⟩, htop⟩
    · simpa using branchSupport_nonadjacent hlo hgap hupper
  · intro ⟨k, s⟩ hp ⟨l, t⟩ hq heq
    obtain ⟨hk, hs⟩ := mem_sigma.mp hp
    obtain ⟨hl, ht⟩ := mem_sigma.mp hq
    have hkA := ((hbar k).mp hk).1
    have hlA := ((hbar l).mp hl).1
    obtain ⟨hk0, _, hkbot⟩ := branchSupport_bits (A := A)
      (mem_powerset.mp (mem_filter.mp hs).1)
    obtain ⟨hl0, _, hlbot⟩ := branchSupport_bits (A := A)
      (mem_powerset.mp (mem_filter.mp ht).1)
    have hst := geomSum_injective (by decide : 2 ≤ (2 : ℕ)) heq
    -- Two different choices of the highest differing bit force different supports.
    have hkl : k = l := by
      apply le_antisymm
      · by_contra! hlt
        have hmem : k ∈ branchSupport A l t := mem_union.mpr (Or.inr (mem_filter.mpr ⟨hkA, hlt⟩))
        exact hk0 (hst.symm ▸ hmem)
      · by_contra! hlt
        have hmem : l ∈ branchSupport A k s := mem_union.mpr (Or.inr (mem_filter.mpr ⟨hlA, hlt⟩))
        exact hl0 (hst ▸ hmem)
    subst l
    congr 1
    exact hkbot.symm.trans ((congrArg (filter (· < k)) hst).trans hlbot)
  · intro n hn
    obtain ⟨hn, hgap⟩ := mem_filter.mp hn
    let u := n.bitIndices.toFinset
    have hsum : ∑ i ∈ u, 2 ^ i = n := sum_toFinset_bitIndices_two_pow n
    have hlt := mem_range.mp hn
    rw [← hsum, geomSum_lt_geomSum_iff_toColex_lt_toColex (by decide : 2 ≤ (2 : ℕ)),
      Finset.Colex.lt_iff_exists_filter_lt] at hlt
    obtain ⟨k, hk, htop⟩ := hlt
    obtain ⟨hkA, hk0⟩ := mem_sdiff.mp hk
    have hu : ∀ i ∈ u, i + 1 ∉ u := (land_shiftRight_eq_zero_iff n).mp hgap
    have hfixed {i : ℕ} (hi : k < i) (hiA : i ∈ A) : i ∈ u :=
      (mem_filter.mp (htop.symm ▸ mem_filter.mpr ⟨hiA, hi⟩)).1
    have hkbar : k ∈ Abar := (hbar k).mpr ⟨hkA, fun j hj hj' => by
      by_contra! hkj
      exact hu j (hfixed hkj hj) (hfixed (Nat.lt_succ_of_lt hkj) hj')⟩
    refine ⟨⟨k, u.filter (· < k)⟩, mem_sigma.mpr ⟨hkbar, mem_filter.mpr ⟨?_, ?_⟩⟩, ?_⟩
    · exact mem_powerset.mpr fun i hi => mem_range.mpr (mem_filter.mp hi).2
    · exact fun i hi hi' => hu i (mem_filter.mp hi).1 (mem_filter.mp hi').1
    · have hbranch : branchSupport A k (u.filter (· < k)) = u := by
        rw [branchSupport, ← htop]
        ext i
        simp only [mem_union, mem_filter]
        by_cases hi : i = k
        · subst i
          simp [hk0]
        · rcases lt_or_gt_of_ne hi with h | h <;> simp [h, h.asymm]
      exact (congrArg (fun s : Finset ℕ => ∑ i ∈ s, 2 ^ i) hbranch).trans hsum

end MetaMathlibExt
