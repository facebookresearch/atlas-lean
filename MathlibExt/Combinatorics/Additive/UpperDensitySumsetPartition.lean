/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.CompletePartialOrder
public import MathlibExt.Data.Set.Density
import Mathlib.Algebra.Group.Pointwise.Set.Finite

/-!
# Splitting a set whose sumset has positive upper density

`upperDensitySumsetSplits_holds` answers the upper-density question of Erdős Problem 741.
After any cutoff, there is a block whose sumset has size at least a fixed positive multiple
of the block's upper endpoint. Assigning successive blocks alternately to the two parts gives
each sumset a sequence of cutoffs witnessing positive upper density.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SumsetPartitionErdosProblem741Wanted

open Set Filter
open scoped Pointwise

/-- **Erdős Problem 741, upper-density question.** This proposition asserts that for every set
$A \subseteq \mathbb{N}$ whose sumset $A + A = \{a + b : a, b \in A\}$ has positive upper density
there are disjoint sets $A_1, A_2 \subseteq \mathbb{N}$ with $A_1 \cup A_2 = A$ such that both
$A_1 + A_1$ and $A_2 + A_2$ have positive upper density. -/
def upperDensitySumsetSplits : Prop :=
  ∀ A : Set ℕ, 0 < (A + A).upperDensity → ∃ A₁ A₂ : Set ℕ, Disjoint A₁ A₂ ∧ A₁ ∪ A₂ = A ∧
    0 < (A₁ + A₁).upperDensity ∧ 0 < (A₂ + A₂).upperDensity

private abbrev block (A : Set ℕ) (m n : ℕ) := A ∩ Ico m n

private lemma block_finite (A : Set ℕ) (m n : ℕ) : (block A m n).Finite :=
  (finite_Ico m n).inter_of_right A

private lemma partialDensity_nat (S : Set ℕ) (n : ℕ) :
    S.partialDensity univ n = ((S ∩ Iio n).ncard : ℝ) / n := by
  simp [partialDensity]

private lemma frequently_dense (S : Set ℕ) {c : ℝ} (hc : c < S.upperDensity) :
    ∃ᶠ n in atTop, c < S.partialDensity univ n :=
  frequently_lt_of_lt_limsup (isCoboundedUnder_le_of_le atTop (x := (0 : ℝ))
    fun n ↦ by rw [partialDensity_nat]; positivity) hc

-- Doubling embeds the part of A in the block into its sumset.
private lemma count_le_cutoff_add_block_sum (A : Set ℕ) (m n : ℕ) :
    (A ∩ Iio n).ncard ≤ m + (block A m n + block A m n).ncard := by
  let B := block A m n
  have hB := block_finite A m n
  have hcover : A ∩ Iio n ⊆ Iio m ∪ B := by
    intro x hx
    by_cases h : x < m
    · exact Or.inl h
    · exact Or.inr ⟨hx.1, le_of_not_gt h, hx.2⟩
  have hd : B.ncard ≤ (B + B).ncard :=
    ncard_le_ncard_of_injOn (fun x ↦ x + x) (fun _ hx ↦ add_mem_add hx hx)
      (fun _ _ _ _ h ↦ by dsimp at h; omega) (hB.add hB)
  calc
    _ ≤ (Iio m ∪ B).ncard := ncard_le_ncard hcover ((finite_Iio m).union hB)
    _ ≤ (Iio m).ncard + B.ncard := ncard_union_le _ _
    _ ≤ _ := by simpa using Nat.add_le_add_left hd m

-- A sum below n that uses a summand below m belongs to one of m translates of A ∩ [0,n).
private lemma sum_count_le (A : Set ℕ) (m n : ℕ) :
    ((A + A) ∩ Iio n).ncard ≤
      m * (A ∩ Iio n).ncard + (block A m n + block A m n).ncard := by
  let P := A ∩ Iio n
  let B := block A m n
  have hP : P.Finite := (finite_Iio n).inter_of_right A
  have hB := block_finite A m n
  have hcover : (A + A) ∩ Iio n ⊆ (Iio m + P) ∪ (B + B) := by
    rintro _ ⟨⟨x, hx, y, hy, rfl⟩, hxy⟩
    change x + y < n at hxy
    by_cases h : x < m
    · exact Or.inl (add_mem_add h ⟨hy, by change y < n; omega⟩)
    by_cases h' : y < m
    · exact Or.inl ⟨y, h', x, ⟨hx, by change x < n; omega⟩, Nat.add_comm y x⟩
    exact Or.inr (add_mem_add ⟨hx, by omega, by omega⟩ ⟨hy, by omega, by omega⟩)
  have hsmall : (Iio m + P).ncard ≤ m * P.ncard := by
    simpa using ncard_image2_le (f := (· + ·)) (finite_Iio m) hP
  calc
    _ ≤ ((Iio m + P) ∪ (B + B)).ncard :=
      ncard_le_ncard hcover (((finite_Iio m).add hP).union (hB.add hB))
    _ ≤ (Iio m + P).ncard + (B + B).ncard := ncard_union_le _ _
    _ ≤ _ := Nat.add_le_add_right hsmall _

private lemma exists_dense_blocks (A : Set ℕ) (h : 0 < (A + A).upperDensity) :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, ∃ n > m,
      c * n ≤ ((block A m n + block A m n).ncard : ℝ) := by
  by_cases hA : 0 < A.upperDensity
  · let c := A.upperDensity / 4
    have hc : 0 < c := by dsimp [c]; positivity
    refine ⟨c, hc, fun m ↦ ?_⟩
    have hfreq := frequently_dense A (c := 2 * c) (by dsimp [c]; linarith)
    have hevent : ∀ᶠ n : ℕ in atTop, (m : ℝ) / n < c :=
      (tendsto_const_div_atTop_nhds_zero_nat (m : ℝ)).eventually_lt_const hc
    obtain ⟨n, hmn, hn, hm⟩ := frequently_atTop'.1 (hfreq.and_eventually hevent) m
    have hn₀ : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hmn)
    rw [partialDensity_nat, lt_div_iff₀ hn₀] at hn
    rw [div_lt_iff₀ hn₀] at hm
    have hcount : ((A ∩ Iio n).ncard : ℝ) ≤ m + ((block A m n + block A m n).ncard : ℝ) := by
      exact_mod_cast count_le_cutoff_add_block_sum A m n
    exact ⟨n, hmn, by linarith⟩
  · let c := (A + A).upperDensity / 4
    have hc : 0 < c := by dsimp [c]; positivity
    refine ⟨c, hc, fun m ↦ ?_⟩
    have hfreq := frequently_dense (A + A) (c := 2 * c) (by dsimp [c]; linarith)
    have hm₀ : 0 < (m : ℝ) + 1 := by positivity
    have hevent : ∀ᶠ n in atTop, A.partialDensity univ n < c / (m + 1 : ℝ) :=
      eventually_lt_of_limsup_lt (u := fun n ↦ A.partialDensity univ n)
        (lt_of_le_of_lt (le_of_not_gt hA) (div_pos hc hm₀))
        (isBoundedUnder_of ⟨1, A.partialDensity_le_one univ⟩)
    obtain ⟨n, hmn, hn, hm⟩ := frequently_atTop'.1 (hfreq.and_eventually hevent) m
    have hn₀ : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hmn)
    rw [partialDensity_nat, lt_div_iff₀ hn₀] at hn
    rw [partialDensity_nat, div_lt_div_iff₀ hn₀ hm₀] at hm
    have hcount : (((A + A) ∩ Iio n).ncard : ℝ) ≤
        m * ((A ∩ Iio n).ncard : ℝ) + ((block A m n + block A m n).ncard : ℝ) := by
      exact_mod_cast sum_count_le A m n
    exact ⟨n, hmn, by nlinarith [Nat.cast_nonneg (α := ℝ) (A ∩ Iio n).ncard]⟩

-- Any part containing cofinally many of the chosen blocks has a dense sumset.
private lemma positive_of_blocks {A T : Set ℕ} {c : ℝ} (hc : 0 < c)
    {f : ℕ → ℕ} (hf : StrictMono f)
    (hd : ∀ k, c * f (k + 1) ≤
      ((block A (f k) (f (k + 1)) + block A (f k) (f (k + 1))).ncard : ℝ))
    (hT : ∀ n, ∃ k ≥ n, block A (f k) (f (k + 1)) ⊆ T) :
    0 < (T + T).upperDensity := by
  apply lt_of_lt_of_le (half_pos hc)
  apply le_limsup_of_frequently_le _ (isBoundedUnder_of ⟨1, (T + T).partialDensity_le_one univ⟩)
  apply frequently_atTop.2
  intro n
  obtain ⟨k, hnk, hsub⟩ := hT n
  let N := f (k + 1)
  have hk : k + 1 ≤ N := hf.le_apply
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  refine ⟨2 * N, by omega, ?_⟩
  have hsum : block A (f k) N + block A (f k) N ⊆ (T + T) ∩ Iio (2 * N) := by
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact ⟨add_mem_add (hsub hx) (hsub hy), by
      have hx' := hx.2.2
      have hy' := hy.2.2
      change x + y < 2 * N
      omega⟩
  have hcount : c * N ≤ (((T + T) ∩ Iio (2 * N)).ncard : ℝ) :=
    (hd k).trans (by exact_mod_cast ncard_le_ncard hsum)
  rw [partialDensity_nat, Nat.cast_mul, Nat.cast_ofNat, le_div_iff₀ (by positivity)]
  linarith

/-- **Splitting a set whose sumset has positive upper density.** For every set
$A \subseteq \mathbb{N}$ whose sumset $A + A = \{a + b : a, b \in A\}$ has positive upper density,
there are disjoint sets $A_1, A_2 \subseteq \mathbb{N}$ with $A_1 \cup A_2 = A$ such that both
$A_1 + A_1$ and $A_2 + A_2$ have positive upper density.

Source: T. F. Bloom, Erdős Problems, Problem #741,
https://www.erdosproblems.com/741 (status SOLVED (LEAN)); resolution: B. Alexeev, M. Putterman, M.
Sawhney, M. Sellke and G. Valiant, Short proofs in combinatorics and number theory, arXiv:2603.29961
(2026); erdosproblems.com/741 (DeepMind), Theorem 3.1 of arXiv:2603.29961 (proof due to an internal
OpenAI model): there is A ⊂ ℕ, a basis of order 2 with [4, ∞) ⊆ A + A, such that for every partition
A = A₁ ⊔ A₂ one of A₁ + A₁, A₂ + A₂ does not have bounded gaps; erdosproblems.com/741: DeepMind gave
a positive answer to the upper-density question (proof sketched in the comments),
https://arxiv.org/abs/2603.29961.
-/
public theorem upperDensitySumsetSplits_holds : upperDensitySumsetSplits := by
  intro A hA
  obtain ⟨c, hc, hblocks⟩ := exists_dense_blocks A hA
  choose nextCut hlt hd using hblocks
  let f (k : ℕ) := nextCut^[k] 0
  have step (k : ℕ) : f (k + 1) = nextCut (f k) := Function.iterate_succ_apply' ..
  have hf : StrictMono f := strictMono_nat_of_lt_succ fun k ↦ (hlt (f k)).trans_eq (step k).symm
  let B (k : ℕ) := block A (f k) (f (k + 1))
  have hd' (k : ℕ) : c * f (k + 1) ≤ ((B k + B k).ncard : ℝ) := by
    simpa only [B, step k] using hd (f k)
  let S := ⋃ i : ℕ, B (2 * i)
  have hS : S ⊆ A := iUnion_subset fun _ ↦ inter_subset_left
  refine ⟨S, A \ S, disjoint_sdiff_right, union_sdiff_cancel hS, ?_, ?_⟩
  · apply positive_of_blocks hc hf hd'
    exact fun n ↦ ⟨2 * n, by omega, subset_iUnion (fun i ↦ B (2 * i)) n⟩
  · apply positive_of_blocks hc hf hd'
    intro n
    refine ⟨2 * n + 1, by omega, ?_⟩
    intro x hx
    refine ⟨hx.1, fun hxS ↦ ?_⟩
    obtain ⟨i, hi⟩ := mem_iUnion.1 hxS
    by_cases hin : i ≤ n
    · exact ((hi.2.2).trans_le (hf.monotone (by omega : 2 * i + 1 ≤ 2 * n + 1))).not_ge hx.2.1
    · exact ((hx.2.2).trans_le (hf.monotone (by omega : 2 * n + 1 + 1 ≤ 2 * i))).not_ge hi.2.1

end MathlibExt.Combinatorics.SumsetPartitionErdosProblem741Wanted
