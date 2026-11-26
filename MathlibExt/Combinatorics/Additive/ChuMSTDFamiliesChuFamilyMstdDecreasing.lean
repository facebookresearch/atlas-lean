/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.ChuMSTDFamilies
import Mathlib.Data.Int.Interval
import Lean.Elab.Tactic.Omega

/-! # Decreasing-block Chu MSTD family -/

namespace MetaMathlibExt

open Pointwise

private def run (a b r : ℤ) : Finset ℤ :=
  (Finset.Icc a b).image fun i => 4 * i + r

private theorem mem_run (a b r x : ℤ) :
    x ∈ run a b r ↔ 4 * a + r ≤ x ∧ x ≤ 4 * b + r ∧ (x - r) % 4 = 0 := by
  simp only [run, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨i, ⟨ha, hb⟩, rfl⟩
    omega
  · intro ⟨ha, hb, hr⟩
    exact ⟨(x - r) / 4, ⟨by omega, by omega⟩, by omega⟩

private theorem run_add (a b c d r s : ℤ) (hab : a ≤ b) (hcd : c ≤ d) :
    run a b r + run c d s = run (a + c) (b + d) (r + s) := by
  ext x
  rw [Finset.mem_add]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    rw [mem_run] at hy hz ⊢
    omega
  · intro hx
    rw [mem_run] at hx
    let q := (x - (r + s)) / 4
    let i := max a (q - d)
    refine ⟨4 * i + r, ?_, 4 * (q - i) + s, ?_, ?_⟩
    all_goals try simp only [mem_run]
    all_goals dsimp [i, q]
    all_goals omega

private theorem run_sub (a b c d r s : ℤ) (hab : a ≤ b) (hcd : c ≤ d) :
    run a b r - run c d s = run (a - d) (b - c) (r - s) := by
  ext x
  rw [Finset.mem_sub]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    rw [mem_run] at hy hz ⊢
    omega
  · intro hx
    rw [mem_run] at hx
    let q := (x - (r - s)) / 4
    let i := max a (q + c)
    refine ⟨4 * i + r, ?_, 4 * (i - q) + s, ?_, ?_⟩
    all_goals try simp only [mem_run]
    all_goals dsimp [i, q]
    all_goals omega

private theorem card_run (a b r : ℤ) :
    (run a b r).card = (b + 1 - a).toNat := by
  rw [run, Finset.card_image_of_injective]
  · exact Int.card_Icc a b
  · intro x y h
    change 4 * x + r = 4 * y + r at h
    omega

private theorem mem_run' (a b r x : ℤ) :
    x ∈ run a b r ↔ a + r / 4 ≤ x / 4 ∧ x / 4 ≤ b + r / 4 ∧ x % 4 = r % 4 := by
  rw [mem_run]
  omega

private def family (k t u : ℤ) : Finset ℤ :=
  run 0 1 0 ∪ run (k + 3) (k + 3) 0 ∪ run (2 * k + 4) (2 * k + 4 + t) 0 ∪
    run 0 (2 * k + 4 + u) 1 ∪ run 0 0 2 ∪ run (2 * k + 4) (2 * k + 4) 2

private theorem family_add (k t u : ℤ) (hk : 1 ≤ k) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (hu : 0 ≤ u) (hut : u ≤ t) :
    family k t u + family k t u =
      run 0 2 0 ∪ run (k + 3) (k + 4) 0 ∪ run (2 * k + 4) (2 * k + 6) 0 ∪
        run (3 * k + 7) (3 * k + 7 + t) 0 ∪
          run (4 * k + 8) (4 * k + 9 + t) 0 ∪
            run 0 (4 * k + 8 + t + u) 1 ∪ run 0 (4 * k + 8 + t + u) 2 ∪
              run 0 (4 * k + 8 + u) 3 := by
  unfold family
  simp (disch := omega) only [Finset.union_add, Finset.add_union, run_add]
  ext x
  simp only [Finset.mem_union, mem_run', or_assoc]
  constructor
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      omega
  · intro h
    rcases h with h | h | h | h | h | h | h | h
    · left
      omega
    · right
      left
      omega
    · by_cases hx : x = 4 * (2 * k + 6)
      · iterate 7 right
        left
        omega
      · iterate 2 right
        left
        omega
    · iterate 8 right
      left
      omega
    · by_cases hx : x = 4 * (4 * k + 9)
      · iterate 35 right
        omega
      · iterate 14 right
        left
        omega
    · by_cases hx : x ≤ 4 * (2 * k + 5 + u) + 1
      · iterate 3 right
        left
        omega
      · iterate 15 right
        left
        omega
    · by_cases hx : x ≤ 4 * (4 * k + 8 + 2 * u) + 2
      · iterate 21 right
        left
        omega
      · iterate 17 right
        left
        omega
    · by_cases hx : x ≤ 4 * (2 * k + 4 + u) + 3
      · iterate 22 right
        left
        omega
      · iterate 23 right
        left
        omega

private def differenceRuns (k t u : ℤ) : Finset ℤ :=
  run (-2 * k - 4 - t) (2 * k + 4 + t) 0 ∪
    run (-2 * k - 4 - t) (2 * k + 4 + u) 1 ∪
      run (-2 * k - 5) (-2 * k - 4) 2 ∪ run (-k - 3) (-k - 2) 2 ∪
        run (-1) 0 2 ∪ run (k + 1) (k + 2) 2 ∪
          run (2 * k + 3) (2 * k + 4) 2 ∪
            run (-2 * k - 5 - u) (2 * k + 3 + t) 3

private theorem family_sub_subset (k t u : ℤ) (hk : 1 ≤ k) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (hu : 0 ≤ u) (hut : u ≤ t) :
    family k t u - family k t u ⊆ differenceRuns k t u := by
  unfold family differenceRuns
  simp (disch := omega) only [Finset.union_sub, Finset.sub_union, run_sub]
  intro x h
  simp only [Finset.mem_union, mem_run', or_assoc] at h ⊢
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    omega

private theorem card_differenceRuns (k t u : ℤ) (hk : 1 ≤ k) (hu : 0 ≤ u) (hut : u ≤ t) :
    ((differenceRuns k t u).card : ℤ) = 12 * k + 37 + 4 * t + 2 * u := by
  unfold differenceRuns
  simp (disch := (simp only [Finset.disjoint_left, Finset.mem_union, mem_run']; omega)) only
    [Finset.card_union_of_disjoint, card_run]
  omega

private theorem card_family_add (k t u : ℤ) (hk : 1 ≤ k) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (hu : 0 ≤ u) (hut : u ≤ t) :
    ((family k t u + family k t u).card : ℤ) = 12 * k + 38 + 4 * t + 3 * u := by
  rw [family_add k t u hk ht ht' hu hut]
  simp (disch := (simp only [Finset.disjoint_left, Finset.mem_union, mem_run']; omega)) only
    [Finset.card_union_of_disjoint, card_run]
  omega

private theorem family_mstd (k t u : ℤ) (hk : 1 ≤ k) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (hu : 0 ≤ u) (hut : u ≤ t) :
    (family k t u - family k t u).card < (family k t u + family k t u).card := by
  have hd := Finset.card_le_card (family_sub_subset k t u hk ht ht' hu hut)
  have hc := card_differenceRuns k t u hk hu hut
  have hs := card_family_add k t u hk ht ht' hu hut
  omega

private theorem replicate_four (m : ℕ) (a : ℤ) (l : List ℕ) :
    setOfConsecutiveDifferences a (List.replicate m 4 ++ l) =
      run 0 ((m : ℤ) - 1) a ∪ setOfConsecutiveDifferences (a + 4 * m) l := by
  induction m generalizing a with
  | zero =>
      ext x
      simp [mem_run]
      omega
  | succ m ih =>
      rw [List.replicate_succ, List.cons_append, setOfConsecutiveDifferences, ih]
      simp only [Nat.cast_ofNat]
      have he : a + 4 + 4 * (m : ℤ) = a + 4 * ((m + 1 : ℕ) : ℤ) := by omega
      rw [he]
      simp only [Int.natCast_add, Nat.cast_one]
      rw [← Finset.insert_union]
      congr 1
      ext x
      simp only [Finset.mem_insert, mem_run]
      omega

private theorem family_shape (k t u : ℕ) (ht : t ≤ 1) (hu : u ≤ t) :
    setOfConsecutiveDifferences 0
      ([1, 1, 2] ++ chuBlock (k + 1) ++ chuBlock k ++
        ([1, 1] ++ List.replicate t 2 ++ List.replicate u 1)) = family k t u := by
  have htc : t = 0 ∨ t = 1 := by omega
  rcases htc with rfl | rfl
  · have hue : u = 0 := by omega
    subst u
    ext x
    simp only [chuBlock, List.append_assoc, List.cons_append, List.nil_append,
      List.replicate_zero, setOfConsecutiveDifferences, replicate_four, family,
      Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, mem_run,
      Int.natCast_add, Nat.cast_one, Nat.cast_ofNat]
    omega
  · have huc : u = 0 ∨ u = 1 := by omega
    rcases huc with rfl | rfl <;> ext x <;>
      simp only [chuBlock, List.append_assoc, List.cons_append, List.nil_append,
        List.replicate_zero, List.replicate_one, setOfConsecutiveDifferences,
        replicate_four, family, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton, mem_run, Int.natCast_add, Nat.cast_one, Nat.cast_ofNat] <;> omega

private theorem tail_mstd (k t u : ℕ) (hk : 0 < k) (ht : t ≤ 1) (hu : u ≤ t) :
    let A := setOfConsecutiveDifferences 0
      ([1, 1, 2] ++ chuBlock (k + 1) ++ chuBlock k ++
        ([1, 1] ++ List.replicate t 2 ++ List.replicate u 1))
    (A - A).card < (A + A).card := by
  dsimp only
  rw [family_shape k t u ht hu]
  apply family_mstd <;> omega

/-- **MSTD sets with $M^{k+1}$ before $M^k$ (Theorem 4).** Let $k$ be a positive integer, let
$M^n$ denote the block $1, 4, \dots, 4, 3$ with $n$ fours, and let $M_1$ be one of the
sequences $(1, 1)$, $(1, 1, 2)$, $(1, 1, 2, 1)$. Let $A = (0 \mid 1, 1, 2, M^{k+1}, M^k, M_1)$
be the set of partial sums, starting from $0$, of the concatenated sequence
$1, 1, 2, M^{k+1}, M^k, M_1$. Then $A$ is sum-dominated: $|A - A| < |A + A|$.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Theorem 4 (`integers-2024-A32-thm-4`). -/
public theorem chu_family_mstd_decreasing {k : ℕ} (hk : 0 < k) {M₁ : List ℕ}
    (hM₁ : M₁ = [1, 1] ∨ M₁ = [1, 1, 2] ∨ M₁ = [1, 1, 2, 1]) :
    let A := setOfConsecutiveDifferences 0 ([1, 1, 2] ++ chuBlock (k + 1) ++ chuBlock k ++ M₁)
    (A - A).card < (A + A).card := by
  rcases hM₁ with rfl | rfl | rfl
  · exact tail_mstd k 0 0 hk (by decide) (by decide)
  · exact tail_mstd k 1 0 hk (by decide) (by decide)
  · exact tail_mstd k 1 1 hk (by decide) (by decide)

end MetaMathlibExt
