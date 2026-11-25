/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Lattice.Nat
public import MathlibExt.NumberTheory.BinomidIndex

/-!
# Partial sums of binomid indices

`isBinomidIndex_iff_partialSum` characterizes binomid indices by superadditivity of their
partial sums and gives the partial-sum recurrence for lexicographically minimal extensions.
-/

namespace MetaMathlibExt

private theorem binomid_iff_split_le (η : ℕ → ℕ) :
    IsBinomidIndex η ↔ ∀ k n : ℕ, 1 ≤ k → k < n →
      ∑ i ∈ Finset.range (n - k), η i + ∑ i ∈ Finset.range k, η i
        ≤ ∑ i ∈ Finset.range n, η i := by
  constructor
  · intro h k n _ hkn
    rw [← Finset.sum_range_add_sum_Ico η (Nat.sub_le n k)]
    exact Nat.add_le_add_left (h k n hkn.le) _
  · intro h k n hkn
    rcases eq_or_lt_of_le hkn with rfl | hlt
    · simp
    · cases k with
      | zero => simp
      | succ k =>
        have hs := h (k + 1) n (by omega) hlt
        rw [← Finset.sum_range_add_sum_Ico η (Nat.sub_le n (k + 1))] at hs
        exact Nat.le_of_add_le_add_left hs

/-- **Partial-sum characterization of binomid indices.** Let $\eta = (e_1, e_2, \dots)$ be a
sequence of nonnegative integers with partial sums $s_n = e_1 + \dots + e_n$ (so $s_0 = 0$).
Then $\eta$ is a binomid index if and only if $s_{n-k} + s_k \le s_n$ for all $k$ and $n$ with
$1 \le k < n$. Moreover, for every $m$, if $\eta$ is the lex-minimal extension of its first $m$
entries, then for every $n > m$
$$s_n = \max_{1 \le k < n} (s_{n-k} + s_k),$$
where the maximum over the empty range (for $n = 1$) is taken to be $0$.

Source: Caalim and Tanaka, *Lexicographically Minimal Extension of a Finite
Binomid Index*, INTEGERS 24 (2024), Article A53, Lemma 1
(`integers-2024-A53-lem-1`). -/
public theorem isBinomidIndex_iff_partialSum (η : ℕ → ℕ) :
    (IsBinomidIndex η ↔ ∀ k n : ℕ, 1 ≤ k → k < n →
      ∑ i ∈ Finset.range (n - k), η i + ∑ i ∈ Finset.range k, η i
        ≤ ∑ i ∈ Finset.range n, η i) ∧
    ∀ m : ℕ, IsLexMinimalExtensionOf η m → ∀ n : ℕ, m < n →
      ∑ i ∈ Finset.range n, η i
        = (Finset.Ico 1 n).sup fun k =>
            ∑ i ∈ Finset.range (n - k), η i + ∑ i ∈ Finset.range k, η i := by
  refine ⟨binomid_iff_split_le η, ?_⟩
  rintro m hη (_ | j) hm
  · omega
  let s (n : ℕ) := ∑ i ∈ Finset.range n, η i
  let bound := (Finset.Ico 1 (j + 1)).sup fun k => s (j + 1 - k) + s k
  have hsplit := (binomid_iff_split_le η).mp hη.1
  have hbound : bound ≤ s (j + 1) :=
    Finset.sup_le fun k hk => hsplit k _ (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2
  -- Lower just this partial sum to the bound. All split inequalities still hold.
  let t (n : ℕ) := if n = j + 1 then bound else s n
  have htarget : t (j + 1) = bound := by simp [t]
  have ht (n : ℕ) : t n ≤ s n := by
    by_cases h : n = j + 1 <;> simp [t, h, hbound]
  have hzero : t 0 = 0 := by simp [t, s]
  have htsplit (k n : ℕ) (hk : 1 ≤ k) (hkn : k < n) : t (n - k) + t k ≤ t n := by
    apply (Nat.add_le_add (ht _) (ht k)).trans
    by_cases hn : n = j + 1
    · subst n
      rw [htarget]
      exact Finset.le_sup (f := fun k => s (j + 1 - k) + s k) (Finset.mem_Ico.mpr ⟨hk, hkn⟩)
    · simpa [t, hn, s] using hsplit k n hk hkn
  -- The successive differences of t therefore form a competing binomid index.
  have hmono : Monotone t := by
    apply monotone_nat_of_le_succ
    intro i
    cases i with
    | zero => simp [hzero]
    | succ i =>
      have h := htsplit 1 (i + 2) (by omega) (by omega)
      simpa using (Nat.le_add_right _ _).trans h
  let γ (i : ℕ) := t (i + 1) - t i
  have hsum (n : ℕ) : ∑ i ∈ Finset.range n, γ i = t n := by
    simpa [γ, hzero] using Finset.sum_range_tsub hmono n
  have hγ : IsBinomidIndex γ := by
    apply (binomid_iff_split_le γ).mpr
    simpa only [hsum] using htsplit
  have hagree (i : ℕ) (hi : i < j) : γ i = η i := by
    simp [γ, t, hi.ne, show i ≠ j + 1 by omega, s, Finset.sum_range_succ]
  have hle : η j ≤ γ j := by
    rcases hη.2 γ hγ (fun i hi => hagree i (by omega)) with heq | ⟨l, hl, hlt⟩
    · rw [heq]
    · rcases lt_trichotomy l j with h | rfl | h
      · exact False.elim ((hagree l h).not_gt hlt)
      · exact hlt.le
      · exact (hl j h).le
  change s (j + 1) = bound
  apply le_antisymm ?_ hbound
  calc
    s (j + 1) = s j + η j := Finset.sum_range_succ ..
    _ ≤ t j + γ j := by simpa [t] using Nat.add_le_add_left hle (s j)
    _ = t (j + 1) := by simpa only [Finset.sum_range_succ, hsum j] using hsum (j + 1)
    _ = bound := htarget

end MetaMathlibExt
