/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.SequenceAlignment
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finset.Erase

/-!
# Multiple sequence alignment: sum-of-pairs scoring

Multiple sequence alignment (Durbin et al., *Biological Sequence Analysis*,
Cambridge, 1998) aligns `k` sequences at once. An alignment is a list of
columns, each a function `Fin k → Option α` assigning each sequence either its
next letter or a gap. The score is the sum-of-pairs (SP) score: for each column,
the sum over unordered pairs of sequences of the pairwise column score, summed
over columns.

Main results:

* `inducedPair_isAlignment`: the induced pairwise alignment of any two rows is
  a valid pairwise alignment (all-gap columns for that pair are dropped).
* `msaScore_eq_sum_induced`: **the SP score is the sum of the induced pairwise
  scores** — the defining identity of sum-of-pairs scoring.
* `msaScore_le_sum_nwScore`: the SP score is at most the sum of the pairwise
  Needleman–Wunsch optima.
* `exists_isMSAlignment`: a multiple alignment exists for every family of
  sequences.

Exact optimization of the SP score is NP-hard in general; progressive and
star-alignment heuristics that approximate it are future work, as is an
enumeration of all multiple alignments.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u

variable {α : Type u}

section MSA

variable (σ : α → α → ℤ) (gap : ℤ)

/-- **Multiple alignments.** A multiple alignment with $k$ rows over an alphabet $\alpha$ is a
finite list of columns, each of which assigns to every row $i \in \{0, \dots, k-1\}$ either a
letter of $\alpha$ or a gap. No condition ties the rows to given sequences. -/
abbrev MSAlignment (k : ℕ) (α : Type*) := List (Fin k → Option α)

/-- **Valid multiple alignment.** A multiple alignment $A$ of $k$ rows is a valid multiple
alignment of sequences $s_0, \dots, s_{k-1}$ when no column of $A$ consists only of gaps and, for
every $i < k$, deleting the gaps from row $i$ of $A$ gives $s_i$. -/
def IsMSAlignment {k : ℕ} (seqs : Fin k → List α) (A : MSAlignment k α) : Prop :=
  (∀ col ∈ A, ∃ i, col i ≠ none) ∧
    ∀ i, (A.map fun col => col i).filterMap id = seqs i

/-- **Induced pairwise alignment.** Given a multiple alignment $A$ of $k$ sequences and rows
$i, j < k$, the pairwise alignment induced by $A$ on rows $i$ and $j$ is obtained by keeping, for
each column $c$ of $A$ in order, the pair $(c_i, c_j)$, and dropping the columns in which both
$c_i$ and $c_j$ are gaps. -/
def inducedPair {k : ℕ} (A : MSAlignment k α) (i j : Fin k) : Alignment α :=
  A.filterMap (fun col =>
    if (col i).isSome || (col j).isSome then some (col i, col j) else none)

/-- **Induced alignments have no all-gap column.** For a multiple alignment $A$ of $k$ sequences
and rows $i, j < k$, no column of the pairwise alignment induced by $A$ on rows $i$ and $j$ is a
gap in both rows. -/
theorem inducedPair_ne_none_none {k : ℕ} {A : MSAlignment k α} {i j : Fin k}
    {c : Option α × Option α} (hc : c ∈ inducedPair A i j) :
    c ≠ (none, none) := by
  rw [inducedPair, List.mem_filterMap] at hc
  obtain ⟨col, -, hcol⟩ := hc
  by_cases hcond : ((col i).isSome || (col j).isSome) = true
  · simp only [hcond, eq_self_iff_true, if_true] at hcol
    have hceq : (col i, col j) = c := Option.some.inj hcol
    intro hnone
    subst hnone
    have hi0 : col i = none := congrArg Prod.fst hceq
    have hj0 : col j = none := congrArg Prod.snd hceq
    rw [hi0, hj0] at hcond
    simp at hcond
  · simp only [hcond, Bool.false_eq_true, if_false] at hcol
    exact absurd hcol.symm (Option.some_ne_none _)

/-- **Letters of the first row of an induced alignment.** For a multiple alignment $A$ of $k$
sequences and rows $i, j < k$, deleting the gaps from the first row of the pairwise alignment
induced by $A$ on rows $i$ and $j$ gives the same sequence as deleting the gaps from row $i$ of
$A$. -/
theorem inducedPair_filterMap_fst {k : ℕ} {A : MSAlignment k α} {i j : Fin k} :
    (inducedPair A i j).filterMap Prod.fst =
      (A.map fun col => col i).filterMap id := by
  rw [inducedPair, List.filterMap_filterMap, List.filterMap_map]
  apply List.filterMap_congr
  intro col _
  cases hi : col i with
  | none =>
      cases hj : col j with
      | none => simp [hi, hj]
      | some b => simp [hi, hj]
  | some a => simp [hi]

/-- **Letters of the second row of an induced alignment.** For a multiple alignment $A$ of $k$
sequences and rows $i, j < k$, deleting the gaps from the second row of the pairwise alignment
induced by $A$ on rows $i$ and $j$ gives the same sequence as deleting the gaps from row $j$ of
$A$. -/
theorem inducedPair_filterMap_snd {k : ℕ} {A : MSAlignment k α} {i j : Fin k} :
    (inducedPair A i j).filterMap Prod.snd =
      (A.map fun col => col j).filterMap id := by
  rw [inducedPair, List.filterMap_filterMap, List.filterMap_map]
  apply List.filterMap_congr
  intro col _
  cases hi : col i with
  | none =>
      cases hj : col j with
      | none => simp [hi, hj]
      | some b => simp [hi, hj]
  | some a => simp [hi]

/-- **Induced pairwise alignments are valid.** Let $A$ be a valid multiple alignment of sequences
$s_0, \dots, s_{k-1}$. Then for all rows $i, j < k$, the pairwise alignment induced by $A$ on rows
$i$ and $j$ is a valid pairwise alignment of $s_i$ and $s_j$. -/
theorem inducedPair_isAlignment {k : ℕ} {seqs : Fin k → List α}
    {A : MSAlignment k α} (hA : IsMSAlignment seqs A) (i j : Fin k) :
    IsAlignment (inducedPair A i j) (seqs i) (seqs j) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    exact inducedPair_ne_none_none hc
  · rw [inducedPair_filterMap_fst, hA.2 i]
  · rw [inducedPair_filterMap_snd, hA.2 j]

/-- **Pairs of rows.** For $k \in \mathbb{N}$, the finite set of all pairs $(i, j)$ with
$i, j \in \{0, \dots, k-1\}$ and $i < j$, so that each unordered pair of distinct rows appears
exactly once. -/
def pairFinset (k : ℕ) : Finset (Fin k × Fin k) :=
  Finset.univ.filter (fun p => p.1 < p.2)

/-- **Sum-of-pairs score of a column.** Let $\sigma$ assign an integer score to each pair of
letters and let $g$ be an integer gap score. For a column $c$ of a multiple alignment of $k$
sequences, which gives each row $r < k$ either a letter or a gap $c_r$, the sum-of-pairs score of
$c$ is $\sum_{i < j < k} s(c_i, c_j)$, where $s$ is the pairwise column score: $\sigma(a, b)$ for
letters $a$ and $b$, $g$ for a letter against a gap, and $0$ for two gaps. -/
def columnSP {k : ℕ} (col : Fin k → Option α) : ℤ :=
  ∑ p ∈ pairFinset k, columnScore σ gap (col p.1, col p.2)

/-- **Sum-of-pairs score.** Fix a score $\sigma(a, b) \in \mathbb{Z}$ for each pair of letters
$a, b$ and a gap score $g \in \mathbb{Z}$. For two entries $x, y$, each a letter or a gap, let
$s(x, y) = \sigma(x, y)$ if both are letters, $s(x, y) = g$ if exactly one is a gap, and
$s(x, y) = 0$ if both are gaps. The sum-of-pairs score of a multiple alignment $A$ of $k$
sequences is the sum, over the columns $c$ of $A$, of $\sum_{0 \le i < j < k} s(c_i, c_j)$,
where $c_i$ is the entry of $c$ in row $i$. -/
def msaScore {k : ℕ} (A : MSAlignment k α) : ℤ :=
  (A.map (fun col => columnSP σ gap col)).sum

/-- A list-sum over a finset-sum swaps: the two ways of totaling a table. -/
private theorem sum_map_finset_sum {k : ℕ} (A : MSAlignment k α)
    (S : Finset (Fin k × Fin k)) (f : (Fin k × Fin k) → (Fin k → Option α) → ℤ) :
    (A.map (fun col => ∑ p ∈ S, f p col)).sum =
      ∑ p ∈ S, (A.map (fun col => f p col)).sum := by
  induction A with
  | nil => simp
  | cons col A' ih =>
      simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

/-- **Score of an induced pairwise alignment.** Let $\sigma$ assign an integer score to each
pair of letters and let $g$ be an integer gap score. For a multiple alignment $A$ of $k$
sequences and rows $i, j < k$, the score (with respect to $\sigma$ and $g$) of the pairwise
alignment induced by $A$ on rows $i$ and $j$ equals the sum, over all columns $c$ of $A$, of the
column score of the pair $(c_i, c_j)$. -/
theorem alignmentScore_inducedPair {k : ℕ} {A : MSAlignment k α} (i j : Fin k) :
    alignmentScore σ gap (inducedPair A i j) =
      (A.map (fun col => columnScore σ gap (col i, col j))).sum := by
  induction A with
  | nil => rfl
  | cons col A' ih =>
      cases hi : col i with
      | none =>
          cases hj : col j with
          | none =>
              have hcond : ((col i).isSome || (col j).isSome) = false := by
                simp [hi, hj]
              have e1 : inducedPair (col :: A') i j = inducedPair A' i j := by
                simp only [inducedPair, List.filterMap_cons, hcond,
                  Bool.false_eq_true, if_false]
              have e2 : ((col :: A').map
                  (fun c => columnScore σ gap (c i, c j))).sum =
                  (A'.map (fun c => columnScore σ gap (c i, c j))).sum := by
                simp [hi, hj, columnScore]
              rw [e1, e2]
              exact ih
          | some b =>
              have hcond : ((col i).isSome || (col j).isSome) = true := by
                simp [hi, hj]
              have e1 : inducedPair (col :: A') i j =
                  (col i, col j) :: inducedPair A' i j := by
                simp only [inducedPair, List.filterMap_cons, hcond,
                  eq_self_iff_true, if_true]
              have escore : alignmentScore σ gap
                    ((col i, col j) :: inducedPair A' i j) =
                  columnScore σ gap (col i, col j) +
                    alignmentScore σ gap (inducedPair A' i j) := by
                simp [alignmentScore]
              rw [e1, escore, ih]
              simp [List.map_cons, List.sum_cons]
      | some a =>
          have hcond : ((col i).isSome || (col j).isSome) = true := by
            simp [hi]
          have e1 : inducedPair (col :: A') i j =
              (col i, col j) :: inducedPair A' i j := by
            simp only [inducedPair, List.filterMap_cons, hcond,
              eq_self_iff_true, if_true]
          have escore : alignmentScore σ gap
                ((col i, col j) :: inducedPair A' i j) =
              columnScore σ gap (col i, col j) +
                alignmentScore σ gap (inducedPair A' i j) := by
            simp [alignmentScore]
          rw [e1, escore, ih]
          simp [List.map_cons, List.sum_cons]

/-- **The SP score is the sum of the induced pairwise scores.** Let $\sigma$ assign an integer
score to each pair of letters and let $g$ be an integer gap score. For every multiple alignment
$A$ of $k$ sequences, the sum-of-pairs score of $A$ equals the sum, over all pairs of rows
$i < j < k$, of the score of the pairwise alignment induced by $A$ on rows $i$ and $j$. -/
theorem msaScore_eq_sum_induced {k : ℕ} {A : MSAlignment k α} :
    msaScore σ gap A =
      ∑ p ∈ pairFinset k, alignmentScore σ gap (inducedPair A p.1 p.2) := by
  simp only [msaScore, columnSP]
  rw [sum_map_finset_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [alignmentScore_inducedPair]

/-- **The sum-of-pairs score is bounded by the pairwise optima.** Fix a score
$\sigma(a, b) \in \mathbb{Z}$ for each pair of letters $a, b$ of an alphabet $\alpha$ and a gap
score $g \in \mathbb{Z}$. Let $s_0, \dots, s_{k-1}$ be sequences over $\alpha$ and let $A$ be a
valid multiple alignment of them: no column of $A$ consists only of gaps, and deleting the gaps
from row $i$ of $A$ leaves $s_i$. Then the sum-of-pairs score of $A$ under $\sigma$ and $g$ is at
most $\sum_{0 \le i < j < k} \mathrm{NW}(s_i, s_j)$, where $\mathrm{NW}(s_i, s_j)$ is the optimal
global (Needleman–Wunsch) alignment score of $s_i$ and $s_j$ under $\sigma$ and $g$. -/
theorem msaScore_le_sum_nwScore {k : ℕ} {seqs : Fin k → List α}
    {A : MSAlignment k α} (hA : IsMSAlignment seqs A) :
    msaScore σ gap A ≤
      ∑ p ∈ pairFinset k, nwScore σ gap (seqs p.1) (seqs p.2) := by
  rw [msaScore_eq_sum_induced]
  apply Finset.sum_le_sum
  intro p _
  exact alignmentScore_le_nwScore σ gap _ _ (inducedPair A p.1 p.2)
    (inducedPair_isAlignment hA p.1 p.2)

/-- **Every family of sequences has a multiple alignment.** For every natural number $n$ and
every family of $k$ sequences $s_0, \dots, s_{k-1}$ whose lengths sum to at most $n$, there is a
valid multiple alignment of $s_0, \dots, s_{k-1}$.

The bound $n$ is the parameter of the induction in the proof, which removes the first letter of
one nonempty sequence; taking $n$ to be the total length shows that every finite family of
sequences has a valid multiple alignment. -/
theorem exists_isMSAlignment : ∀ (n : ℕ) {k : ℕ} (seqs : Fin k → List α),
    (∑ i, (seqs i).length) ≤ n → ∃ A, IsMSAlignment seqs A := by
  intro n
  induction n with
  | zero =>
      intro k seqs hsum
      have hzero : ∀ i, (seqs i).length = 0 := by
        have h := (Finset.sum_eq_zero_iff_of_nonneg
          (s := Finset.univ) (f := fun i => (seqs i).length)
          (fun i _ => Nat.zero_le _)).mp (Nat.eq_zero_of_le_zero hsum)
        intro i
        exact h i (Finset.mem_univ i)
      refine ⟨[], ?_, ?_⟩
      · intro col hc
        simp at hc
      · intro i
        have hi : seqs i = [] := List.length_eq_zero_iff.mp (hzero i)
        simp [hi]
  | succ n ih =>
      intro k seqs hsum
      by_cases hall : ∀ i, seqs i = []
      · refine ⟨[], ?_, ?_⟩
        · intro col hc
          simp at hc
        · intro i
          simp [hall i]
      · push_neg at hall
        obtain ⟨i, hi⟩ := hall
        obtain ⟨a, rest, hrest⟩ := List.exists_cons_of_ne_nil hi
        set seqs' := Function.update seqs i rest with hseqs'
        have hlen_i : (seqs i).length = rest.length + 1 := by rw [hrest]; simp
        have hsum' : (∑ j, (seqs' j).length) ≤ n := by
          have h1 := Finset.add_sum_erase (Finset.univ : Finset (Fin _))
            (fun j => (seqs j).length) (Finset.mem_univ i)
          have h2 := Finset.add_sum_erase (Finset.univ : Finset (Fin _))
            (fun j => (seqs' j).length) (Finset.mem_univ i)
          have hrest : ∀ j ∈ (Finset.univ : Finset (Fin _)).erase i,
              (seqs' j).length = (seqs j).length := by
            intro j hj
            rw [Finset.mem_erase] at hj
            rw [hseqs', Function.update_of_ne hj.1 rest seqs]
          have hsum_erase : ∑ j ∈ (Finset.univ : Finset (Fin _)).erase i,
              (seqs' j).length =
              ∑ j ∈ (Finset.univ : Finset (Fin _)).erase i,
              (seqs j).length :=
            Finset.sum_congr rfl hrest
          have hself : seqs' i = rest := by
            rw [hseqs']
            exact Function.update_self _ _ _
          rw [hself] at h2
          omega
        obtain ⟨A', hA'⟩ := ih seqs' hsum'
        set col0 : Fin _ → Option α := fun j => if j = i then some a else none with hcol0
        refine ⟨col0 :: A', ?_, ?_⟩
        · intro col hc
          rw [List.mem_cons] at hc
          rcases hc with rfl | hc
          · exact ⟨i, by simp [hcol0]⟩
          · exact hA'.1 col hc
        · intro j
          by_cases hji : j = i
          · rw [hji]
            have hcol0i : col0 i = some a := by simp [hcol0]
            have hmap : ((col0 :: A').map fun col => col i) =
                some a :: (A'.map fun col => col i) := by
              simp [List.map_cons, hcol0i]
            rw [hmap]
            show a :: ((A'.map fun col => col i).filterMap id) = seqs i
            have hrow := hA'.2 i
            have hself : seqs' i = rest := by
              rw [hseqs']
              exact Function.update_self _ _ _
            rw [hself] at hrow
            rw [hrow, ← hrest]
          · have hcol0j : col0 j = none := by simp [hcol0, hji]
            have hmap : ((col0 :: A').map fun col => col j) =
                none :: (A'.map fun col => col j) := by
              simp [List.map_cons, hcol0j]
            rw [hmap]
            show ((A'.map fun col => col j).filterMap id) = seqs j
            have hrow := hA'.2 j
            have hother : seqs' j = seqs j := by
              rw [hseqs']
              exact Function.update_of_ne hji rest seqs
            rw [hother] at hrow
            exact hrow

end MSA

end Cslib.Algorithms.Lean
