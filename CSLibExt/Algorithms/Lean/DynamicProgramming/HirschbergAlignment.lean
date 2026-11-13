/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.SequenceAlignment

/-!
# Hirschberg linear-space reconstruction

Hirschberg's algorithm (Hirschberg, *A linear space algorithm for computing
maximal common subsequences*, Comm. ACM 1975; Durbin et al., *Biological
Sequence Analysis*, Cambridge, 1998) recovers an optimal alignment without
building the full dynamic-programming table: split one sequence in half, score
the two halves against every split of the other sequence, pick the split that
maximizes the sum of the two half-scores, and recurse on the two halves. Only
the split scores are needed, never the whole table.

Main results:

* `isAlignment_hirschberg`, `alignmentScore_hirschberg`: **Hirschberg
  reconstruction is correct**: it returns a valid alignment whose score is the
  Needleman–Wunsch optimum.
* `nwScore_eq_bestSplit_ys`, `nwScore_eq_bestSplit_xs`: the split identity the
  recursion rests on — the optimum is the sum of the two half-optima at the
  argmax split.

Cost model: as with `nwScore`, the split scores are specified via `nwScore` on
prefixes and suffixes, not computed by two-row dynamic programs; a tabulated
linear-space implementation proved equal to this specification is future work.
The recursion splits the longer sequence, so every recursive call is on a
strictly smaller total length (except the `≤ 1 × ≤ 1` base case, handled
directly by `smallAlign`).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u

variable {α : Type u}

section Hirschberg

variable (σ : α → α → ℤ) (gap : ℤ)

/-- **Argmax over an initial segment.** For a function $f : \mathbb{N} \to \mathbb{Z}$ and
$n \in \mathbb{N}$, the argmax of $f$ over $\{0, \dots, n\}$ is the least $k \le n$ such that
$f(j) \le f(k)$ for all $j \le n$.

It is computed as the first maximizer of $f$ on the list $[0, 1, \dots, n]$, which is never
empty. -/
def bestArgmax (f : ℕ → ℤ) (n : ℕ) : ℕ :=
  ((List.range (n + 1)).argmax f).getD 0

/-- **The argmax over $\{0, \dots, n\}$ is at most $n$.** For every function
$f : \mathbb{N} \to \mathbb{Z}$ and every $n \in \mathbb{N}$, the argmax of $f$ over
$\{0, \dots, n\}$ is at most $n$. -/
theorem bestArgmax_le (f : ℕ → ℤ) (n : ℕ) : bestArgmax f n ≤ n := by
  unfold bestArgmax
  cases h : (List.range (n + 1)).argmax f with
  | none =>
      have hempty := List.argmax_eq_none.mp h
      have hmem : (0 : ℕ) ∈ List.range (n + 1) :=
        List.mem_range.mpr (Nat.zero_lt_succ _)
      rw [hempty] at hmem
      simp at hmem
  | some m =>
      have hmem : m ∈ List.range (n + 1) :=
        List.argmax_mem (Option.mem_def.2 h)
      rw [List.mem_range] at hmem
      show m ≤ n
      omega

/-- **The argmax over $\{0, \dots, n\}$ maximizes the function there.** Let
$f : \mathbb{N} \to \mathbb{Z}$, let $n \in \mathbb{N}$ and let $m$ be the argmax of $f$ over
$\{0, \dots, n\}$. Then $f(k) \le f(m)$ for every $k \le n$. -/
theorem bestArgmax_spec (f : ℕ → ℤ) {n k : ℕ} (hk : k ≤ n) :
    f k ≤ f (bestArgmax f n) := by
  unfold bestArgmax
  cases h : (List.range (n + 1)).argmax f with
  | none =>
      have hempty := List.argmax_eq_none.mp h
      have hmem : (0 : ℕ) ∈ List.range (n + 1) :=
        List.mem_range.mpr (Nat.zero_lt_succ _)
      rw [hempty] at hmem
      simp at hmem
  | some m =>
      show f k ≤ f m
      exact List.le_of_mem_argmax (List.mem_range.mpr (by omega))
        (Option.mem_def.2 h)

/-- Splitting a column list at a given second-row length: the first part has
exactly `m` second-row entries. -/
private theorem exists_split_filterMap_snd (A : Alignment α) (m : ℕ)
    (hm : m ≤ (A.filterMap Prod.snd).length) :
    ∃ A1 A2, A = A1 ++ A2 ∧ (A1.filterMap Prod.snd).length = m ∧
      (A2.filterMap Prod.snd).length = (A.filterMap Prod.snd).length - m := by
  induction A generalizing m with
  | nil =>
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero (by simpa using hm)
      exact ⟨[], [], rfl, by simp [hm0], by simp [hm0]⟩
  | cons c A' ih =>
      obtain ⟨c1, c2⟩ := c
      cases c2 with
      | none =>
          have hlen : (List.filterMap Prod.snd ((c1, none) :: A')).length
              = (A'.filterMap Prod.snd).length := by
            simp [List.filterMap_cons]
          obtain ⟨A1, A2, hA, h1, h2⟩ := ih m (by rw [hlen] at hm; exact hm)
          refine ⟨(c1, none) :: A1, A2, ?_, ?_, ?_⟩
          · simp [hA]
          · simp only [List.filterMap_cons, List.length_cons]
            omega
          · rw [hlen]
            exact h2
      | some b =>
          have hlen : (List.filterMap Prod.snd ((c1, some b) :: A')).length
              = (A'.filterMap Prod.snd).length + 1 := by
            simp [List.filterMap_cons]
          cases m with
          | zero =>
              refine ⟨[], (c1, some b) :: A', by simp, by simp, ?_⟩
              rw [hlen]
              simp
          | succ m' =>
              obtain ⟨A1, A2, hA, h1, h2⟩ := ih m' (by rw [hlen] at hm; omega)
              refine ⟨(c1, some b) :: A1, A2, ?_, ?_, ?_⟩
              · simp [hA]
              · simp only [List.filterMap_cons, List.length_cons]
                omega
              · rw [hlen]
                omega

/-- Splitting a column list at a given first-row length (mirror of the above). -/
private theorem exists_split_filterMap_fst (A : Alignment α) (m : ℕ)
    (hm : m ≤ (A.filterMap Prod.fst).length) :
    ∃ A1 A2, A = A1 ++ A2 ∧ (A1.filterMap Prod.fst).length = m ∧
      (A2.filterMap Prod.fst).length = (A.filterMap Prod.fst).length - m := by
  induction A generalizing m with
  | nil =>
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero (by simpa using hm)
      exact ⟨[], [], rfl, by simp [hm0], by simp [hm0]⟩
  | cons c A' ih =>
      obtain ⟨c1, c2⟩ := c
      cases c1 with
      | none =>
          have hlen : (List.filterMap Prod.fst ((none, c2) :: A')).length
              = (A'.filterMap Prod.fst).length := by
            simp [List.filterMap_cons]
          obtain ⟨A1, A2, hA, h1, h2⟩ := ih m (by rw [hlen] at hm; exact hm)
          refine ⟨(none, c2) :: A1, A2, ?_, ?_, ?_⟩
          · simp [hA]
          · simp only [List.filterMap_cons, List.length_cons]
            omega
          · rw [hlen]
            exact h2
      | some a =>
          have hlen : (List.filterMap Prod.fst ((some a, c2) :: A')).length
              = (A'.filterMap Prod.fst).length + 1 := by
            simp [List.filterMap_cons]
          cases m with
          | zero =>
              refine ⟨[], (some a, c2) :: A', by simp, by simp, ?_⟩
              rw [hlen]
              simp
          | succ m' =>
              obtain ⟨A1, A2, hA, h1, h2⟩ := ih m' (by rw [hlen] at hm; omega)
              refine ⟨(some a, c2) :: A1, A2, ?_, ?_, ?_⟩
              · simp [hA]
              · simp only [List.filterMap_cons, List.length_cons]
                omega
              · rw [hlen]
                omega

/-- Splitting a valid alignment at `m` second-row letters gives valid alignments
of the two halves. -/
private theorem exists_split_alignment_snd {A : Alignment α} {xs ys : List α}
    (hA : IsAlignment A xs ys) {m : ℕ} (hm : m ≤ ys.length) :
    ∃ k A1 A2, k ≤ xs.length ∧ A = A1 ++ A2 ∧
      IsAlignment A1 (List.take k xs) (List.take m ys) ∧
      IsAlignment A2 (List.drop k xs) (List.drop m ys) ∧
      alignmentScore σ gap A = alignmentScore σ gap A1 + alignmentScore σ gap A2 := by
  have hsplit := exists_split_filterMap_snd (α := α) A m (by rw [hA.2.2]; exact hm)
  obtain ⟨A1, A2, hAeq, h1, h2⟩ := hsplit
  have hxs : xs = A1.filterMap Prod.fst ++ A2.filterMap Prod.fst := by
    rw [← hA.2.1, hAeq, List.filterMap_append]
  have hys : ys = A1.filterMap Prod.snd ++ A2.filterMap Prod.snd := by
    rw [← hA.2.2, hAeq, List.filterMap_append]
  have hk_le : (A1.filterMap Prod.fst).length ≤ xs.length := by
    rw [hxs, List.length_append]
    exact Nat.le_add_right _ _
  refine ⟨(A1.filterMap Prod.fst).length, A1, A2, hk_le, hAeq, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro c hc
      apply hA.1 c
      rw [hAeq]
      exact List.mem_append_left _ hc
    · rw [hxs]
      exact List.take_left.symm
    · rw [hys, ← h1]
      exact List.take_left.symm
  · refine ⟨?_, ?_, ?_⟩
    · intro c hc
      apply hA.1 c
      rw [hAeq]
      exact List.mem_append_right _ hc
    · rw [hxs]
      exact List.drop_left.symm
    · rw [hys, ← h1]
      exact List.drop_left.symm
  · rw [hAeq, alignmentScore_append]

/-- Splitting a valid alignment at `m` first-row letters (mirror image). -/
private theorem exists_split_alignment_fst {A : Alignment α} {xs ys : List α}
    (hA : IsAlignment A xs ys) {m : ℕ} (hm : m ≤ xs.length) :
    ∃ k A1 A2, k ≤ ys.length ∧ A = A1 ++ A2 ∧
      IsAlignment A1 (List.take m xs) (List.take k ys) ∧
      IsAlignment A2 (List.drop m xs) (List.drop k ys) ∧
      alignmentScore σ gap A = alignmentScore σ gap A1 + alignmentScore σ gap A2 := by
  have hsplit := exists_split_filterMap_fst (α := α) A m (by rw [hA.2.1]; exact hm)
  obtain ⟨A1, A2, hAeq, h1, h2⟩ := hsplit
  have hxs : xs = A1.filterMap Prod.fst ++ A2.filterMap Prod.fst := by
    rw [← hA.2.1, hAeq, List.filterMap_append]
  have hys : ys = A1.filterMap Prod.snd ++ A2.filterMap Prod.snd := by
    rw [← hA.2.2, hAeq, List.filterMap_append]
  have hk_le : (A1.filterMap Prod.snd).length ≤ ys.length := by
    rw [hys, List.length_append]
    exact Nat.le_add_right _ _
  refine ⟨(A1.filterMap Prod.snd).length, A1, A2, hk_le, hAeq, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro c hc
      apply hA.1 c
      rw [hAeq]
      exact List.mem_append_left _ hc
    · rw [hxs, ← h1]
      exact List.take_left.symm
    · rw [hys]
      exact List.take_left.symm
  · refine ⟨?_, ?_, ?_⟩
    · intro c hc
      apply hA.1 c
      rw [hAeq]
      exact List.mem_append_right _ hc
    · rw [hxs, ← h1]
      exact List.drop_left.symm
    · rw [hys]
      exact List.drop_left.symm
  · rw [hAeq, alignmentScore_append]

/-- **A split of the second sequence scores at most the Needleman–Wunsch optimum.** Let
$\sigma$ be an integer-valued substitution score on an alphabet, let $g$ be an integer gap
score, and write $\mathrm{NW}(x, y)$ for the optimal Needleman–Wunsch global alignment score
of sequences $x$ and $y$ under $\sigma$ and $g$. For sequences $x$, $y$ and natural numbers
$k$, $m$, let $x_{<k}$ be the first $k$ letters of $x$ (all of $x$ if $k$ is at least its
length) and $x_{\ge k}$ the remaining letters, and define $y_{<m}$ and $y_{\ge m}$ likewise.
Then $\mathrm{NW}(x_{<k}, y_{<m}) + \mathrm{NW}(x_{\ge k}, y_{\ge m}) \le \mathrm{NW}(x, y)$.

The bound holds because optimal alignments of the two halves concatenate to an alignment of
$x$ and $y$. -/
theorem splitScore_le_nwScore_ys (xs ys : List α) {mid k : ℕ} :
    nwScore σ gap (List.take k xs) (List.take mid ys) +
      nwScore σ gap (List.drop k xs) (List.drop mid ys) ≤ nwScore σ gap xs ys := by
  obtain ⟨A1, hA1, hs1⟩ := exists_alignmentScore_eq_nwScore σ gap
    (List.take k xs) (List.take mid ys)
  obtain ⟨A2, hA2, hs2⟩ := exists_alignmentScore_eq_nwScore σ gap
    (List.drop k xs) (List.drop mid ys)
  have happend := isAlignment_append hA1 hA2
  rw [List.take_append_drop, List.take_append_drop] at happend
  rw [← hs1, ← hs2, ← alignmentScore_append]
  exact alignmentScore_le_nwScore σ gap xs ys (A1 ++ A2) happend

/-- **A split of the first sequence scores at most the Needleman–Wunsch optimum.** Let
$\sigma$ be an integer-valued substitution score on an alphabet, let $g$ be an integer gap
score, and write $\mathrm{NW}(x, y)$ for the optimal Needleman–Wunsch global alignment score
of sequences $x$ and $y$ under $\sigma$ and $g$. For sequences $x$, $y$ and natural numbers
$m$, $k$, let $x_{<m}$ be the first $m$ letters of $x$ (all of $x$ if $m$ is at least its
length) and $x_{\ge m}$ the remaining letters, and define $y_{<k}$ and $y_{\ge k}$ likewise.
Then $\mathrm{NW}(x_{<m}, y_{<k}) + \mathrm{NW}(x_{\ge m}, y_{\ge k}) \le \mathrm{NW}(x, y)$. -/
theorem splitScore_le_nwScore_xs (xs ys : List α) {mid k : ℕ} :
    nwScore σ gap (List.take mid xs) (List.take k ys) +
      nwScore σ gap (List.drop mid xs) (List.drop k ys) ≤ nwScore σ gap xs ys := by
  obtain ⟨A1, hA1, hs1⟩ := exists_alignmentScore_eq_nwScore σ gap
    (List.take mid xs) (List.take k ys)
  obtain ⟨A2, hA2, hs2⟩ := exists_alignmentScore_eq_nwScore σ gap
    (List.drop mid xs) (List.drop k ys)
  have happend := isAlignment_append hA1 hA2
  rw [List.take_append_drop, List.take_append_drop] at happend
  rw [← hs1, ← hs2, ← alignmentScore_append]
  exact alignmentScore_le_nwScore σ gap xs ys (A1 ++ A2) happend

/-- **Every cut of the second list extends to an optimal split.** Fix a type $\alpha$, a
substitution score $\sigma : \alpha \to \alpha \to \mathbb{Z}$ and a gap score $g \in \mathbb{Z}$.
Write $S(u, v)$ for the Needleman–Wunsch score of lists $u$, $v$, and $u_{<m}$ for the first
$m$ elements of $u$ and $u_{\ge m}$ for the rest. For all lists $xs$, $ys$ over $\alpha$ and
every $m \le |ys|$, there is $k \le |xs|$ with
$S(xs_{<k}, ys_{<m}) + S(xs_{\ge k}, ys_{\ge m}) = S(xs, ys)$. -/
theorem exists_split_eq_nwScore_ys (xs ys : List α) {mid : ℕ}
    (hmid : mid ≤ ys.length) :
    ∃ k ≤ xs.length, nwScore σ gap (List.take k xs) (List.take mid ys) +
      nwScore σ gap (List.drop k xs) (List.drop mid ys) = nwScore σ gap xs ys := by
  obtain ⟨A, hA, hscore⟩ := exists_alignmentScore_eq_nwScore σ gap xs ys
  obtain ⟨k, A1, A2, hk, -, hA1, hA2, hsplit⟩ :=
    exists_split_alignment_snd σ gap hA hmid
  refine ⟨k, hk, ?_⟩
  · apply le_antisymm
    · exact splitScore_le_nwScore_ys σ gap xs ys
    · rw [← hscore, hsplit]
      exact add_le_add (alignmentScore_le_nwScore σ gap _ _ A1 hA1)
        (alignmentScore_le_nwScore σ gap _ _ A2 hA2)

/-- **Every cut of the first list extends to an optimal split.** Fix a type $\alpha$, a
substitution score $\sigma : \alpha \to \alpha \to \mathbb{Z}$ and a gap score $g \in \mathbb{Z}$.
Write $S(u, v)$ for the Needleman–Wunsch score of lists $u$, $v$, and $u_{<m}$ for the first
$m$ elements of $u$ and $u_{\ge m}$ for the rest. For all lists $xs$, $ys$ over $\alpha$ and
every $m \le |xs|$, there is $k \le |ys|$ with
$S(xs_{<m}, ys_{<k}) + S(xs_{\ge m}, ys_{\ge k}) = S(xs, ys)$. -/
theorem exists_split_eq_nwScore_xs (xs ys : List α) {mid : ℕ}
    (hmid : mid ≤ xs.length) :
    ∃ k ≤ ys.length, nwScore σ gap (List.take mid xs) (List.take k ys) +
      nwScore σ gap (List.drop mid xs) (List.drop k ys) = nwScore σ gap xs ys := by
  obtain ⟨A, hA, hscore⟩ := exists_alignmentScore_eq_nwScore σ gap xs ys
  obtain ⟨k, A1, A2, hk, -, hA1, hA2, hsplit⟩ :=
    exists_split_alignment_fst σ gap hA hmid
  refine ⟨k, hk, ?_⟩
  · apply le_antisymm
    · exact splitScore_le_nwScore_xs σ gap xs ys
    · rw [← hscore, hsplit]
      exact add_le_add (alignmentScore_le_nwScore σ gap _ _ A1 hA1)
        (alignmentScore_le_nwScore σ gap _ _ A2 hA2)

/-- **Hirschberg split identity, splitting the second sequence.** Fix a substitution score
$\sigma$ assigning an integer to each pair of letters and an integer gap score $g$, and write
$\mathrm{NW}$ for the Needleman–Wunsch score. For a sequence $s$, write $s_{<j}$ for its first
$j$ letters and $s_{\ge j}$ for the remaining letters. Let $x$, $y$ be sequences and
$m \le |y|$, and let $k$ be the first index $j \in \{0, \dots, |x|\}$ that maximizes
$\mathrm{NW}(x_{<j}, y_{<m}) + \mathrm{NW}(x_{\ge j}, y_{\ge m})$. Then
$\mathrm{NW}(x_{<k}, y_{<m}) + \mathrm{NW}(x_{\ge k}, y_{\ge m}) = \mathrm{NW}(x, y)$. -/
theorem nwScore_eq_bestSplit_ys (xs ys : List α) {mid : ℕ}
    (hmid : mid ≤ ys.length) :
    nwScore σ gap
        (List.take (bestArgmax (fun k => nwScore σ gap (List.take k xs)
          (List.take mid ys) + nwScore σ gap (List.drop k xs)
          (List.drop mid ys)) xs.length) xs) (List.take mid ys) +
      nwScore σ gap
        (List.drop (bestArgmax (fun k => nwScore σ gap (List.take k xs)
          (List.take mid ys) + nwScore σ gap (List.drop k xs)
          (List.drop mid ys)) xs.length) xs) (List.drop mid ys) =
    nwScore σ gap xs ys := by
  have hle : (fun k => nwScore σ gap (List.take k xs) (List.take mid ys) +
      nwScore σ gap (List.drop k xs) (List.drop mid ys))
      (bestArgmax (fun k => nwScore σ gap (List.take k xs) (List.take mid ys) +
        nwScore σ gap (List.drop k xs) (List.drop mid ys)) xs.length)
      ≤ nwScore σ gap xs ys :=
    splitScore_le_nwScore_ys σ gap xs ys
  obtain ⟨k, hk, hkeq⟩ := exists_split_eq_nwScore_ys σ gap xs ys hmid
  have hge : nwScore σ gap xs ys ≤ (fun k => nwScore σ gap (List.take k xs)
      (List.take mid ys) + nwScore σ gap (List.drop k xs)
      (List.drop mid ys))
      (bestArgmax (fun k => nwScore σ gap (List.take k xs) (List.take mid ys) +
        nwScore σ gap (List.drop k xs) (List.drop mid ys)) xs.length) := by
    rw [← hkeq]
    exact bestArgmax_spec (fun k => nwScore σ gap (List.take k xs) (List.take mid ys) +
      nwScore σ gap (List.drop k xs) (List.drop mid ys)) hk
  exact le_antisymm hle hge

/-- **Hirschberg split identity, splitting the first sequence.** Fix a substitution score
$\sigma$ assigning an integer to each pair of letters and an integer gap score $g$, and write
$\mathrm{NW}$ for the Needleman–Wunsch score. For a sequence $s$, write $s_{<j}$ for its first
$j$ letters and $s_{\ge j}$ for the remaining letters. Let $x$, $y$ be sequences and
$m \le |x|$, and let $k$ be the first index $j \in \{0, \dots, |y|\}$ that maximizes
$\mathrm{NW}(x_{<m}, y_{<j}) + \mathrm{NW}(x_{\ge m}, y_{\ge j})$. Then
$\mathrm{NW}(x_{<m}, y_{<k}) + \mathrm{NW}(x_{\ge m}, y_{\ge k}) = \mathrm{NW}(x, y)$. -/
theorem nwScore_eq_bestSplit_xs (xs ys : List α) {mid : ℕ}
    (hmid : mid ≤ xs.length) :
    nwScore σ gap (List.take mid xs)
        (List.take (bestArgmax (fun k => nwScore σ gap (List.take mid xs)
          (List.take k ys) + nwScore σ gap (List.drop mid xs)
          (List.drop k ys)) ys.length) ys) +
      nwScore σ gap (List.drop mid xs)
        (List.drop (bestArgmax (fun k => nwScore σ gap (List.take mid xs)
          (List.take k ys) + nwScore σ gap (List.drop mid xs)
          (List.drop k ys)) ys.length) ys) =
    nwScore σ gap xs ys := by
  have hle : (fun k => nwScore σ gap (List.take mid xs) (List.take k ys) +
      nwScore σ gap (List.drop mid xs) (List.drop k ys))
      (bestArgmax (fun k => nwScore σ gap (List.take mid xs) (List.take k ys) +
        nwScore σ gap (List.drop mid xs) (List.drop k ys)) ys.length)
      ≤ nwScore σ gap xs ys :=
    splitScore_le_nwScore_xs σ gap xs ys
  obtain ⟨k, hk, hkeq⟩ := exists_split_eq_nwScore_xs σ gap xs ys hmid
  have hge : nwScore σ gap xs ys ≤ (fun k => nwScore σ gap (List.take mid xs)
      (List.take k ys) + nwScore σ gap (List.drop mid xs)
      (List.drop k ys))
      (bestArgmax (fun k => nwScore σ gap (List.take mid xs) (List.take k ys) +
        nwScore σ gap (List.drop mid xs) (List.drop k ys)) ys.length) := by
    rw [← hkeq]
    exact bestArgmax_spec (fun k => nwScore σ gap (List.take mid xs) (List.take k ys) +
      nwScore σ gap (List.drop mid xs) (List.drop k ys)) hk
  exact le_antisymm hle hge


/-- **Needleman–Wunsch score of two single letters.** For every substitution score $\sigma$
assigning an integer to each pair of letters, integer gap score $g$ and letters $a$, $b$, the
Needleman–Wunsch score of the one-letter sequences $[a]$ and $[b]$ is
$\max(\sigma(a, b), g + g)$: the better of matching $a$ with $b$ and gapping both. -/
theorem nwScore_singleton_singleton (a b : α) :
    nwScore σ gap [a] [b] = max (σ a b) (gap + gap) := by
  have e := nwScore_eq σ gap a b [] []
  have h00 : nwScore σ gap [] [] = 0 := rfl
  rw [e]
  simp [h00, nwScore_nil_left, nwScore_nil_right, max_idem]

/-- **Base-case alignment for Hirschberg.** Fix a substitution score $\sigma$ assigning an
integer to each pair of letters and an integer gap score $g$, and write a column as a pair
whose missing entry, a gap, is marked $\bot$. The base-case alignment of sequences $x$ and $y$
is the empty alignment if both are empty; the single column $(\bot, b)$ if $x$ is empty and
$y = [b]$; the single column $(a, \bot)$ if $x = [a]$ and $y$ is empty; if $x = [a]$ and
$y = [b]$, it is the single column $(a, b)$ when $\sigma(a, b) \ge 2g$ and the two columns
$(a, \bot)$, $(\bot, b)$ otherwise; and it is the empty alignment when $x$ or $y$ has length
at least $2$. -/
def smallAlign : List α → List α → Alignment α
  | [], [] => []
  | [], [b] => [(none, some b)]
  | [a], [] => [(some a, none)]
  | [a], [b] => if σ a b ≥ 2 * gap then [(some a, some b)]
      else [(some a, none), (none, some b)]
  | _, _ => []

/-- **The base-case alignment is valid.** For every substitution score $\sigma$ assigning an
integer to each pair of letters, integer gap score $g$ and sequences $x$, $y$ with
$|x| \le 1$ and $|y| \le 1$, the base-case alignment of $x$ and $y$ is a valid alignment of
$x$ and $y$. -/
theorem isAlignment_smallAlign (xs ys : List α) (hxs : xs.length ≤ 1)
    (hys : ys.length ≤ 1) : IsAlignment (smallAlign σ gap xs ys) xs ys := by
  cases xs with
  | nil =>
      cases ys with
      | nil =>
          show IsAlignment [] [] []
          exact ⟨by simp, rfl, rfl⟩
      | cons b ys' =>
          cases ys' with
          | nil =>
              show IsAlignment [(none, some b)] [] [b]
              exact ⟨by simp, rfl, rfl⟩
          | cons b' ys'' =>
              exfalso
              simp only [List.length_cons] at hys
              omega
  | cons a xs' =>
      cases xs' with
      | nil =>
          cases ys with
          | nil =>
              show IsAlignment [(some a, none)] [a] []
              exact ⟨by simp, rfl, rfl⟩
          | cons b ys' =>
              cases ys' with
              | nil =>
                  by_cases h : σ a b ≥ 2 * gap
                  · have esmall : smallAlign σ gap [a] [b] = [(some a, some b)] := by
                      simp only [smallAlign, ite_eq_left h]
                    rw [esmall]
                    exact ⟨by simp, rfl, rfl⟩
                  · have esmall : smallAlign σ gap [a] [b]
                        = [(some a, none), (none, some b)] := by
                      simp only [smallAlign, ite_eq_right h]
                    rw [esmall]
                    exact ⟨by simp, rfl, rfl⟩
              | cons b' ys'' =>
                  exfalso
                  simp only [List.length_cons] at hys
                  omega
      | cons a' xs'' =>
          exfalso
          simp only [List.length_cons] at hxs
          omega

/-- **The base-case alignment is optimal.** Fix a type $\alpha$, a substitution score
$\sigma : \alpha \to \alpha \to \mathbb{Z}$ and a gap score $g \in \mathbb{Z}$. For all lists
$xs$, $ys$ over $\alpha$ with $|xs| \le 1$ and $|ys| \le 1$, the alignment score of the
base-case alignment of $xs$ and $ys$ equals the Needleman–Wunsch score of $xs$ and $ys$. -/
theorem alignmentScore_smallAlign_eq_nwScore (xs ys : List α)
    (hxs : xs.length ≤ 1) (hys : ys.length ≤ 1) :
    alignmentScore σ gap (smallAlign σ gap xs ys) = nwScore σ gap xs ys := by
  cases xs with
  | nil =>
      cases ys with
      | nil => rfl
      | cons b ys' =>
          cases ys' with
          | nil => simp [smallAlign, alignmentScore, columnScore, nwScore_nil_left]
          | cons b' ys'' =>
              exfalso
              simp only [List.length_cons] at hys
              omega
  | cons a xs' =>
      cases xs' with
      | nil =>
          cases ys with
          | nil => simp [smallAlign, alignmentScore, columnScore, nwScore_nil_right]
          | cons b ys' =>
              cases ys' with
              | nil =>
                  by_cases h : σ a b ≥ 2 * gap
                  · have hmax : max (σ a b) (gap + gap) = σ a b :=
                      max_eq_left (by
                        have h2 : (2 : ℤ) * gap = gap + gap := by ring
                        linarith)
                    rw [nwScore_singleton_singleton, hmax]
                    have esmall : smallAlign σ gap [a] [b] = [(some a, some b)] := by
                      simp only [smallAlign, ite_eq_left h]
                    rw [esmall]
                    simp [alignmentScore, columnScore]
                  · have hmax : max (σ a b) (gap + gap) = gap + gap :=
                      max_eq_right (by
                        have h2 : (2 : ℤ) * gap = gap + gap := by ring
                        have hlt : σ a b < 2 * gap := lt_of_not_ge h
                        linarith)
                    rw [nwScore_singleton_singleton, hmax]
                    have esmall : smallAlign σ gap [a] [b]
                        = [(some a, none), (none, some b)] := by
                      simp only [smallAlign, ite_eq_right h]
                    rw [esmall]
                    simp [alignmentScore, columnScore]
              | cons b' ys'' =>
                  exfalso
                  simp only [List.length_cons] at hys
                  omega
      | cons a' xs'' =>
          exfalso
          simp only [List.length_cons] at hxs
          omega

/-- **Hirschberg reconstruction with fuel.** Fix a substitution score $\sigma$ assigning an
integer to each pair of letters and an integer gap score $g$, and write $\mathrm{NW}$ for the
Needleman–Wunsch score. For a sequence $s$, write $s_{<j}$ for its first $j$ letters and
$s_{\ge j}$ for the remaining letters. The Hirschberg reconstruction of sequences $x$ and $y$
with fuel $n$ is the alignment defined by recursion on $n$. With fuel $0$ it is the empty
alignment. With fuel $n + 1$: if $|x| \le 1$ and $|y| \le 1$, it is the base-case alignment
of $x$ and $y$; otherwise, if $|y| \ge |x|$, let $m = \lfloor |y|/2 \rfloor$ and let $k$ be
the first index $j \in \{0, \dots, |x|\}$ that maximizes
$\mathrm{NW}(x_{<j}, y_{<m}) + \mathrm{NW}(x_{\ge j}, y_{\ge m})$, and the result is the
concatenation of the reconstructions with fuel $n$ of $x_{<k}$ and $y_{<m}$ and of $x_{\ge k}$
and $y_{\ge m}$; otherwise, let $m = \lfloor |x|/2 \rfloor$ and let $k$ be the first index
$j \in \{0, \dots, |y|\}$ that maximizes
$\mathrm{NW}(x_{<m}, y_{<j}) + \mathrm{NW}(x_{\ge m}, y_{\ge j})$, and the result is the
concatenation of the reconstructions with fuel $n$ of $x_{<m}$ and $y_{<k}$ and of $x_{\ge m}$
and $y_{\ge k}$.

Hirschberg's alignment algorithm runs this reconstruction with fuel $|x| + |y|$. -/
def hirschbergAlign : ℕ → List α → List α → Alignment α
  | 0, _, _ => []
  | fuel + 1, xs, ys =>
      if (decide (xs.length ≤ 1) && decide (ys.length ≤ 1)) then
        smallAlign σ gap xs ys
      else if decide (ys.length ≥ xs.length) then
        hirschbergAlign fuel
            (List.take (bestArgmax (fun k => nwScore σ gap (List.take k xs)
              (List.take (ys.length / 2) ys) + nwScore σ gap (List.drop k xs)
              (List.drop (ys.length / 2) ys)) xs.length) xs)
            (List.take (ys.length / 2) ys) ++
        hirschbergAlign fuel
            (List.drop (bestArgmax (fun k => nwScore σ gap (List.take k xs)
              (List.take (ys.length / 2) ys) + nwScore σ gap (List.drop k xs)
              (List.drop (ys.length / 2) ys)) xs.length) xs)
            (List.drop (ys.length / 2) ys)
      else
        hirschbergAlign fuel
            (List.take (xs.length / 2) xs)
            (List.take (bestArgmax (fun k => nwScore σ gap
              (List.take (xs.length / 2) xs) (List.take k ys) + nwScore σ gap
              (List.drop (xs.length / 2) xs) (List.drop k ys)) ys.length) ys) ++
        hirschbergAlign fuel
            (List.drop (xs.length / 2) xs)
            (List.drop (bestArgmax (fun k => nwScore σ gap
              (List.take (xs.length / 2) xs) (List.take k ys) + nwScore σ gap
              (List.drop (xs.length / 2) xs) (List.drop k ys)) ys.length) ys)

/-- **Hirschberg reconstruction on lists of length at most one.** Fix a type $\alpha$, a
substitution score $\sigma : \alpha \to \alpha \to \mathbb{Z}$ and a gap score $g \in \mathbb{Z}$.
For every $n \in \mathbb{N}$ and all lists $xs$, $ys$ over $\alpha$ with $|xs| \le 1$ and
$|ys| \le 1$, the Hirschberg reconstruction of $xs$ and $ys$ with fuel $n + 1$ is the
base-case alignment of $xs$ and $ys$. -/
theorem hirschbergAlign_small (fuel : ℕ) (xs ys : List α)
    (hsmall : xs.length ≤ 1 ∧ ys.length ≤ 1) :
    hirschbergAlign σ gap (fuel + 1) xs ys = smallAlign σ gap xs ys := by
  have hbool : (decide (xs.length ≤ 1) && decide (ys.length ≤ 1)) = true := by
    rw [Bool.and_eq_true]
    exact ⟨decide_eq_true_eq.mpr hsmall.1, decide_eq_true_eq.mpr hsmall.2⟩
  simp only [hirschbergAlign]
  rw [ite_eq_left hbool]

/-- **Hirschberg recursion step splitting the second sequence.** Fix a substitution score
$\sigma$ assigning an integer to each pair of letters and an integer gap score $g$, and write
$\mathrm{NW}$ for the Needleman–Wunsch score. For a sequence $s$, write $s_{<j}$ for its first
$j$ letters and $s_{\ge j}$ for the remaining letters. Let $x$, $y$ be sequences with
$|y| \ge |x|$ that do not both have length at most $1$, let $m = \lfloor |y|/2 \rfloor$, and
let $k$ be the first index $j \in \{0, \dots, |x|\}$ that maximizes
$\mathrm{NW}(x_{<j}, y_{<m}) + \mathrm{NW}(x_{\ge j}, y_{\ge m})$. Then for every natural
number $n$, the Hirschberg reconstruction of $x$ and $y$ with fuel $n + 1$ is the
concatenation of the Hirschberg reconstruction of $x_{<k}$ and $y_{<m}$ with fuel $n$ and the
Hirschberg reconstruction of $x_{\ge k}$ and $y_{\ge m}$ with fuel $n$. -/
theorem hirschbergAlign_split_ys (fuel : ℕ) (xs ys : List α)
    (hsmall : ¬ (xs.length ≤ 1 ∧ ys.length ≤ 1)) (hge : ys.length ≥ xs.length) :
    hirschbergAlign σ gap (fuel + 1) xs ys =
      hirschbergAlign σ gap fuel
          (List.take (bestArgmax (fun k => nwScore σ gap (List.take k xs)
            (List.take (ys.length / 2) ys) + nwScore σ gap (List.drop k xs)
            (List.drop (ys.length / 2) ys)) xs.length) xs)
          (List.take (ys.length / 2) ys) ++
      hirschbergAlign σ gap fuel
          (List.drop (bestArgmax (fun k => nwScore σ gap (List.take k xs)
            (List.take (ys.length / 2) ys) + nwScore σ gap (List.drop k xs)
            (List.drop (ys.length / 2) ys)) xs.length) xs)
          (List.drop (ys.length / 2) ys) := by
  have hbool : ¬ ((decide (xs.length ≤ 1) && decide (ys.length ≤ 1)) = true) := by
    intro hcon
    rw [Bool.and_eq_true] at hcon
    exact hsmall ⟨of_decide_eq_true hcon.1, of_decide_eq_true hcon.2⟩
  have hge_bool : decide (ys.length ≥ xs.length) = true :=
    decide_eq_true_eq.mpr hge
  simp only [hirschbergAlign]
  rw [ite_eq_right hbool, ite_eq_left hge_bool]

/-- **Hirschberg reconstruction splits the longer first list.** Fix a type $\alpha$, a
substitution score $\sigma : \alpha \to \alpha \to \mathbb{Z}$ and a gap score $g \in \mathbb{Z}$.
Write $H_n(u, v)$ for the Hirschberg reconstruction of lists $u$, $v$ with fuel $n$, $S(u, v)$
for their Needleman–Wunsch score, and $u_{<m}$, $u_{\ge m}$ for the first $m$ elements of $u$
and the rest. Let $xs$, $ys$ be lists over $\alpha$ that are not both of length at most $1$,
with $|ys| < |xs|$. Put $h = \lfloor |xs| / 2 \rfloor$ and let $k$ be the least maximizer over
$\{0, \dots, |ys|\}$ of $j \mapsto S(xs_{<h}, ys_{<j}) + S(xs_{\ge h}, ys_{\ge j})$. Then
for every $n \in \mathbb{N}$, $H_{n+1}(xs, ys)$ is the concatenation of
$H_n(xs_{<h}, ys_{<k})$ and $H_n(xs_{\ge h}, ys_{\ge k})$. -/
theorem hirschbergAlign_split_xs (fuel : ℕ) (xs ys : List α)
    (hsmall : ¬ (xs.length ≤ 1 ∧ ys.length ≤ 1))
    (hge : ¬ ys.length ≥ xs.length) :
    hirschbergAlign σ gap (fuel + 1) xs ys =
      hirschbergAlign σ gap fuel
          (List.take (xs.length / 2) xs)
          (List.take (bestArgmax (fun k => nwScore σ gap
            (List.take (xs.length / 2) xs) (List.take k ys) + nwScore σ gap
            (List.drop (xs.length / 2) xs) (List.drop k ys)) ys.length) ys) ++
      hirschbergAlign σ gap fuel
          (List.drop (xs.length / 2) xs)
          (List.drop (bestArgmax (fun k => nwScore σ gap
            (List.take (xs.length / 2) xs) (List.take k ys) + nwScore σ gap
            (List.drop (xs.length / 2) xs) (List.drop k ys)) ys.length) ys) := by
  have hbool : ¬ ((decide (xs.length ≤ 1) && decide (ys.length ≤ 1)) = true) := by
    intro hcon
    rw [Bool.and_eq_true] at hcon
    exact hsmall ⟨of_decide_eq_true hcon.1, of_decide_eq_true hcon.2⟩
  have hge_bool : ¬ (decide (ys.length ≥ xs.length) = true) := by
    intro hcon
    exact hge (of_decide_eq_true hcon)
  simp only [hirschbergAlign]
  rw [ite_eq_right hbool, ite_eq_right hge_bool]

/-- **Hirschberg reconstruction with enough fuel is valid.** For every substitution score
$\sigma$ assigning an integer to each pair of letters, integer gap score $g$, natural number
$n$ and sequences $x$, $y$ with $|x| + |y| \le n$, the Hirschberg reconstruction of $x$ and
$y$ with fuel $n$ is a valid alignment of $x$ and $y$. -/
theorem isAlignment_hirschbergAlign : ∀ (fuel : ℕ) (xs ys : List α),
    xs.length + ys.length ≤ fuel →
    IsAlignment (hirschbergAlign σ gap fuel xs ys) xs ys
  | 0, xs, ys, h => by
      have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
      have hy : ys = [] := List.length_eq_zero_iff.mp (by omega)
      subst hx
      subst hy
      show IsAlignment [] [] []
      exact ⟨by simp, rfl, rfl⟩
  | fuel + 1, xs, ys, h => by
      by_cases hsmall : xs.length ≤ 1 ∧ ys.length ≤ 1
      · rw [hirschbergAlign_small σ gap fuel xs ys hsmall]
        exact isAlignment_smallAlign σ gap xs ys hsmall.1 hsmall.2
      · by_cases hge : ys.length ≥ xs.length
        · rw [hirschbergAlign_split_ys σ gap fuel xs ys hsmall hge]
          set mid := ys.length / 2 with hmid
          set k := bestArgmax (fun k => nwScore σ gap (List.take k xs)
            (List.take mid ys) + nwScore σ gap (List.drop k xs)
            (List.drop mid ys)) xs.length with hk_def
          have hys2 : 2 ≤ ys.length := by omega
          have hmid_bounds : 1 ≤ mid ∧ mid < ys.length := by omega
          have hk_le : k ≤ xs.length := bestArgmax_le _ _
          have htake1 : (List.take k xs).length = k := by
            rw [List.length_take]; omega
          have htake2 : (List.take mid ys).length = mid := by
            rw [List.length_take]; omega
          have hdrop1 : (List.drop k xs).length = xs.length - k := by simp
          have hdrop2 : (List.drop mid ys).length = ys.length - mid := by simp
          have ih1 := isAlignment_hirschbergAlign fuel (List.take k xs)
            (List.take mid ys) (by omega)
          have ih2 := isAlignment_hirschbergAlign fuel (List.drop k xs)
            (List.drop mid ys) (by omega)
          have happ := isAlignment_append ih1 ih2
          rwa [List.take_append_drop, List.take_append_drop] at happ
        · rw [hirschbergAlign_split_xs σ gap fuel xs ys hsmall hge]
          set mid := xs.length / 2 with hmid
          set k := bestArgmax (fun k => nwScore σ gap (List.take mid xs)
            (List.take k ys) + nwScore σ gap (List.drop mid xs)
            (List.drop k ys)) ys.length with hk_def
          have hxs2 : 2 ≤ xs.length := by omega
          have hmid_bounds : 1 ≤ mid ∧ mid < xs.length := by omega
          have hk_le : k ≤ ys.length := bestArgmax_le _ _
          have htake1 : (List.take mid xs).length = mid := by
            rw [List.length_take]; omega
          have htake2 : (List.take k ys).length = k := by
            rw [List.length_take]; omega
          have hdrop1 : (List.drop mid xs).length = xs.length - mid := by simp
          have hdrop2 : (List.drop k ys).length = ys.length - k := by simp
          have ih1 := isAlignment_hirschbergAlign fuel (List.take mid xs)
            (List.take k ys) (by omega)
          have ih2 := isAlignment_hirschbergAlign fuel (List.drop mid xs)
            (List.drop k ys) (by omega)
          have happ := isAlignment_append ih1 ih2
          rwa [List.take_append_drop, List.take_append_drop] at happ

/-- **Hirschberg reconstruction with enough fuel attains the optimum.** Fix a type $\alpha$, a
substitution score $\sigma : \alpha \to \alpha \to \mathbb{Z}$ and a gap score $g \in \mathbb{Z}$.
For every fuel $n \in \mathbb{N}$ and all lists $xs$, $ys$ over $\alpha$ with
$|xs| + |ys| \le n$, the alignment score of the Hirschberg reconstruction of $xs$ and $ys$ with
fuel $n$ equals the Needleman–Wunsch score of $xs$ and $ys$. -/
theorem alignmentScore_hirschbergAlign : ∀ (fuel : ℕ) (xs ys : List α),
    xs.length + ys.length ≤ fuel →
    alignmentScore σ gap (hirschbergAlign σ gap fuel xs ys) = nwScore σ gap xs ys
  | 0, xs, ys, h => by
      have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
      have hy : ys = [] := List.length_eq_zero_iff.mp (by omega)
      subst hx
      subst hy
      rfl
  | fuel + 1, xs, ys, h => by
      by_cases hsmall : xs.length ≤ 1 ∧ ys.length ≤ 1
      · rw [hirschbergAlign_small σ gap fuel xs ys hsmall]
        exact alignmentScore_smallAlign_eq_nwScore σ gap xs ys hsmall.1 hsmall.2
      · by_cases hge : ys.length ≥ xs.length
        · rw [hirschbergAlign_split_ys σ gap fuel xs ys hsmall hge]
          set mid := ys.length / 2 with hmid
          set k := bestArgmax (fun k => nwScore σ gap (List.take k xs)
            (List.take mid ys) + nwScore σ gap (List.drop k xs)
            (List.drop mid ys)) xs.length with hk_def
          have hys2 : 2 ≤ ys.length := by omega
          have hmid_bounds : 1 ≤ mid ∧ mid < ys.length := by omega
          have hk_le : k ≤ xs.length := bestArgmax_le _ _
          have htake1 : (List.take k xs).length = k := by
            rw [List.length_take]; omega
          have htake2 : (List.take mid ys).length = mid := by
            rw [List.length_take]; omega
          have hdrop1 : (List.drop k xs).length = xs.length - k := by simp
          have hdrop2 : (List.drop mid ys).length = ys.length - mid := by simp
          have ih1 := alignmentScore_hirschbergAlign fuel (List.take k xs)
            (List.take mid ys) (by omega)
          have ih2 := alignmentScore_hirschbergAlign fuel (List.drop k xs)
            (List.drop mid ys) (by omega)
          rw [alignmentScore_append, ih1, ih2]
          exact nwScore_eq_bestSplit_ys σ gap xs ys
            (by omega : mid ≤ ys.length)
        · rw [hirschbergAlign_split_xs σ gap fuel xs ys hsmall hge]
          set mid := xs.length / 2 with hmid
          set k := bestArgmax (fun k => nwScore σ gap (List.take mid xs)
            (List.take k ys) + nwScore σ gap (List.drop mid xs)
            (List.drop k ys)) ys.length with hk_def
          have hxs2 : 2 ≤ xs.length := by omega
          have hmid_bounds : 1 ≤ mid ∧ mid < xs.length := by omega
          have hk_le : k ≤ ys.length := bestArgmax_le _ _
          have htake1 : (List.take mid xs).length = mid := by
            rw [List.length_take]; omega
          have htake2 : (List.take k ys).length = k := by
            rw [List.length_take]; omega
          have hdrop1 : (List.drop mid xs).length = xs.length - mid := by simp
          have hdrop2 : (List.drop k ys).length = ys.length - k := by simp
          have ih1 := alignmentScore_hirschbergAlign fuel (List.take mid xs)
            (List.take k ys) (by omega)
          have ih2 := alignmentScore_hirschbergAlign fuel (List.drop mid xs)
            (List.drop k ys) (by omega)
          rw [alignmentScore_append, ih1, ih2]
          exact nwScore_eq_bestSplit_xs σ gap xs ys
            (by omega : mid ≤ xs.length)

/-- **Hirschberg's alignment algorithm.** Fix a substitution score $\sigma$ assigning an integer
to each pair of letters and an integer gap score $g$. The Hirschberg alignment of sequences $x$
and $y$ is the Hirschberg reconstruction of $x$ and $y$ with fuel $|x| + |y|$. -/
def hirschberg (xs ys : List α) : Alignment α :=
  hirschbergAlign σ gap (xs.length + ys.length) xs ys

/-- **Hirschberg reconstruction is valid.** For every substitution score $\sigma$ assigning an
integer to each pair of letters, integer gap score $g$ and sequences $x$, $y$, the Hirschberg
alignment of $x$ and $y$ is a valid alignment of $x$ and $y$. -/
theorem isAlignment_hirschberg (xs ys : List α) :
    IsAlignment (hirschberg σ gap xs ys) xs ys :=
  isAlignment_hirschbergAlign σ gap _ xs ys le_rfl

/-- **Hirschberg reconstruction attains the Needleman–Wunsch optimum.** Fix a type $\alpha$, a
substitution score $\sigma : \alpha \to \alpha \to \mathbb{Z}$ and a gap score $g \in \mathbb{Z}$.
For all lists $xs$, $ys$ over $\alpha$, the alignment score of the Hirschberg alignment of $xs$
and $ys$ equals the Needleman–Wunsch score of $xs$ and $ys$. -/
theorem alignmentScore_hirschberg (xs ys : List α) :
    alignmentScore σ gap (hirschberg σ gap xs ys) = nwScore σ gap xs ys :=
  alignmentScore_hirschbergAlign σ gap _ xs ys le_rfl

end Hirschberg

end Cslib.Algorithms.Lean
