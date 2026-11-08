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

/-- The argmax of `f` over `0, …, n`, via the standard `List.argmax` API:
the argmax of `f` on `List.range (n + 1)`, defaulting to `0` (the range is
never empty, so the default is never used). -/
def bestArgmax (f : ℕ → ℤ) (n : ℕ) : ℕ :=
  ((List.range (n + 1)).argmax f).getD 0

/-- The argmax lies in `0, …, n`. -/
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

/-- Every value is at most the argmax value. -/
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

/-- Any split of `ys` scores at most the optimum: concatenate optimal halves. -/
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

/-- Any split of `xs` scores at most the optimum. -/
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

/-- Some split of `ys` attains the optimum: split an optimal alignment. -/
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

/-- Some split of `xs` attains the optimum. -/
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

/-- The argmax split of `ys` attains the optimum. -/
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

/-- The argmax split of `xs` attains the optimum. -/
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


/-- The optimal alignment of two singletons: match, or two gaps. -/
theorem nwScore_singleton_singleton (a b : α) :
    nwScore σ gap [a] [b] = max (σ a b) (gap + gap) := by
  have e := nwScore_eq σ gap a b [] []
  have h00 : nwScore σ gap [] [] = 0 := rfl
  rw [e]
  simp [h00, nwScore_nil_left, nwScore_nil_right, max_idem]

/-- The `≤ 1 × ≤ 1` base case: match singletons, or gap them. -/
def smallAlign : List α → List α → Alignment α
  | [], [] => []
  | [], [b] => [(none, some b)]
  | [a], [] => [(some a, none)]
  | [a], [b] => if σ a b ≥ 2 * gap then [(some a, some b)]
      else [(some a, none), (none, some b)]
  | _, _ => []

/-- The base case is valid. -/
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

/-- The base case attains the optimum. -/
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

/-- Hirschberg reconstruction: split the longer sequence in half, pick the
argmax split of the other sequence, and recurse on the two halves. The fuel
is the total length. -/
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

/-- The base-case unfolding. -/
theorem hirschbergAlign_small (fuel : ℕ) (xs ys : List α)
    (hsmall : xs.length ≤ 1 ∧ ys.length ≤ 1) :
    hirschbergAlign σ gap (fuel + 1) xs ys = smallAlign σ gap xs ys := by
  have hbool : (decide (xs.length ≤ 1) && decide (ys.length ≤ 1)) = true := by
    rw [Bool.and_eq_true]
    exact ⟨decide_eq_true_eq.mpr hsmall.1, decide_eq_true_eq.mpr hsmall.2⟩
  simp only [hirschbergAlign]
  rw [ite_eq_left hbool]

/-- The split-`ys` unfolding. -/
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

/-- The split-`xs` unfolding. -/
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

/-- Hirschberg reconstruction returns a valid alignment. -/
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

/-- Hirschberg reconstruction attains the optimum. -/
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

/-- The Hirschberg alignment: divide-and-conquer reconstruction at full fuel. -/
def hirschberg (xs ys : List α) : Alignment α :=
  hirschbergAlign σ gap (xs.length + ys.length) xs ys

/-- **Hirschberg reconstruction is valid.** -/
theorem isAlignment_hirschberg (xs ys : List α) :
    IsAlignment (hirschberg σ gap xs ys) xs ys :=
  isAlignment_hirschbergAlign σ gap _ xs ys le_rfl

/-- **Hirschberg reconstruction attains the Needleman–Wunsch optimum.** -/
theorem alignmentScore_hirschberg (xs ys : List α) :
    alignmentScore σ gap (hirschberg σ gap xs ys) = nwScore σ gap xs ys :=
  alignmentScore_hirschbergAlign σ gap _ xs ys le_rfl

end Hirschberg

end Cslib.Algorithms.Lean
