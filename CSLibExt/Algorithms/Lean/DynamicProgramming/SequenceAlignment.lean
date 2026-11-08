/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.List.Infix
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Pairwise sequence alignment: Needleman–Wunsch and Smith–Waterman

Pairwise alignment (Needleman and Wunsch, *A general method applicable to the search for
similarities in the amino acid sequence of two proteins*, J. Mol. Biol. 1970; Smith and
Waterman, *Identification of common molecular subsequences*, J. Mol. Biol. 1981; Durbin et
al., *Biological Sequence Analysis*, Cambridge, 1998) scores an alignment of two sequences
`xs`, `ys` by a substitution score `σ` per matched pair of letters and a gap score `gap` per
gap column. An alignment is a list of columns `(Option α × Option α)` with no `(none, none)`
column whose rows filter to `xs` and `ys`.

Main results:

* `nwScore_eq`: **the Needleman–Wunsch recurrence**: the optimal global alignment score
  satisfies the standard dynamic programming recurrence.
* `alignmentScore_le_nwScore`, `exists_alignmentScore_eq_nwScore`: **Needleman–Wunsch is
  optimal**: every alignment scores at most `nwScore`, and some alignment attains it.
* `swCellScore_eq`: **the terminal-cell recurrence**: the terminal Smith–Waterman cell,
  defined by front-peeling on reversed lists, satisfies the standard end-peeling
  recurrence.
* `swCellScore_eq_suffixMax`: **the terminal cell is a suffix maximum** (for
  `gap ≤ 0`): it is the maximum `nwScore` over all pairs of suffixes (`swCellScore` is
  `0` when no positive local alignment exists, since the empty alignment scores `0`).
* `swScore`: **the Smith–Waterman score** is the maximum terminal-cell score over all pairs
  of prefixes, i.e. the optimal local alignment score for `gap ≤ 0`
  (`localScore_eq_swScore` identifies it with the maximum `nwScore` over all pairs
  of infixes).

The terminal cell is defined by front-peeling on reversed lists, so its defining
recurrence peels the *last* elements of the original lists; that is what makes the
last-column argument in `swCellScore_eq_suffixMax` work. The maximum over infixes is stated
through `localScore`, and the cell recurrence through `swCellScore_eq`.

Cost model: `nwScore` and `swCellScore` are exponential-time *specifications*, not
memoized dynamic-programming tables: each unfolds three overlapping subproblems without
sharing, so naive evaluation follows exponentially many paths. They are the right
objects for proving the recurrences and the optimality / suffix-max characterizations;
a tabulated `O(|xs| * |ys|)` implementation proved equal to them is future work.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u

variable {α : Type u}

/-- An alignment of two sequences is a list of columns, each pairing an optional element
of the first sequence with an optional element of the second. -/
abbrev Alignment (α : Type*) := List (Option α × Option α)

/-- An alignment is valid for `xs`, `ys` when it has no `(none, none)` column and its rows
filter to `xs` and `ys`. -/
def IsAlignment (A : Alignment α) (xs ys : List α) : Prop :=
  (∀ c ∈ A, c ≠ (none, none)) ∧ A.filterMap Prod.fst = xs ∧ A.filterMap Prod.snd = ys

/-- The score of one alignment column. -/
def columnScore (σ : α → α → ℤ) (gap : ℤ) : Option α × Option α → ℤ
  | (some a, some b) => σ a b
  | (some _, none) => gap
  | (none, some _) => gap
  | (none, none) => 0

/-- The score of an alignment: the sum of its column scores. -/
def alignmentScore (σ : α → α → ℤ) (gap : ℤ) (A : Alignment α) : ℤ :=
  (A.map (columnScore σ gap)).sum

theorem alignmentScore_nil (σ : α → α → ℤ) (gap : ℤ) : alignmentScore σ gap [] = 0 := rfl

theorem alignmentScore_append (σ : α → α → ℤ) (gap : ℤ) (A B : Alignment α) :
    alignmentScore σ gap (A ++ B) = alignmentScore σ gap A + alignmentScore σ gap B := by
  simp [alignmentScore, List.map_append, List.sum_append]

/-- Appending two valid alignments gives a valid alignment of the concatenated
sequences. -/
theorem isAlignment_append {A1 A2 : Alignment α} {xs1 ys1 xs2 ys2 : List α}
    (h1 : IsAlignment A1 xs1 ys1) (h2 : IsAlignment A2 xs2 ys2) :
    IsAlignment (A1 ++ A2) (xs1 ++ xs2) (ys1 ++ ys2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    rw [List.mem_append] at hc
    rcases hc with hc | hc <;> [exact h1.1 c hc; exact h2.1 c hc]
  · rw [List.filterMap_append, h1.2.1, h2.2.1]
  · rw [List.filterMap_append, h1.2.2, h2.2.2]

theorem alignmentScore_singleton (σ : α → α → ℤ) (gap : ℤ) (c : Option α × Option α) :
    alignmentScore σ gap [c] = columnScore σ gap c := by
  simp [alignmentScore]

section NeedlemanWunsch

variable (σ : α → α → ℤ) (gap : ℤ)

/-- The Needleman–Wunsch score, by fuel recursion on the total length. The fuel is the
sum of the two lengths; the recursion below only calls itself on strictly shorter pairs.
Exponential-time specification, not a memoized table (see the module cost model).
Implementation detail: use `nwScore`, not this worker, which returns `0` on
insufficient fuel. -/
def nwScoreAux : ℕ → List α → List α → ℤ
  | 0, _, _ => 0
  | _ + 1, [], [] => 0
  | _ + 1, [], b :: ys => gap * ((b :: ys).length : ℤ)
  | _ + 1, a :: xs, [] => gap * ((a :: xs).length : ℤ)
  | n + 1, a :: xs, b :: ys =>
      max (max (nwScoreAux n xs ys + σ a b) (nwScoreAux n xs (b :: ys) + gap))
        (nwScoreAux n (a :: xs) ys + gap)

/-- The optimal global alignment score (Needleman–Wunsch). -/
def nwScore (xs ys : List α) : ℤ := nwScoreAux σ gap (xs.length + ys.length) xs ys

/-- Extra fuel does not change the score. -/
private theorem nwScoreAux_succ_of_le : ∀ (m : ℕ) (xs ys : List α), xs.length + ys.length ≤ m →
    nwScoreAux σ gap m xs ys = nwScoreAux σ gap (m + 1) xs ys
  | 0, xs, ys, h => by
      have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
      have hy : ys = [] := List.length_eq_zero_iff.mp (by omega)
      subst hx
      subst hy
      rfl
  | m + 1, [], [], _ => rfl
  | m + 1, [], b :: ys, _ => rfl
  | m + 1, a :: xs, [], _ => rfl
  | m + 1, a :: xs, b :: ys, _ => by
      have h1 : (a :: xs).length = xs.length + 1 := rfl
      have h2 : (b :: ys).length = ys.length + 1 := rfl
      simp only [nwScoreAux]
      rw [nwScoreAux_succ_of_le m xs ys (by omega),
        nwScoreAux_succ_of_le m xs (b :: ys) (by omega),
        nwScoreAux_succ_of_le m (a :: xs) ys (by omega)]

/-- The score depends only on the lengths through the fuel bound. -/
private theorem nwScoreAux_eq_of_le (m : ℕ) (xs ys : List α) (h : xs.length + ys.length ≤ m) :
    nwScoreAux σ gap m xs ys = nwScoreAux σ gap (xs.length + ys.length) xs ys := by
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
      rw [← ih, nwScoreAux_succ_of_le σ gap m xs ys hm]

/-- Aligning anything with the empty sequence costs one gap per letter. -/
theorem nwScore_nil_left (ys : List α) : nwScore σ gap [] ys = gap * ys.length := by
  cases ys with
  | nil => simp [nwScore, nwScoreAux]
  | cons b ys =>
      have : nwScoreAux σ gap (0 + (b :: ys).length) [] (b :: ys) =
          gap * ((b :: ys).length : ℤ) := by
        cases h : (b :: ys).length with
        | zero => exact absurd h (by simp)
        | succ k => rw [← h]; rfl
      simpa [nwScore] using this

/-- Aligning anything with the empty sequence costs one gap per letter. -/
theorem nwScore_nil_right (xs : List α) : nwScore σ gap xs [] = gap * xs.length := by
  cases xs with
  | nil => simp [nwScore, nwScoreAux]
  | cons a xs =>
      have : nwScoreAux σ gap ((a :: xs).length + 0) (a :: xs) [] =
          gap * ((a :: xs).length : ℤ) := by
        cases h : (a :: xs).length with
        | zero => exact absurd h (by simp)
        | succ k => rw [← h]; rfl
      simpa [nwScore] using this

/-- **The Needleman–Wunsch recurrence.** -/
theorem nwScore_eq (a b : α) (xs ys : List α) :
    nwScore σ gap (a :: xs) (b :: ys) =
      max (max (nwScore σ gap xs ys + σ a b) (nwScore σ gap xs (b :: ys) + gap))
        (nwScore σ gap (a :: xs) ys + gap) := by
  have h1 : nwScoreAux σ gap ((a :: xs).length + (b :: ys).length) (a :: xs) (b :: ys) =
      max (max (nwScoreAux σ gap (xs.length + ys.length + 1) xs ys + σ a b)
        (nwScoreAux σ gap (xs.length + ys.length + 1) xs (b :: ys) + gap))
        (nwScoreAux σ gap (xs.length + ys.length + 1) (a :: xs) ys + gap) := by
    rw [show (a :: xs).length + (b :: ys).length = (xs.length + ys.length + 1) + 1 by
      simp only [List.length_cons]; omega]
    simp only [nwScoreAux]
  have e1 : nwScoreAux σ gap (xs.length + ys.length + 1) xs ys =
      nwScoreAux σ gap (xs.length + ys.length) xs ys :=
    (nwScoreAux_succ_of_le σ gap (xs.length + ys.length) xs ys le_rfl).symm
  have e2 : nwScoreAux σ gap (xs.length + ys.length + 1) xs (b :: ys) =
      nwScoreAux σ gap (xs.length + (b :: ys).length) xs (b :: ys) := by
    rw [show xs.length + (b :: ys).length = xs.length + ys.length + 1 by
      simp only [List.length_cons]; omega]
  have e3 : nwScoreAux σ gap (xs.length + ys.length + 1) (a :: xs) ys =
      nwScoreAux σ gap ((a :: xs).length + ys.length) (a :: xs) ys := by
    rw [show (a :: xs).length + ys.length = xs.length + ys.length + 1 by
      simp only [List.length_cons]; omega]
  rw [nwScore, nwScore, nwScore, nwScore, h1, e1, e2, e3]

end NeedlemanWunsch

section Alignments

variable (σ : α → α → ℤ) (gap : ℤ)

/-- All alignments of two sequences, by fuel recursion. Implementation detail: use
`alignments`, not this worker, which returns `[]` on insufficient fuel. -/
def alignmentsAux : ℕ → List α → List α → List (Alignment α)
  | 0, _, _ => []
  | _ + 1, [], [] => [[]]
  | n + 1, [], b :: ys => (alignmentsAux n [] ys).map fun A => (none, some b) :: A
  | n + 1, a :: xs, [] => (alignmentsAux n xs []).map fun A => (some a, none) :: A
  | n + 1, a :: xs, b :: ys =>
      (alignmentsAux n xs ys).map (fun A => (some a, some b) :: A) ++
        (alignmentsAux n xs (b :: ys)).map (fun A => (some a, none) :: A) ++
        (alignmentsAux n (a :: xs) ys).map (fun A => (none, some b) :: A)

/-- All alignments of two sequences. -/
def alignments (xs ys : List α) : List (Alignment α) :=
  alignmentsAux (xs.length + ys.length + 1) xs ys

/-- Extra fuel does not change the alignment list. -/
private theorem alignmentsAux_succ_of_le : ∀ (m : ℕ) (xs ys : List α), xs.length + ys.length < m →
    alignmentsAux m xs ys = alignmentsAux (m + 1) xs ys
  | 0, _, _, h => by exact absurd h (Nat.not_lt_zero _)
  | m + 1, [], [], _ => rfl
  | m + 1, [], b :: ys, _ => by
      have h2 : (b :: ys).length = ys.length + 1 := rfl
      simp only [alignmentsAux]
      rw [alignmentsAux_succ_of_le m [] ys (by omega)]
  | m + 1, a :: xs, [], _ => by
      have h1 : (a :: xs).length = xs.length + 1 := rfl
      simp only [alignmentsAux]
      rw [alignmentsAux_succ_of_le m xs [] (by omega)]
  | m + 1, a :: xs, b :: ys, _ => by
      have h1 : (a :: xs).length = xs.length + 1 := rfl
      have h2 : (b :: ys).length = ys.length + 1 := rfl
      simp only [alignmentsAux]
      rw [alignmentsAux_succ_of_le m xs ys (by omega),
        alignmentsAux_succ_of_le m xs (b :: ys) (by omega),
        alignmentsAux_succ_of_le m (a :: xs) ys (by omega)]

/-- The alignment list depends only on the lengths through the fuel bound. -/
private theorem alignmentsAux_eq_of_le (m : ℕ) (xs ys : List α) (h : xs.length +
    ys.length + 1 ≤ m) :
    alignmentsAux m xs ys = alignmentsAux (xs.length + ys.length + 1) xs ys := by
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
      rw [← ih, alignmentsAux_succ_of_le m xs ys (by omega)]

/-- Auxiliary fuel-indexed form of `mem_alignments`. -/
private theorem mem_alignments_aux : ∀ (n : ℕ) (xs ys : List α), xs.length + ys.length ≤ n →
    ∀ A : Alignment α, A ∈ alignmentsAux (n + 1) xs ys ↔ IsAlignment A xs ys := by
  intro n
  induction n with
  | zero =>
      intro xs ys hle A
      have hx : xs = [] := by
        rcases xs with _ | ⟨a, xs⟩ <;> simp_all
      have hy : ys = [] := by
        rcases ys with _ | ⟨b, ys⟩ <;> simp_all
      subst hx; subst hy
      simp only [alignmentsAux, List.mem_singleton]
      constructor
      · rintro rfl
        refine ⟨fun c hc => ?_, by simp, by simp⟩
        simp at hc
      · intro h
        have : A = [] := by
          rcases A with _ | ⟨c, A⟩
          · rfl
          · exfalso
            obtain ⟨h1, h2, h3⟩ := h
            have hc := h1 c (by simp)
            have e1 : (c :: A).filterMap Prod.fst = [] := by simpa using h2
            have e2 : (c :: A).filterMap Prod.snd = [] := by simpa using h3
            rw [List.filterMap_cons] at e1 e2
            cases hc1 : c.1 with
            | none =>
                cases hc2 : c.2 with
                | none => exact hc (Prod.ext hc1 hc2)
                | some b => simp [hc2] at e2
            | some a => simp [hc1] at e1
        exact this
  | succ n ih =>
      intro xs ys hle A
      cases xs with
      | nil =>
          cases ys with
          | nil =>
              simp only [alignmentsAux, List.mem_singleton]
              constructor
              · rintro rfl
                refine ⟨fun c hc => ?_, by simp, by simp⟩
                simp at hc
              · intro h
                have : A = [] := by
                  rcases A with _ | ⟨c, A⟩
                  · rfl
                  · exfalso
                    obtain ⟨h1, h2, h3⟩ := h
                    have hc := h1 c (by simp)
                    have e1 : (c :: A).filterMap Prod.fst = [] := by simpa using h2
                    have e2 : (c :: A).filterMap Prod.snd = [] := by simpa using h3
                    rw [List.filterMap_cons] at e1 e2
                    cases hc1 : c.1 with
                    | none =>
                        cases hc2 : c.2 with
                        | none => exact hc (Prod.ext hc1 hc2)
                        | some b => simp [hc2] at e2
                    | some a => simp [hc1] at e1
                exact this
          | cons b ys =>
              have hmem : A ∈ alignmentsAux ((n + 1) + 1) [] (b :: ys) ↔
                  ∃ A', A' ∈ alignmentsAux (n + 1) [] ys ∧ A = (none, some b) :: A' := by
                simp only [alignmentsAux, List.mem_map]
                constructor
                · rintro ⟨A', hA', rfl⟩
                  exact ⟨A', hA', rfl⟩
                · rintro ⟨A', hA', rfl⟩
                  exact ⟨A', hA', rfl⟩
              rw [hmem]
              constructor
              · rintro ⟨A', hA', rfl⟩
                obtain ⟨h1, h2,
                  h3⟩ := (ih [] ys (by simp only [List.length_cons] at hle ⊢; omega) A').mp hA'
                refine ⟨?_, ?_, ?_⟩
                · intro c hc
                  rcases List.mem_cons.mp hc with rfl | hc
                  · simp
                  · exact h1 c hc
                · simp [h2]
                · simp [h3]
              · intro h
                obtain ⟨h1, h2, h3⟩ := h
                rcases A with _ | ⟨c, A'⟩
                · simp at h3
                · have hc := h1 c (by simp)
                  have e1 : (c :: A').filterMap Prod.fst = [] := by simpa using h2
                  have e2 : (c :: A').filterMap Prod.snd = b :: ys := by simpa using h3
                  rw [List.filterMap_cons] at e1 e2
                  cases hc1 : c.1 with
                  | none =>
                      cases hc2 : c.2 with
                      | none => exact absurd (Prod.ext hc1 hc2) hc
                      | some b' =>
                          have hb : b' = b := by
                            have := e2
                            rw [hc2] at this
                            simp at this
                            exact this.1
                          subst hb
                          have hc_eq : c = (none, some b') := Prod.ext hc1 hc2
                          refine ⟨A', ?_, by rw [hc_eq]⟩
                          apply (ih [] ys (by simp only [List.length_cons] at hle ⊢; omega) A').mpr
                          refine ⟨?_, ?_, ?_⟩
                          · intro d hd
                            exact h1 d (by simp [hd])
                          · rw [hc1] at e1
                            exact e1
                          · have : A'.filterMap Prod.snd = ys := by
                              have h := e2
                              rw [hc2] at h
                              simpa using h
                            exact this
                  | some a => simp [hc1] at e1
      | cons a xs =>
          cases ys with
          | nil =>
              have hmem : A ∈ alignmentsAux ((n + 1) + 1) (a :: xs) [] ↔
                  ∃ A', A' ∈ alignmentsAux (n + 1) xs [] ∧ A = (some a, none) :: A' := by
                simp only [alignmentsAux, List.mem_map]
                constructor
                · rintro ⟨A', hA', rfl⟩
                  exact ⟨A', hA', rfl⟩
                · rintro ⟨A', hA', rfl⟩
                  exact ⟨A', hA', rfl⟩
              rw [hmem]
              constructor
              · rintro ⟨A', hA', rfl⟩
                obtain ⟨h1, h2,
                  h3⟩ := (ih xs [] (by simp only [List.length_cons] at hle ⊢; omega) A').mp hA'
                refine ⟨?_, ?_, ?_⟩
                · intro c hc
                  rcases List.mem_cons.mp hc with rfl | hc
                  · simp
                  · exact h1 c hc
                · simp [h2]
                · simp [h3]
              · intro h
                obtain ⟨h1, h2, h3⟩ := h
                rcases A with _ | ⟨c, A'⟩
                · simp at h2
                · have hc := h1 c (by simp)
                  have e1 : (c :: A').filterMap Prod.fst = a :: xs := by simpa using h2
                  have e2 : (c :: A').filterMap Prod.snd = [] := by simpa using h3
                  rw [List.filterMap_cons] at e1 e2
                  cases hc1 : c.1 with
                  | none =>
                      cases hc2 : c.2 with
                      | none => exact absurd (Prod.ext hc1 hc2) hc
                      | some b => simp [hc2] at e2
                  | some a' =>
                      have ha : a' = a := by
                        have := e1
                        rw [hc1] at this
                        simp at this
                        exact this.1
                      subst ha
                      have hc2 : c.2 = none := by
                        cases hc2eq : c.2 with
                        | none => rfl
                        | some b => simp [hc2eq] at e2
                      have hc_eq : c = (some a', none) := Prod.ext hc1 hc2
                      refine ⟨A', ?_, by rw [hc_eq]⟩
                      apply (ih xs [] (by simp only [List.length_cons] at hle ⊢; omega) A').mpr
                      refine ⟨?_, ?_, ?_⟩
                      · intro d hd
                        exact h1 d (by simp [hd])
                      · have : A'.filterMap Prod.fst = xs := by
                          have h := e1
                          rw [hc1] at h
                          simpa using h
                        exact this
                      · rw [hc2] at e2
                        exact e2
          | cons b ys =>
              have hmem : A ∈ alignmentsAux ((n + 1) + 1) (a :: xs) (b :: ys) ↔
                  (∃ A', A' ∈ alignmentsAux (n + 1) xs ys ∧ A = (some a, some b) :: A') ∨
                  (∃ A', A' ∈ alignmentsAux (n + 1) xs (b :: ys) ∧
                    A = (some a, none) :: A') ∨
                  (∃ A', A' ∈ alignmentsAux (n + 1) (a :: xs) ys ∧
                    A = (none, some b) :: A') := by
                simp only [alignmentsAux, List.mem_append, List.mem_map]
                constructor
                · rintro ((⟨A', hA', rfl⟩ | ⟨A', hA', rfl⟩) | ⟨A', hA', rfl⟩)
                  · exact Or.inl ⟨A', hA', rfl⟩
                  · exact Or.inr (Or.inl ⟨A', hA', rfl⟩)
                  · exact Or.inr (Or.inr ⟨A', hA', rfl⟩)
                · rintro (⟨A', hA', rfl⟩ | ⟨A', hA', rfl⟩ | ⟨A', hA', rfl⟩)
                  · exact Or.inl (Or.inl ⟨A', hA', rfl⟩)
                  · exact Or.inl (Or.inr ⟨A', hA', rfl⟩)
                  · exact Or.inr ⟨A', hA', rfl⟩
              rw [hmem]
              constructor
              · rintro (⟨A', hA', rfl⟩ | ⟨A', hA', rfl⟩ | ⟨A', hA', rfl⟩)
                · obtain ⟨h1, h2,
                  h3⟩ := (ih xs ys (by simp only [List.length_cons] at hle ⊢; omega) A').mp hA'
                  refine ⟨?_, ?_, ?_⟩
                  · intro c hc
                    rcases List.mem_cons.mp hc with rfl | hc
                    · simp
                    · exact h1 c hc
                  · simp [h2]
                  · simp [h3]
                · obtain ⟨h1, h2, h3⟩ := (ih xs (b ::
                  ys) (by simp only [List.length_cons] at hle ⊢; omega) A').mp hA'
                  refine ⟨?_, ?_, ?_⟩
                  · intro c hc
                    rcases List.mem_cons.mp hc with rfl | hc
                    · simp
                    · exact h1 c hc
                  · simp [h2]
                  · simp [h3]
                · obtain ⟨h1, h2, h3⟩ := (ih (a ::
                  xs) ys (by simp only [List.length_cons] at hle ⊢; omega) A').mp hA'
                  refine ⟨?_, ?_, ?_⟩
                  · intro c hc
                    rcases List.mem_cons.mp hc with rfl | hc
                    · simp
                    · exact h1 c hc
                  · simp [h2]
                  · simp [h3]
              · intro h
                obtain ⟨h1, h2, h3⟩ := h
                rcases A with _ | ⟨c, A'⟩
                · simp at h2
                · have hc := h1 c (by simp)
                  have e1 : (c :: A').filterMap Prod.fst = a :: xs := by simpa using h2
                  have e2 : (c :: A').filterMap Prod.snd = b :: ys := by simpa using h3
                  rw [List.filterMap_cons] at e1 e2
                  cases hc1 : c.1 with
                  | none =>
                      cases hc2 : c.2 with
                      | none => exact absurd (Prod.ext hc1 hc2) hc
                      | some b' =>
                          have hb : b' = b := by
                            have := e2
                            rw [hc2] at this
                            simp at this
                            exact this.1
                          subst hb
                          have hc_eq : c = (none, some b') := Prod.ext hc1 hc2
                          refine Or.inr (Or.inr ⟨A', ?_, by rw [hc_eq]⟩)
                          apply (ih (a ::
                            xs) ys (by simp only [List.length_cons] at hle ⊢; omega) A').mpr
                          refine ⟨?_, ?_, ?_⟩
                          · intro d hd
                            exact h1 d (by simp [hd])
                          · rw [hc1] at e1
                            exact e1
                          · have : A'.filterMap Prod.snd = ys := by
                              have h := e2
                              rw [hc2] at h
                              simpa using h
                            exact this
                  | some a' =>
                      have ha : a' = a := by
                        have := e1
                        rw [hc1] at this
                        simp at this
                        exact this.1
                      subst ha
                      cases hc2 : c.2 with
                      | none =>
                          have hc_eq : c = (some a', none) := Prod.ext hc1 hc2
                          refine Or.inr (Or.inl ⟨A', ?_, by rw [hc_eq]⟩)
                          apply (ih xs (b ::
                            ys) (by simp only [List.length_cons] at hle ⊢; omega) A').mpr
                          refine ⟨?_, ?_, ?_⟩
                          · intro d hd
                            exact h1 d (by simp [hd])
                          · have : A'.filterMap Prod.fst = xs := by
                              have h := e1
                              rw [hc1] at h
                              simpa using h
                            exact this
                          · rw [hc2] at e2
                            exact e2
                      | some b' =>
                          have hb : b' = b := by
                            have := e2
                            rw [hc2] at this
                            simp at this
                            exact this.1
                          subst hb
                          have hc_eq : c = (some a', some b') := Prod.ext hc1 hc2
                          refine Or.inl ⟨A', ?_, by rw [hc_eq]⟩
                          apply (ih xs ys (by simp only [List.length_cons] at hle ⊢; omega) A').mpr
                          refine ⟨?_, ?_, ?_⟩
                          · intro d hd
                            exact h1 d (by simp [hd])
                          · have : A'.filterMap Prod.fst = xs := by
                              have h := e1
                              rw [hc1] at h
                              simpa using h
                            exact this
                          · have : A'.filterMap Prod.snd = ys := by
                              have h := e2
                              rw [hc2] at h
                              simpa using h
                            exact this

/-- Membership in the alignment list is exactly validity. -/
theorem mem_alignments (xs ys : List α) (A : Alignment α) :
    A ∈ alignments xs ys ↔ IsAlignment A xs ys := by
  unfold alignments
  rw [← alignmentsAux_eq_of_le (xs.length + ys.length + 1) xs ys le_rfl]
  exact mem_alignments_aux (xs.length + ys.length) xs ys le_rfl A

/-- **Needleman–Wunsch is optimal**: every valid alignment scores at most `nwScore`. -/
private theorem alignmentScore_le_nwScore_aux : ∀ (n : ℕ) (xs ys : List α),
    xs.length + ys.length ≤ n → ∀ A : Alignment α, IsAlignment A xs ys →
      alignmentScore σ gap A ≤ nwScore σ gap xs ys := by
  intro n
  induction n with
  | zero =>
      intro xs ys hle A hA
      have hx : xs = [] := by
        rcases xs with _ | ⟨a, xs⟩ <;> simp_all
      have hy : ys = [] := by
        rcases ys with _ | ⟨b, ys⟩ <;> simp_all
      subst hx; subst hy
      obtain ⟨h1, h2, h3⟩ := hA
      have : A = [] := by
        rcases A with _ | ⟨c, A⟩
        · rfl
        · exfalso
          have hc := h1 c (by simp)
          have e1 : (c :: A).filterMap Prod.fst = [] := by simpa using h2
          have e2 : (c :: A).filterMap Prod.snd = [] := by simpa using h3
          rw [List.filterMap_cons] at e1 e2
          cases hc1 : c.1 with
          | none =>
              cases hc2 : c.2 with
              | none => exact hc (Prod.ext hc1 hc2)
              | some b => simp [hc2] at e2
          | some a => simp [hc1] at e1
      rw [this]; simp [alignmentScore, nwScore, nwScoreAux]
  | succ n ih =>
      intro xs ys hle A hA
      cases xs with
      | nil =>
          cases ys with
          | nil =>
              obtain ⟨h1, h2, h3⟩ := hA
              have : A = [] := by
                rcases A with _ | ⟨c, A⟩
                · rfl
                · exfalso
                  have hc := h1 c (by simp)
                  have e1 : (c :: A).filterMap Prod.fst = [] := by simpa using h2
                  have e2 : (c :: A).filterMap Prod.snd = [] := by simpa using h3
                  rw [List.filterMap_cons] at e1 e2
                  cases hc1 : c.1 with
                  | none =>
                      cases hc2 : c.2 with
                      | none => exact hc (Prod.ext hc1 hc2)
                      | some b => simp [hc2] at e2
                  | some a => simp [hc1] at e1
              rw [this]; simp [alignmentScore, nwScore, nwScoreAux]
          | cons b ys =>
              obtain ⟨h1, h2, h3⟩ := hA
              rcases A with _ | ⟨c, A'⟩
              · simp at h3
              · have hc := h1 c (by simp)
                have e1 : (c :: A').filterMap Prod.fst = [] := by simpa using h2
                have e2 : (c :: A').filterMap Prod.snd = b :: ys := by simpa using h3
                rw [List.filterMap_cons] at e1 e2
                cases hc1 : c.1 with
                | none =>
                    cases hc2 : c.2 with
                    | none => exact absurd (Prod.ext hc1 hc2) hc
                    | some b' =>
                        have hb : b' = b := by
                          have := e2
                          rw [hc2] at this
                          simp at this
                          exact this.1
                        subst hb
                        have hc_eq : c = (none, some b') := Prod.ext hc1 hc2
                        rw [hc_eq]
                        have hA' : IsAlignment A' [] ys := by
                          refine ⟨?_, ?_, ?_⟩
                          · intro d hd
                            exact h1 d (by simp [hd])
                          · rw [hc1] at e1
                            exact e1
                          · have : A'.filterMap Prod.snd = ys := by
                              have h := e2
                              rw [hc2] at h
                              simpa using h
                            exact this
                        have
                          ih' := ih [] ys (by simp only [List.length_cons] at hle ⊢; omega) A' hA'
                        have hscore : alignmentScore σ gap ((none, some b') :: A') =
                            gap + alignmentScore σ gap A' := by
                          simp [alignmentScore, columnScore]
                        rw [hscore]
                        have hrec : nwScore σ gap [] (b' :: ys) =
                            nwScore σ gap [] ys + gap := by
                          have h1 : nwScore σ gap [] (b' :: ys) = gap * ((b' :: ys).length : ℤ) :=
                            nwScore_nil_left σ gap (b' :: ys)
                          have h2 : nwScore σ gap [] ys = gap * (ys.length : ℤ) :=
                            nwScore_nil_left σ gap ys
                          rw [h1, h2]
                          simp
                          ring
                        rw [hrec]
                        linarith
                | some a => simp [hc1] at e1
      | cons a xs =>
          cases ys with
          | nil =>
              obtain ⟨h1, h2, h3⟩ := hA
              rcases A with _ | ⟨c, A'⟩
              · simp at h2
              · have hc := h1 c (by simp)
                have e1 : (c :: A').filterMap Prod.fst = a :: xs := by simpa using h2
                have e2 : (c :: A').filterMap Prod.snd = [] := by simpa using h3
                rw [List.filterMap_cons] at e1 e2
                cases hc1 : c.1 with
                | none =>
                    cases hc2 : c.2 with
                    | none => exact absurd (Prod.ext hc1 hc2) hc
                    | some b => simp [hc2] at e2
                | some a' =>
                    have ha : a' = a := by
                      have := e1
                      rw [hc1] at this
                      simp at this
                      exact this.1
                    subst ha
                    have hc2 : c.2 = none := by
                      cases hc2eq : c.2 with
                      | none => rfl
                      | some b => simp [hc2eq] at e2
                    have hc_eq : c = (some a', none) := Prod.ext hc1 hc2
                    rw [hc_eq]
                    have hA' : IsAlignment A' xs [] := by
                      refine ⟨?_, ?_, ?_⟩
                      · intro d hd
                        exact h1 d (by simp [hd])
                      · have : A'.filterMap Prod.fst = xs := by
                          have h := e1
                          rw [hc1] at h
                          simpa using h
                        exact this
                      · rw [hc2] at e2
                        exact e2
                    have ih' := ih xs [] (by simp only [List.length_cons] at hle ⊢; omega) A' hA'
                    have hscore : alignmentScore σ gap ((some a', none) :: A') =
                        gap + alignmentScore σ gap A' := by
                      simp [alignmentScore, columnScore]
                    rw [hscore]
                    have hrec : nwScore σ gap (a' :: xs) [] =
                        nwScore σ gap xs [] + gap := by
                      have h1 : nwScore σ gap (a' :: xs) [] = gap * ((a' :: xs).length : ℤ) :=
                        nwScore_nil_right σ gap (a' :: xs)
                      have h2 : nwScore σ gap xs [] = gap * (xs.length : ℤ) :=
                        nwScore_nil_right σ gap xs
                      rw [h1, h2]
                      simp
                      ring
                    rw [hrec]
                    linarith
          | cons b ys =>
              obtain ⟨h1, h2, h3⟩ := hA
              rcases A with _ | ⟨c, A'⟩
              · simp at h2
              · have hc := h1 c (by simp)
                have e1 : (c :: A').filterMap Prod.fst = a :: xs := by simpa using h2
                have e2 : (c :: A').filterMap Prod.snd = b :: ys := by simpa using h3
                rw [List.filterMap_cons] at e1 e2
                cases hc1 : c.1 with
                | none =>
                    cases hc2 : c.2 with
                    | none => exact absurd (Prod.ext hc1 hc2) hc
                    | some b' =>
                        have hb : b' = b := by
                          have := e2
                          rw [hc2] at this
                          simp at this
                          exact this.1
                        subst hb
                        have hc_eq : c = (none, some b') := Prod.ext hc1 hc2
                        rw [hc_eq]
                        have hA' : IsAlignment A' (a :: xs) ys := by
                          refine ⟨?_, ?_, ?_⟩
                          · intro d hd
                            exact h1 d (by simp [hd])
                          · rw [hc1] at e1
                            exact e1
                          · have : A'.filterMap Prod.snd = ys := by
                              have h := e2
                              rw [hc2] at h
                              simpa using h
                            exact this
                        have ih' := ih (a ::
                          xs) ys (by simp only [List.length_cons] at hle ⊢; omega) A' hA'
                        have hscore : alignmentScore σ gap ((none, some b') :: A') =
                            gap + alignmentScore σ gap A' := by
                          simp [alignmentScore, columnScore]
                        rw [nwScore_eq, hscore]
                        exact le_max_of_le_right (by linarith)
                | some a' =>
                    have ha : a' = a := by
                      have := e1
                      rw [hc1] at this
                      simp at this
                      exact this.1
                    subst ha
                    cases hc2 : c.2 with
                    | none =>
                        have hc_eq : c = (some a', none) := Prod.ext hc1 hc2
                        rw [hc_eq]
                        have hA' : IsAlignment A' xs (b :: ys) := by
                          refine ⟨?_, ?_, ?_⟩
                          · intro d hd
                            exact h1 d (by simp [hd])
                          · have : A'.filterMap Prod.fst = xs := by
                              have h := e1
                              rw [hc1] at h
                              simpa using h
                            exact this
                          · rw [hc2] at e2
                            exact e2
                        have ih' := ih xs (b ::
                          ys) (by simp only [List.length_cons] at hle ⊢; omega) A' hA'
                        have hscore : alignmentScore σ gap ((some a', none) :: A') =
                            gap + alignmentScore σ gap A' := by
                          simp [alignmentScore, columnScore]
                        rw [nwScore_eq, hscore]
                        have hle : gap + alignmentScore σ gap A' ≤
                            nwScore σ gap xs (b :: ys) + gap := by linarith [ih']
                        exact le_max_of_le_left (le_max_of_le_right hle)
                    | some b' =>
                        have hb : b' = b := by
                          have := e2
                          rw [hc2] at this
                          simp at this
                          exact this.1
                        subst hb
                        have hc_eq : c = (some a', some b') := Prod.ext hc1 hc2
                        rw [hc_eq]
                        have hA' : IsAlignment A' xs ys := by
                          refine ⟨?_, ?_, ?_⟩
                          · intro d hd
                            exact h1 d (by simp [hd])
                          · have : A'.filterMap Prod.fst = xs := by
                              have h := e1
                              rw [hc1] at h
                              simpa using h
                            exact this
                          · have : A'.filterMap Prod.snd = ys := by
                              have h := e2
                              rw [hc2] at h
                              simpa using h
                            exact this
                        have
                          ih' := ih xs ys (by simp only [List.length_cons] at hle ⊢; omega) A' hA'
                        have hscore : alignmentScore σ gap ((some a', some b') :: A') =
                            σ a' b' + alignmentScore σ gap A' := by
                          simp [alignmentScore, columnScore]
                        rw [nwScore_eq, hscore]
                        exact le_max_of_le_left (le_max_of_le_left (by linarith))

/-- Auxiliary fuel-indexed form of `exists_alignmentScore_eq_nwScore`. -/
private theorem exists_alignmentScore_eq_nwScore_aux : ∀ (n : ℕ) (xs ys : List α),
    xs.length + ys.length ≤ n →
      ∃ A : Alignment α, IsAlignment A xs ys ∧ alignmentScore σ gap A = nwScore σ gap xs ys := by
  intro n
  induction n with
  | zero =>
      intro xs ys hle
      have hx : xs = [] := by
        rcases xs with _ | ⟨a, xs⟩ <;> simp_all
      have hy : ys = [] := by
        rcases ys with _ | ⟨b, ys⟩ <;> simp_all
      subst hx; subst hy
      exact ⟨[], ⟨by simp, rfl, rfl⟩, by simp [alignmentScore, nwScore, nwScoreAux]⟩
  | succ n ih =>
      intro xs ys hle
      cases xs with
      | nil =>
          cases ys with
          | nil => exact ⟨[], ⟨by simp, rfl, rfl⟩, by simp [alignmentScore, nwScore, nwScoreAux]⟩
          | cons b ys =>
              obtain ⟨A', hA', hscore⟩ := ih [] ys (by simp only [List.length_cons] at hle ⊢; omega)
              refine ⟨(none, some b) :: A', ?_, ?_⟩
              · obtain ⟨h1, h2, h3⟩ := hA'
                refine ⟨?_, ?_, ?_⟩
                · intro c hc
                  rcases List.mem_cons.mp hc with rfl | hc
                  · simp
                  · exact h1 c hc
                · simp [h2]
                · simp [h3]
              · have hsc : alignmentScore σ gap ((none, some b) :: A') =
                    gap + alignmentScore σ gap A' := by
                  simp [alignmentScore, columnScore]
                rw [hsc, hscore]
                have hrec : nwScore σ gap [] (b :: ys) = nwScore σ gap [] ys + gap := by
                  have h1 : nwScore σ gap [] (b :: ys) = gap * ((b :: ys).length : ℤ) :=
                    nwScore_nil_left σ gap (b :: ys)
                  have h2 : nwScore σ gap [] ys = gap * (ys.length : ℤ) :=
                    nwScore_nil_left σ gap ys
                  rw [h1, h2]
                  simp
                  ring
                omega
      | cons a xs =>
          cases ys with
          | nil =>
              obtain ⟨A', hA', hscore⟩ := ih xs [] (by simp only [List.length_cons] at hle ⊢; omega)
              refine ⟨(some a, none) :: A', ?_, ?_⟩
              · obtain ⟨h1, h2, h3⟩ := hA'
                refine ⟨?_, ?_, ?_⟩
                · intro c hc
                  rcases List.mem_cons.mp hc with rfl | hc
                  · simp
                  · exact h1 c hc
                · simp [h2]
                · simp [h3]
              · have hsc : alignmentScore σ gap ((some a, none) :: A') =
                    gap + alignmentScore σ gap A' := by
                  simp [alignmentScore, columnScore]
                rw [hsc, hscore]
                have hrec : nwScore σ gap (a :: xs) [] = nwScore σ gap xs [] + gap := by
                  have h1 : nwScore σ gap (a :: xs) [] = gap * ((a :: xs).length : ℤ) :=
                    nwScore_nil_right σ gap (a :: xs)
                  have h2 : nwScore σ gap xs [] = gap * (xs.length : ℤ) :=
                    nwScore_nil_right σ gap xs
                  rw [h1, h2]
                  simp
                  ring
                omega
          | cons b ys =>
              rw [nwScore_eq]
              rcases le_total (nwScore σ gap xs ys + σ a b)
                (max (nwScore σ gap xs (b ::
                  ys) + gap) (nwScore σ gap (a :: xs) ys + gap)) with hcase | hcase
              · rcases le_total (nwScore σ gap xs (b :: ys) + gap)
                  (nwScore σ gap (a :: xs) ys + gap) with hcase2 | hcase2
                · obtain ⟨A', hA',
                  hscore⟩ := ih (a :: xs) ys (by simp only [List.length_cons] at hle ⊢; omega)
                  refine ⟨(none, some b) :: A', ?_, ?_⟩
                  · obtain ⟨h1, h2, h3⟩ := hA'
                    refine ⟨?_, ?_, ?_⟩
                    · intro c hc
                      rcases List.mem_cons.mp hc with rfl | hc
                      · simp
                      · exact h1 c hc
                    · simp [h2]
                    · simp [h3]
                  · have hsc : alignmentScore σ gap ((none, some b) :: A') =
                        gap + alignmentScore σ gap A' := by
                      simp [alignmentScore, columnScore]
                    rw [hsc, hscore]
                    omega
                · obtain ⟨A', hA',
                  hscore⟩ := ih xs (b :: ys) (by simp only [List.length_cons] at hle ⊢; omega)
                  refine ⟨(some a, none) :: A', ?_, ?_⟩
                  · obtain ⟨h1, h2, h3⟩ := hA'
                    refine ⟨?_, ?_, ?_⟩
                    · intro c hc
                      rcases List.mem_cons.mp hc with rfl | hc
                      · simp
                      · exact h1 c hc
                    · simp [h2]
                    · simp [h3]
                  · have hsc : alignmentScore σ gap ((some a, none) :: A') =
                        gap + alignmentScore σ gap A' := by
                      simp [alignmentScore, columnScore]
                    rw [hsc, hscore]
                    omega
              · obtain
                ⟨A', hA', hscore⟩ := ih xs ys (by simp only [List.length_cons] at hle ⊢; omega)
                refine ⟨(some a, some b) :: A', ?_, ?_⟩
                · obtain ⟨h1, h2, h3⟩ := hA'
                  refine ⟨?_, ?_, ?_⟩
                  · intro c hc
                    rcases List.mem_cons.mp hc with rfl | hc
                    · simp
                    · exact h1 c hc
                  · simp [h2]
                  · simp [h3]
                · have hsc : alignmentScore σ gap ((some a, some b) :: A') =
                      σ a b + alignmentScore σ gap A' := by
                    simp [alignmentScore, columnScore]
                  rw [hsc, hscore]
                  omega

/-- **Needleman–Wunsch is optimal**: every valid alignment scores at most `nwScore`. -/
theorem alignmentScore_le_nwScore (xs ys : List α) (A : Alignment α)
    (hA : IsAlignment A xs ys) :
    alignmentScore σ gap A ≤ nwScore σ gap xs ys :=
  alignmentScore_le_nwScore_aux σ gap (xs.length + ys.length) xs ys le_rfl A hA

/-- **Needleman–Wunsch is attained**: some valid alignment achieves `nwScore`. -/
theorem exists_alignmentScore_eq_nwScore (xs ys : List α) :
    ∃ A : Alignment α, IsAlignment A xs ys ∧ alignmentScore σ gap A = nwScore σ gap xs ys :=
  exists_alignmentScore_eq_nwScore_aux σ gap (xs.length + ys.length) xs ys le_rfl

end Alignments

section SmithWaterman

variable (σ : α → α → ℤ) (gap : ℤ)

/-- The Smith–Waterman front score: like `nwScoreAux`, but with the `0` floor of local
alignment. Front-peeling: the recursion drops heads. Exponential-time specification,
not a memoized table (see the module cost model). Implementation detail: use
`swCellScore`, not this worker, which returns `0` on insufficient fuel. -/
def swCellFront : ℕ → List α → List α → ℤ
  | 0, _, _ => 0
  | _ + 1, [], _ => 0
  | _ + 1, _, [] => 0
  | n + 1, a :: xs, b :: ys =>
      max 0 (max (max (swCellFront n xs ys + σ a b) (swCellFront n xs (b :: ys) + gap))
        (swCellFront n (a :: xs) ys + gap))

/-- The terminal Smith–Waterman cell (the `H(|xs|, |ys|)` entry of the DP table).
Defined by front-peeling on reversed lists, so the recurrence peels the *last* elements of
the original lists. For `gap ≤ 0` it is the optimal local alignment score of suffixes of
`xs` and `ys` ending at the last elements (`swCellScore_eq_suffixMax`); for positive gaps
it can be strictly smaller (one-letter lists with `σ = -100`, `gap = 1` give cell `1`
while the two-gap alignment scores `2`). This is *not* the optimal local alignment score
over all positions; that is `swScore`, the maximum of this cell over all prefix pairs. -/
def swCellScore (xs ys : List α) : ℤ :=
  swCellFront σ gap (xs.length + ys.length) xs.reverse ys.reverse

/-- Extra fuel does not change the front score. -/
private theorem swCellFront_succ_of_le : ∀ (m : ℕ) (xs ys : List α), xs.length + ys.length ≤ m →
    swCellFront σ gap m xs ys = swCellFront σ gap (m + 1) xs ys
  | 0, xs, ys, h => by
      have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
      have hy : ys = [] := List.length_eq_zero_iff.mp (by omega)
      subst hx
      subst hy
      rfl
  | m + 1, [], [], _ => rfl
  | m + 1, [], b :: ys, _ => rfl
  | m + 1, a :: xs, [], _ => rfl
  | m + 1, a :: xs, b :: ys, _ => by
      have h1 : (a :: xs).length = xs.length + 1 := rfl
      have h2 : (b :: ys).length = ys.length + 1 := rfl
      simp only [swCellFront]
      rw [swCellFront_succ_of_le m xs ys (by omega),
        swCellFront_succ_of_le m xs (b :: ys) (by omega),
        swCellFront_succ_of_le m (a :: xs) ys (by omega)]

/-- The front score depends only on the lengths through the fuel bound. -/
private theorem swCellFront_eq_of_le (m : ℕ) (xs ys : List α) (h : xs.length + ys.length ≤ m) :
    swCellFront σ gap m xs ys = swCellFront σ gap (xs.length + ys.length) xs ys := by
  induction m, h using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
      rw [← ih, swCellFront_succ_of_le σ gap m xs ys hm]

/-- The front score is nonnegative. -/
private theorem swCellFront_nonneg : ∀ (m : ℕ) (xs ys : List α), 0 ≤ swCellFront σ gap m xs ys := by
  intro m
  induction m with
  | zero => intro xs ys; exact le_rfl
  | succ m ih =>
      intro xs ys
      cases xs with
      | nil => exact le_rfl
      | cons a xs =>
          cases ys with
          | nil => exact le_rfl
          | cons b ys =>
              simp only [swCellFront]
              exact le_max_left 0 _

/-- The Smith–Waterman score is nonnegative. -/
theorem swCellScore_nonneg (xs ys : List α) : 0 ≤ swCellScore σ gap xs ys :=
  swCellFront_nonneg σ gap _ _ _

/-- The front score vanishes when the first list is empty. -/
private theorem swCellFront_nil_left (m : ℕ) (ys : List α) : swCellFront σ gap m [] ys = 0 := by
  cases m with
  | zero => simp [swCellFront]
  | succ m => simp [swCellFront]

/-- The front score vanishes when the second list is empty. -/
private theorem swCellFront_nil_right (m : ℕ) (xs : List α) : swCellFront σ gap m xs [] = 0 := by
  cases m with
  | zero => simp [swCellFront]
  | succ m =>
      cases xs with
      | nil => simp [swCellFront]
      | cons a xs => simp [swCellFront]

/-- Local alignment against the empty sequence scores `0`. -/
theorem swCellScore_nil_left (ys : List α) : swCellScore σ gap [] ys = 0 := by
  unfold swCellScore
  simp only [List.length_nil, List.reverse_nil, Nat.zero_add]
  exact swCellFront_nil_left σ gap _ _

/-- Local alignment against the empty sequence scores `0`. -/
theorem swCellScore_nil_right (xs : List α) : swCellScore σ gap xs [] = 0 := by
  unfold swCellScore
  simp only [List.length_nil, List.reverse_nil, Nat.add_zero]
  exact swCellFront_nil_right σ gap _ _

/-- **The Smith–Waterman recurrence**: the end-peeling recurrence. -/
theorem swCellScore_eq (xs ys : List α) (a b : α) :
    swCellScore σ gap (xs ++ [a]) (ys ++ [b]) =
      max 0 (max (max (swCellScore σ gap xs ys + σ a b)
        (swCellScore σ gap xs (ys ++ [b]) + gap))
        (swCellScore σ gap (xs ++ [a]) ys + gap)) := by
  have hrev1 : (xs ++ [a]).reverse = a :: xs.reverse := by simp [List.reverse_append]
  have hrev2 : (ys ++ [b]).reverse = b :: ys.reverse := by simp [List.reverse_append]
  have hlen : (xs ++ [a]).length + (ys ++ [b]).length = (xs.length + ys.length + 1) + 1 := by
    simp only [List.length_append, List.length_singleton]
    omega
  have e1 : swCellFront σ gap (xs.length + ys.length + 1) xs.reverse ys.reverse =
      swCellScore σ gap xs ys := by
    unfold swCellScore
    exact (swCellFront_succ_of_le σ gap (xs.length + ys.length) xs.reverse ys.reverse
      (by simp)).symm
  have e2 : swCellFront σ gap (xs.length + ys.length + 1) xs.reverse (b :: ys.reverse) =
      swCellScore σ gap xs (ys ++ [b]) := by
    have h : swCellScore σ gap xs (ys ++ [b]) =
        swCellFront σ gap (xs.length + ys.length + 1) xs.reverse (b :: ys.reverse) := by
      unfold swCellScore
      simp [List.reverse_append, List.length_append]
      rw [← Nat.add_assoc]
    exact h.symm
  have e3 : swCellFront σ gap (xs.length + ys.length + 1) (a :: xs.reverse) ys.reverse =
      swCellScore σ gap (xs ++ [a]) ys := by
    have h : swCellScore σ gap (xs ++ [a]) ys =
        swCellFront σ gap (xs.length + ys.length + 1) (a :: xs.reverse) ys.reverse := by
      unfold swCellScore
      simp [List.reverse_append, List.length_append]
      rw [Nat.add_right_comm]
    exact h.symm
  have hunfold : swCellFront σ gap ((xs.length + ys.length + 1) + 1)
      (a :: xs.reverse) (b :: ys.reverse) =
      max 0 (max (max (swCellFront σ gap (xs.length + ys.length + 1) xs.reverse ys.reverse + σ a b)
        (swCellFront σ gap (xs.length + ys.length + 1) xs.reverse (b :: ys.reverse) + gap))
        (swCellFront σ gap (xs.length + ys.length + 1) (a :: xs.reverse) ys.reverse + gap)) := rfl
  rw [swCellScore, hrev1, hrev2, hlen, hunfold, e1, e2, e3]

/-- A suffix of `xs ++ [a]` is either empty or a suffix of `xs` with `a` appended. -/
theorem suffix_of_snoc {xs : List α} {a : α} {s : List α} (h : s <:+ xs ++ [a]) :
    s = [] ∨ ∃ s', s' <:+ xs ∧ s = s' ++ [a] := by
  obtain ⟨t, ht⟩ := h
  rcases List.eq_nil_or_concat s with hs | ⟨s₀, a₀, hs⟩
  · exact Or.inl hs
  · right
    rw [List.concat_eq_append] at hs
    subst hs
    have ht2 : (t ++ s₀) ++ [a₀] = xs ++ [a] := by rwa [← List.append_assoc] at ht
    obtain ⟨ht', ha⟩ := List.append_inj' ht2 (by simp)
    exact ⟨s₀, ⟨t, ht'⟩, by rw [ha]⟩

/-- Appending the same element preserves the suffix relation. -/
theorem suffix_append_snoc {s xs : List α} {a : α} (h : s <:+ xs) : s ++ [a] <:+ xs ++ [a] := by
  obtain ⟨u, hu⟩ := h
  exact ⟨u, by rw [← hu, List.append_assoc]⟩

/-- Reversing an alignment reverses the two sequences it aligns. -/
theorem isAlignment_reverse {A : Alignment α} {xs ys : List α} :
    IsAlignment A xs.reverse ys.reverse ↔ IsAlignment A.reverse xs ys := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun c hc => h1 c (List.mem_reverse.mp hc), ?_, ?_⟩
    · rw [List.filterMap_reverse, h2, List.reverse_reverse]
    · rw [List.filterMap_reverse, h3, List.reverse_reverse]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun c hc => h1 c (List.mem_reverse.mpr hc), ?_, ?_⟩
    · have h2' := congrArg List.reverse h2
      rw [List.filterMap_reverse, List.reverse_reverse] at h2'
      exact h2'
    · have h3' := congrArg List.reverse h3
      rw [List.filterMap_reverse, List.reverse_reverse] at h3'
      exact h3'

/-- Reversing an alignment preserves its score. -/
theorem alignmentScore_reverse (A : Alignment α) :
    alignmentScore σ gap A.reverse = alignmentScore σ gap A := by
  simp [alignmentScore, List.map_reverse, List.sum_reverse]

/-- **Needleman–Wunsch is reversal-invariant**: reversing both sequences preserves the
optimal global score. -/
theorem nwScore_reverse (xs ys : List α) :
    nwScore σ gap xs.reverse ys.reverse = nwScore σ gap xs ys := by
  apply le_antisymm
  · obtain ⟨A, hA, hscore⟩ := exists_alignmentScore_eq_nwScore σ gap xs.reverse ys.reverse
    rw [← hscore, ← alignmentScore_reverse σ gap A]
    exact alignmentScore_le_nwScore σ gap xs ys A.reverse
      ((isAlignment_reverse (A := A) (xs := xs) (ys := ys)).mp hA)
  · obtain ⟨A, hA, hscore⟩ := exists_alignmentScore_eq_nwScore σ gap xs ys
    have hA' : IsAlignment A.reverse xs.reverse ys.reverse :=
      (isAlignment_reverse (A := A.reverse) (xs := xs) (ys := ys)).mpr (by simpa using hA)
    rw [← hscore, ← alignmentScore_reverse σ gap A]
    exact alignmentScore_le_nwScore σ gap xs.reverse ys.reverse A.reverse hA'

/-- **The Needleman–Wunsch recurrence, end-peeling.** -/
theorem nwScore_snoc (xs ys : List α) (a b : α) :
    nwScore σ gap (xs ++ [a]) (ys ++ [b]) =
      max (max (nwScore σ gap xs ys + σ a b) (nwScore σ gap xs (ys ++ [b]) + gap))
        (nwScore σ gap (xs ++ [a]) ys + gap) := by
  have h1 : nwScore σ gap (xs ++ [a]) (ys ++ [b])
      = nwScore σ gap ((xs ++ [a]).reverse) ((ys ++ [b]).reverse) :=
    (nwScore_reverse σ gap (xs ++ [a]) (ys ++ [b])).symm
  have hrev1 : (xs ++ [a]).reverse = a :: xs.reverse := by simp [List.reverse_append]
  have hrev2 : (ys ++ [b]).reverse = b :: ys.reverse := by simp [List.reverse_append]
  have e1 : nwScore σ gap xs.reverse ys.reverse = nwScore σ gap xs ys :=
    nwScore_reverse σ gap xs ys
  have e2 : nwScore σ gap xs.reverse (b :: ys.reverse) = nwScore σ gap xs (ys ++ [b]) := by
    rw [show (b :: ys.reverse) = (ys ++ [b]).reverse by simp [List.reverse_append]]
    exact nwScore_reverse σ gap xs (ys ++ [b])
  have e3 : nwScore σ gap (a :: xs.reverse) ys.reverse = nwScore σ gap (xs ++ [a]) ys := by
    rw [show (a :: xs.reverse) = (xs ++ [a]).reverse by simp [List.reverse_append]]
    exact nwScore_reverse σ gap (xs ++ [a]) ys
  rw [h1, hrev1, hrev2, nwScore_eq, e1, e2, e3]

-- Candidate collections are plain lists, not finsets: `List.product` and `List.map`
-- need no `DecidableEq` on the alphabet, so the characterizations below work over
-- any type. Duplicates in the candidate lists do not affect a maximum.

/-- Maximum of a list of integers, with floor `0` (the empty list folds to `0`).
Internal helper for the candidate-list maxima; the public maxima are `suffixMax`,
`localScore`, and `swScore`. -/
def listMax (xs : List ℤ) : ℤ := xs.foldr (max ·) 0

private theorem listMax_le_of_all_le {xs : List ℤ} {y : ℤ}
    (h : ∀ a ∈ xs, a ≤ y) (hy : 0 ≤ y) : listMax xs ≤ y := by
  induction xs with
  | nil => exact hy
  | cons a as ih =>
    simp only [listMax, List.foldr_cons]
    exact max_le (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

private theorem le_listMax_of_mem {xs : List ℤ} {a : ℤ} (ha : a ∈ xs) : a ≤ listMax xs := by
  induction xs with
  | nil => simp at ha
  | cons b bs ih =>
    rw [listMax, List.foldr_cons]
    cases List.mem_cons.mp ha with
    | inl h => rw [h]; exact le_max_left _ _
    | inr h => exact le_trans (ih h) (le_max_right _ _)

/-- The list maximum is `0` or an element of the list. -/
private theorem listMax_mem {xs : List ℤ} : listMax xs ∈ 0 :: xs := by
  induction xs with
  | nil => exact List.mem_cons_self
  | cons b bs ih =>
    change max b (listMax bs) ∈ 0 :: b :: bs
    by_cases h : b ≤ listMax bs
    · rw [max_eq_right h]
      rcases List.mem_cons.mp ih with h0 | hbs
      · rw [← h0]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hbs)
    · rw [max_eq_left (le_of_not_ge h)]
      exact List.mem_cons_of_mem _ List.mem_cons_self

/-- All suffix pairs of `xs` and `ys`, as a list of pairs. -/
def suffixPairs (xs ys : List α) : List (List α × List α) :=
  xs.tails.product ys.tails

theorem mem_suffixPairs {xs' ys' xs ys : List α} :
    (xs', ys') ∈ suffixPairs xs ys ↔ xs' <:+ xs ∧ ys' <:+ ys := by
  simp [suffixPairs, List.mem_tails]

/-- The maximum Needleman–Wunsch score over all suffix pairs, as a list maximum. -/
def suffixMax (σ : α → α → ℤ) (gap : ℤ) (xs ys : List α) : ℤ :=
  listMax ((suffixPairs xs ys).map (fun p => nwScore σ gap p.1 p.2))

/-- A suffix pair's score is at most the suffix maximum. -/
theorem nwScore_le_suffixMax {xs' ys' xs ys : List α}
    (h : (xs', ys') ∈ suffixPairs xs ys) :
    nwScore σ gap xs' ys' ≤ suffixMax σ gap xs ys := by
  unfold suffixMax
  apply le_listMax_of_mem
  exact List.mem_map_of_mem h

/-- A bound on all suffix-pair scores bounds the suffix maximum. -/
theorem suffixMax_le {xs ys : List α} {y : ℤ}
    (h : ∀ p ∈ suffixPairs xs ys, nwScore σ gap p.1 p.2 ≤ y) :
    suffixMax σ gap xs ys ≤ y := by
  unfold suffixMax
  apply listMax_le_of_all_le _ ?_
  · intro a ha
    rw [List.mem_map] at ha
    obtain ⟨p, hp, rfl⟩ := ha
    exact h p hp
  · have h0 := h ([], [])
      (mem_suffixPairs.mpr ⟨List.nil_suffix (l := xs), List.nil_suffix (l := ys)⟩)
    simpa [nwScore_nil_left] using h0

/-- The suffix maximum is attained by some suffix pair. -/
theorem exists_nwScore_eq_suffixMax (σ : α → α → ℤ) (gap : ℤ) (xs ys : List α) :
    ∃ p ∈ suffixPairs xs ys, nwScore σ gap p.1 p.2 = suffixMax σ gap xs ys := by
  have hmem := listMax_mem
    (xs := (suffixPairs xs ys).map (fun p => nwScore σ gap p.1 p.2))
  rw [List.mem_cons] at hmem
  rcases hmem with h0 | hmem
  · refine ⟨([], []), ?_, ?_⟩
    · exact mem_suffixPairs.mpr ⟨List.nil_suffix (l := xs), List.nil_suffix (l := ys)⟩
    · have h00 : nwScore σ gap [] [] = 0 := by rw [nwScore_nil_left]; simp
      rw [suffixMax]
      exact h00.trans h0.symm
  · rw [List.mem_map] at hmem
    obtain ⟨p, hp, hpEq⟩ := hmem
    exact ⟨p, hp, hpEq⟩

/-- The suffix maximum is nonnegative: the empty pair scores `0`. -/
theorem zero_le_suffixMax (σ : α → α → ℤ) (gap : ℤ) (xs ys : List α) :
    0 ≤ suffixMax σ gap xs ys :=
  nwScore_le_suffixMax σ gap
    (show ([], []) ∈ suffixPairs xs ys from
      mem_suffixPairs.mpr
        ⟨List.nil_suffix (l := xs), List.nil_suffix (l := ys)⟩)
/-- Appending a gap column on the left preserves alignment validity. -/
theorem isAlignment_append_some_none {A : Alignment α} {xs ys : List α} {a : α}
    (hA : IsAlignment A xs ys) :
    IsAlignment (A ++ [(some a, none)]) (xs ++ [a]) ys := by
  obtain ⟨h1, h2, h3⟩ := hA
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    rw [List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | hc
    · exact h1 c hc
    · simp [hc]
  · simp [List.filterMap_append, h2]
  · simp [List.filterMap_append, h3]

/-- Appending a gap column on the right preserves alignment validity. -/
theorem isAlignment_append_none_some {A : Alignment α} {xs ys : List α} {b : α}
    (hA : IsAlignment A xs ys) :
    IsAlignment (A ++ [(none, some b)]) xs (ys ++ [b]) := by
  obtain ⟨h1, h2, h3⟩ := hA
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    rw [List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | hc
    · exact h1 c hc
    · simp [hc]
  · simp [List.filterMap_append, h2]
  · simp [List.filterMap_append, h3]

/-- Extending the first sequence by one element can only add a gap column. -/
theorem nwScore_le_nwScore_snoc_left (σ : α → α → ℤ) (gap : ℤ) (xs ys : List α) (a : α) :
    nwScore σ gap xs ys + gap ≤ nwScore σ gap (xs ++ [a]) ys := by
  obtain ⟨A, hA, hscore⟩ := exists_alignmentScore_eq_nwScore σ gap xs ys
  have hA' : IsAlignment (A ++ [(some a, none)]) (xs ++ [a]) ys :=
    isAlignment_append_some_none hA
  have hcol : columnScore σ gap (some a, none) = gap := rfl
  have hsc : alignmentScore σ gap (A ++ [(some a, none)]) = nwScore σ gap xs ys + gap := by
    rw [alignmentScore_append, alignmentScore_singleton, hscore, hcol]
  rw [← hsc]
  exact alignmentScore_le_nwScore σ gap (xs ++ [a]) ys (A ++ [(some a, none)]) hA'

/-- Extending the second sequence by one element can only add a gap column. -/
theorem nwScore_le_nwScore_snoc_right (σ : α → α → ℤ) (gap : ℤ) (xs ys : List α) (b : α) :
    nwScore σ gap xs ys + gap ≤ nwScore σ gap xs (ys ++ [b]) := by
  obtain ⟨A, hA, hscore⟩ := exists_alignmentScore_eq_nwScore σ gap xs ys
  have hA' : IsAlignment (A ++ [(none, some b)]) xs (ys ++ [b]) :=
    isAlignment_append_none_some hA
  have hcol : columnScore σ gap (none, some b) = gap := rfl
  have hsc : alignmentScore σ gap (A ++ [(none, some b)]) = nwScore σ gap xs ys + gap := by
    rw [alignmentScore_append, alignmentScore_singleton, hscore, hcol]
  rw [← hsc]
  exact alignmentScore_le_nwScore σ gap xs (ys ++ [b]) (A ++ [(none, some b)]) hA'

/-- **Every suffix pair scores at most the Smith–Waterman score** (needs `gap ≤ 0`). -/
theorem nwScore_le_swCellScore_of_suffix (hgap : gap ≤ 0) {xs' ys' xs ys : List α}
    (hxs : xs' <:+ xs) (hys : ys' <:+ ys) :
    nwScore σ gap xs' ys' ≤ swCellScore σ gap xs ys := by
  have key : ∀ (ys' : List α), nwScore σ gap [] ys' ≤ 0 := by
    intro ys'
    rw [nwScore_nil_left]
    exact mul_nonpos_of_nonpos_of_nonneg hgap (by exact_mod_cast Nat.zero_le _)
  have key' : ∀ (xs' : List α), nwScore σ gap xs' [] ≤ 0 := by
    intro xs'
    rw [nwScore_nil_right]
    exact mul_nonpos_of_nonpos_of_nonneg hgap (by exact_mod_cast Nat.zero_le _)
  have key2 : ∀ (n : ℕ) (xs ys : List α), xs.length + ys.length ≤ n →
      ∀ {xs' ys' : List α}, xs' <:+ xs → ys' <:+ ys →
        nwScore σ gap xs' ys' ≤ swCellScore σ gap xs ys := by
    intro n
    induction n with
    | zero =>
        intro xs ys hle xs' ys' hxs hys
        have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
        have hy : ys = [] := List.length_eq_zero_iff.mp (by omega)
        subst hx
        subst hy
        obtain ⟨t, ht⟩ := hxs
        have hxs' : xs' = [] := (List.append_eq_nil_iff.mp ht).2
        obtain ⟨t, ht⟩ := hys
        have hys' : ys' = [] := (List.append_eq_nil_iff.mp ht).2
        rw [hxs', hys']
        exact swCellScore_nonneg σ gap [] []
    | succ n ih =>
        intro xs ys hle xs' ys' hxs hys
        rcases List.eq_nil_or_concat xs with hx | ⟨xs₀, a, hx⟩
        · subst hx
          obtain ⟨t, ht⟩ := hxs
          have hxs' : xs' = [] := (List.append_eq_nil_iff.mp ht).2
          rw [hxs']
          exact le_trans (key ys') (swCellScore_nonneg σ gap [] ys)
        · rw [List.concat_eq_append] at hx
          subst hx
          rcases List.eq_nil_or_concat ys with hy | ⟨ys₀, b, hy⟩
          · subst hy
            obtain ⟨t, ht⟩ := hys
            have hys' : ys' = [] := (List.append_eq_nil_iff.mp ht).2
            rw [hys']
            exact le_trans (key' xs') (swCellScore_nonneg σ gap (xs₀ ++ [a]) [])
          · rw [List.concat_eq_append] at hy
            subst hy
            rcases suffix_of_snoc hxs with rfl | ⟨xs'', hxs'', rfl⟩
            · exact le_trans (key ys') (swCellScore_nonneg σ gap (xs₀ ++ [a]) (ys₀ ++ [b]))
            · rcases suffix_of_snoc hys with rfl | ⟨ys'', hys'', rfl⟩
              · exact le_trans (key' _) (swCellScore_nonneg σ gap (xs₀ ++ [a]) (ys₀ ++ [b]))
              · have hlen1 : (xs₀ ++ [a]).length = xs₀.length + 1 := by simp
                have hlen2 : (ys₀ ++ [b]).length = ys₀.length + 1 := by simp
                have h1 : nwScore σ gap xs'' ys'' ≤ swCellScore σ gap xs₀ ys₀ :=
                  ih xs₀ ys₀ (by omega) hxs'' hys''
                have h2 : nwScore σ gap xs'' (ys'' ++ [b]) ≤
                    swCellScore σ gap xs₀ (ys₀ ++ [b]) :=
                  ih xs₀ (ys₀ ++ [b]) (by omega) hxs'' (suffix_append_snoc hys'')
                have h3 : nwScore σ gap (xs'' ++ [a]) ys'' ≤
                    swCellScore σ gap (xs₀ ++ [a]) ys₀ :=
                  ih (xs₀ ++ [a]) ys₀ (by omega) (suffix_append_snoc hxs'') hys''
                rw [nwScore_snoc, swCellScore_eq]
                exact le_trans
                  (max_le_max (max_le_max (add_le_add_left h1 _)
                    (add_le_add_left h2 _)) (add_le_add_left h3 _))
                  (le_max_right _ _)
  exact key2 (xs.length + ys.length) xs ys le_rfl hxs hys

/-- **The terminal cell is at most the suffix maximum**, for every gap: only the
reverse inequality needs `gap ≤ 0`. -/
theorem swCellScore_le_suffixMax (xs ys : List α) :
    swCellScore σ gap xs ys ≤ suffixMax σ gap xs ys := by
  have key : ∀ (n : ℕ) (xs ys : List α), xs.length + ys.length ≤ n →
      swCellScore σ gap xs ys ≤ suffixMax σ gap xs ys := by
    intro n
    induction n with
    | zero =>
        intro xs ys hle
        have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
        have hy : ys = [] := List.length_eq_zero_iff.mp (by omega)
        subst hx
        subst hy
        rw [swCellScore_nil_left]
        exact zero_le_suffixMax σ gap [] []
    | succ n ih =>
        intro xs ys hle
        rcases List.eq_nil_or_concat xs with hx | ⟨xs₀, a, hx⟩
        · subst hx
          rw [swCellScore_nil_left]
          exact zero_le_suffixMax σ gap [] ys
        · rw [List.concat_eq_append] at hx
          subst hx
          rcases List.eq_nil_or_concat ys with hy | ⟨ys₀, b, hy⟩
          · subst hy
            rw [swCellScore_nil_right]
            exact zero_le_suffixMax σ gap (xs₀ ++ [a]) []
          · rw [List.concat_eq_append] at hy
            subst hy
            have hlen1 : (xs₀ ++ [a]).length = xs₀.length + 1 := by simp
            have hlen2 : (ys₀ ++ [b]).length = ys₀.length + 1 := by simp
            rw [swCellScore_eq]
            refine max_le ?_ (max_le (max_le ?_ ?_) ?_)
            · exact zero_le_suffixMax σ gap (xs₀ ++ [a]) (ys₀ ++ [b])
            · obtain ⟨⟨xs', ys'⟩, hmem, hEq⟩ :=
                exists_nwScore_eq_suffixMax σ gap xs₀ ys₀
              rw [mem_suffixPairs] at hmem
              have hPair : nwScore σ gap (xs' ++ [a]) (ys' ++ [b]) ≤
                  suffixMax σ gap (xs₀ ++ [a]) (ys₀ ++ [b]) :=
                nwScore_le_suffixMax σ gap
                  (show (xs' ++ [a], ys' ++ [b]) ∈
                    suffixPairs (xs₀ ++ [a]) (ys₀ ++ [b]) from
                    mem_suffixPairs.mpr
                      ⟨suffix_append_snoc hmem.1, suffix_append_snoc hmem.2⟩)
              have hNW : nwScore σ gap xs' ys' + σ a b ≤
                  nwScore σ gap (xs' ++ [a]) (ys' ++ [b]) := by
                rw [nwScore_snoc]
                exact le_max_of_le_left (le_max_of_le_left le_rfl)
              have hIH : swCellScore σ gap xs₀ ys₀ ≤ suffixMax σ gap xs₀ ys₀ :=
                ih xs₀ ys₀ (by omega)
              have h1 : swCellScore σ gap xs₀ ys₀ + σ a b ≤
                  suffixMax σ gap xs₀ ys₀ + σ a b := add_le_add_left hIH _
              rw [← hEq] at h1
              exact le_trans (le_trans h1 hNW) hPair
            · obtain ⟨⟨xs', ys'⟩, hmem, hEq⟩ :=
                exists_nwScore_eq_suffixMax σ gap xs₀ (ys₀ ++ [b])
              rw [mem_suffixPairs] at hmem
              have hPair : nwScore σ gap (xs' ++ [a]) ys' ≤
                  suffixMax σ gap (xs₀ ++ [a]) (ys₀ ++ [b]) :=
                nwScore_le_suffixMax σ gap
                  (show (xs' ++ [a], ys') ∈
                    suffixPairs (xs₀ ++ [a]) (ys₀ ++ [b]) from
                    mem_suffixPairs.mpr ⟨suffix_append_snoc hmem.1, hmem.2⟩)
              have hNW : nwScore σ gap xs' ys' + gap ≤
                  nwScore σ gap (xs' ++ [a]) ys' :=
                nwScore_le_nwScore_snoc_left σ gap xs' ys' a
              have hIH : swCellScore σ gap xs₀ (ys₀ ++ [b]) ≤
                  suffixMax σ gap xs₀ (ys₀ ++ [b]) := ih xs₀ (ys₀ ++ [b]) (by omega)
              have h1 : swCellScore σ gap xs₀ (ys₀ ++ [b]) + gap ≤
                  suffixMax σ gap xs₀ (ys₀ ++ [b]) + gap := add_le_add_left hIH _
              rw [← hEq] at h1
              exact le_trans (le_trans h1 hNW) hPair
            · obtain ⟨⟨xs', ys'⟩, hmem, hEq⟩ :=
                exists_nwScore_eq_suffixMax σ gap (xs₀ ++ [a]) ys₀
              rw [mem_suffixPairs] at hmem
              have hPair : nwScore σ gap xs' (ys' ++ [b]) ≤
                  suffixMax σ gap (xs₀ ++ [a]) (ys₀ ++ [b]) :=
                nwScore_le_suffixMax σ gap
                  (show (xs', ys' ++ [b]) ∈
                    suffixPairs (xs₀ ++ [a]) (ys₀ ++ [b]) from
                    mem_suffixPairs.mpr ⟨hmem.1, suffix_append_snoc hmem.2⟩)
              have hNW : nwScore σ gap xs' ys' + gap ≤
                  nwScore σ gap xs' (ys' ++ [b]) :=
                nwScore_le_nwScore_snoc_right σ gap xs' ys' b
              have hIH : swCellScore σ gap (xs₀ ++ [a]) ys₀ ≤
                  suffixMax σ gap (xs₀ ++ [a]) ys₀ := ih (xs₀ ++ [a]) ys₀ (by omega)
              have h1 : swCellScore σ gap (xs₀ ++ [a]) ys₀ + gap ≤
                  suffixMax σ gap (xs₀ ++ [a]) ys₀ + gap := add_le_add_left hIH _
              rw [← hEq] at h1
              exact le_trans (le_trans h1 hNW) hPair
  exact key (xs.length + ys.length) xs ys le_rfl

/-- **Every suffix pair scores at most the Smith–Waterman score**, rephrased as a
supremum bound (needs `gap ≤ 0`). -/
theorem suffixMax_le_swCellScore (hgap : gap ≤ 0) (xs ys : List α) :
    suffixMax σ gap xs ys ≤ swCellScore σ gap xs ys := by
  apply suffixMax_le
  intro p hp
  rw [mem_suffixPairs] at hp
  exact nwScore_le_swCellScore_of_suffix σ gap hgap hp.1 hp.2

/-- **Smith–Waterman equals the max Needleman–Wunsch score over suffix pairs**
(needs `gap ≤ 0`). -/
theorem swCellScore_eq_suffixMax (hgap : gap ≤ 0) (xs ys : List α) :
    swCellScore σ gap xs ys = suffixMax σ gap xs ys :=
  le_antisymm (swCellScore_le_suffixMax σ gap xs ys)
    (suffixMax_le_swCellScore σ gap hgap xs ys)

/-- All prefix pairs of `xs` and `ys`, as a list of pairs. -/
def prefixPairs (xs ys : List α) : List (List α × List α) :=
  xs.inits.product ys.inits

theorem mem_prefixPairs {px py xs ys : List α} :
    (px, py) ∈ prefixPairs xs ys ↔ px <+: xs ∧ py <+: ys := by
  simp [prefixPairs, List.mem_inits]

/-- All infix pairs of `xs` and `ys`, as suffixes of prefixes. -/
def infixPairs (xs ys : List α) : List (List α × List α) :=
  (prefixPairs xs ys).flatMap (fun p => p.1.tails.product p.2.tails)

theorem mem_infixPairs {xs' ys' xs ys : List α} :
    (xs', ys') ∈ infixPairs xs ys ↔
      ∃ px py, px <+: xs ∧ py <+: ys ∧ xs' <:+ px ∧ ys' <:+ py := by
  constructor
  · intro h
    simp only [infixPairs, List.mem_flatMap] at h
    obtain ⟨⟨px, py⟩, hpx, hmem⟩ := h
    rw [mem_prefixPairs] at hpx
    obtain ⟨h1, h2⟩ := List.mem_product.mp hmem
    rw [List.mem_tails] at h1 h2
    exact ⟨px, py, hpx.1, hpx.2, h1, h2⟩
  · rintro ⟨px, py, hpx, hpy, h1, h2⟩
    simp only [infixPairs, List.mem_flatMap]
    refine ⟨⟨px, py⟩, ?_, ?_⟩
    · rw [mem_prefixPairs]
      exact ⟨hpx, hpy⟩
    · exact List.mem_product.mpr
        ⟨(List.mem_tails _ _).mpr h1, (List.mem_tails _ _).mpr h2⟩

/-- The maximum Needleman–Wunsch score over all infix pairs: the local score. -/
def localScore (σ : α → α → ℤ) (gap : ℤ) (xs ys : List α) : ℤ :=
  listMax ((infixPairs xs ys).map (fun p => nwScore σ gap p.1 p.2))

/-- An infix pair's score is at most the local score. -/
theorem nwScore_le_localScore {xs' ys' xs ys : List α}
    (h : (xs', ys') ∈ infixPairs xs ys) :
    nwScore σ gap xs' ys' ≤ localScore σ gap xs ys := by
  unfold localScore
  apply le_listMax_of_mem
  exact List.mem_map_of_mem h

/-- A bound on all infix-pair scores bounds the local score. -/
theorem localScore_le {xs ys : List α} {y : ℤ}
    (h : ∀ p ∈ infixPairs xs ys, nwScore σ gap p.1 p.2 ≤ y) :
    localScore σ gap xs ys ≤ y := by
  unfold localScore
  apply listMax_le_of_all_le _ ?_
  · intro a ha
    rw [List.mem_map] at ha
    obtain ⟨p, hp, rfl⟩ := ha
    exact h p hp
  · have h0 := h ([], [])
      (mem_infixPairs.mpr ⟨[], [], List.nil_prefix (l := xs), List.nil_prefix (l := ys),
        List.nil_suffix (l := []), List.nil_suffix (l := [])⟩)
    simpa [nwScore_nil_left] using h0

/-- **The Smith–Waterman score**: the maximum terminal-cell score over all pairs of
prefixes. For `gap ≤ 0` this is the optimal local alignment score
(`localScore_eq_swScore`); for positive gaps it can be smaller. -/
def swScore (σ : α → α → ℤ) (gap : ℤ) (xs ys : List α) : ℤ :=
  listMax ((prefixPairs xs ys).map (fun p => swCellScore σ gap p.1 p.2))

/-- A prefix pair's cell score is at most the Smith–Waterman score. -/
theorem swCellScore_le_swScore {px py xs ys : List α}
    (h : (px, py) ∈ prefixPairs xs ys) :
    swCellScore σ gap px py ≤ swScore σ gap xs ys := by
  unfold swScore
  apply le_listMax_of_mem
  exact List.mem_map_of_mem h

/-- A bound on all prefix-pair cell scores bounds the Smith–Waterman score. -/
theorem swScore_le {xs ys : List α} {y : ℤ}
    (h : ∀ p ∈ prefixPairs xs ys, swCellScore σ gap p.1 p.2 ≤ y) :
    swScore σ gap xs ys ≤ y := by
  unfold swScore
  apply listMax_le_of_all_le _ ?_
  · intro a ha
    rw [List.mem_map] at ha
    obtain ⟨p, hp, rfl⟩ := ha
    exact h p hp
  · have h0 := h ([], [])
      (mem_prefixPairs.mpr ⟨List.nil_prefix (l := xs), List.nil_prefix (l := ys)⟩)
    simpa [swCellScore_nil_left] using h0

/-- **The local score equals the Smith–Waterman score** (needs `gap ≤ 0`): an infix
is a suffix of a prefix, and the terminal cell is a max over suffixes. -/
theorem localScore_eq_swScore (hgap : gap ≤ 0) (xs ys : List α) :
    localScore σ gap xs ys = swScore σ gap xs ys := by
  apply le_antisymm
  · apply localScore_le
    intro p hp
    rw [mem_infixPairs] at hp
    obtain ⟨px, py, hpx, hpy, h1, h2⟩ := hp
    exact le_trans (nwScore_le_swCellScore_of_suffix σ gap hgap h1 h2)
      (swCellScore_le_swScore σ gap
        (show (px, py) ∈ prefixPairs xs ys from mem_prefixPairs.mpr ⟨hpx, hpy⟩))
  · apply swScore_le
    intro p hp
    rw [mem_prefixPairs] at hp
    rw [swCellScore_eq_suffixMax σ gap hgap]
    obtain ⟨⟨qx, qy⟩, hmem, hEq⟩ := exists_nwScore_eq_suffixMax σ gap p.1 p.2
    rw [mem_suffixPairs] at hmem
    rw [← hEq]
    exact nwScore_le_localScore σ gap
      (show (qx, qy) ∈ infixPairs xs ys from
        mem_infixPairs.mpr ⟨p.1, p.2, hp.1, hp.2, hmem.1, hmem.2⟩)

end SmithWaterman

end Cslib.Algorithms.Lean
