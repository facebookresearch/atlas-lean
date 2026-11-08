/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.SequenceAlignment

/-!
# Banded pairwise sequence alignment

Banded alignment (Durbin et al., *Biological Sequence Analysis*, Cambridge, 1998)
restricts Needleman–Wunsch to alignments whose path stays within a diagonal band:
after each prefix of the alignment, the numbers of consumed letters from the two
sequences differ by at most `w`. This is the right restriction when the sequences
are known to be similar, and it is what makes the banded dynamic program visit only
`O((2 * w + 1) * (min(|xs|, |ys|) + 1))` cells instead of the full table: the
band contains `2 * w + 1` diagonals (offsets `-w` through `w`, so the diagonal
itself counts even when `w = 0`), each of length at most `min(|xs|, |ys|) + 1`.

Main results:

* `bandedScore_le_nwScore`: a banded optimum is at most the unrestricted optimum.
* `bandedScore_eq_nwScore_of_banded_optimal`: if some optimal alignment is banded,
  the banded score is the unrestricted optimum.
* `bandedScore_none_of_length_diff_gt`: if the lengths differ by more than `w`,
  no banded alignment exists.
* `bandedScore_some_of_length_diff_le`: if the lengths differ by at most `w`,
  a banded alignment exists (the diagonal alignment), so the banded score is `some`.

The banded score is specified as the maximum over banded alignments (an `Option`,
`none` when no banded alignment exists), not as a banded dynamic-programming table;
a tabulated banded DP proved equal to it is future work, as is a banded
recurrence for the offset-parameterized score.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u

variable {α : Type u}

section Banded

variable (σ : α → α → ℤ) (gap : ℤ) (w : ℕ)

/-- The band check with starting offset `(i, j)`: every prefix of `A`, counted
from the offset, stays within `|i - j| ≤ w`. -/
def bandedFrom : ℕ → ℕ → Alignment α → Bool
  | i, j, [] => decide (|(i : ℤ) - (j : ℤ)| ≤ (w : ℤ))
  | i, j, (some _, some _) :: A =>
      decide (|(i : ℤ) - (j : ℤ)| ≤ (w : ℤ)) && bandedFrom (i + 1) (j + 1) A
  | i, j, (some _, none) :: A =>
      decide (|(i : ℤ) - (j : ℤ)| ≤ (w : ℤ)) && bandedFrom (i + 1) j A
  | i, j, (none, some _) :: A =>
      decide (|(i : ℤ) - (j : ℤ)| ≤ (w : ℤ)) && bandedFrom i (j + 1) A
  | i, j, (none, none) :: A =>
      decide (|(i : ℤ) - (j : ℤ)| ≤ (w : ℤ)) && bandedFrom i j A

/-- An alignment is banded when its path, from offset `(0, 0)`, stays in the band. -/
def IsBanded (A : Alignment α) : Prop := bandedFrom w 0 0 A = true

/-- A helper: `|a - t| ≤ w` when `t` lies between `0` and `d` and both endpoints
of the interval satisfy the bound. Used for the gap phases, where the offset
difference interpolates between its start and end values. -/
theorem abs_le_of_between {a d t w : ℤ} (h0 : |a| ≤ w) (hd : |a - d| ≤ w)
    (ht0 : 0 ≤ t) (htd : t ≤ d) : |a - t| ≤ w := by
  rw [abs_le] at h0 hd ⊢
  constructor <;> linarith

/-- Same, for `a + t`: used for gap-in-`xs` phases, where the difference grows. -/
theorem abs_le_of_between_add {a d t w : ℤ} (h0 : |a| ≤ w) (hd : |a + d| ≤ w)
    (ht0 : 0 ≤ t) (htd : t ≤ d) : |a + t| ≤ w := by
  rw [abs_le] at h0 hd ⊢
  constructor <;> linarith

/-- A banded alignment ends within the band: its final offset difference is
bounded by `w`. -/
theorem bandedFrom_final : ∀ (A : Alignment α) (i j : ℕ),
    bandedFrom w i j A = true →
    |(i + (A.filterMap Prod.fst).length : ℤ)
      - (j + (A.filterMap Prod.snd).length)| ≤ (w : ℤ)
  | [], i, j, h => by
      simp only [bandedFrom] at h
      have h' : |(i : ℤ) - (j : ℤ)| ≤ (w : ℤ) := of_decide_eq_true h
      simpa using h'
  | (some a, some b) :: A, i, j, h => by
      simp only [bandedFrom] at h
      rw [Bool.and_eq_true] at h
      have ih := bandedFrom_final A (i + 1) (j + 1) h.2
      simp only [List.filterMap_cons, List.length_cons] at ⊢
      convert ih using 2
      push_cast
      ring
  | (some a, none) :: A, i, j, h => by
      simp only [bandedFrom] at h
      rw [Bool.and_eq_true] at h
      have ih := bandedFrom_final A (i + 1) j h.2
      simp only [List.filterMap_cons, List.length_cons] at ⊢
      convert ih using 2
      push_cast
      ring
  | (none, some b) :: A, i, j, h => by
      simp only [bandedFrom] at h
      rw [Bool.and_eq_true] at h
      have ih := bandedFrom_final A i (j + 1) h.2
      simp only [List.filterMap_cons, List.length_cons] at ⊢
      convert ih using 2
      push_cast
      ring
  | (none, none) :: A, i, j, h => by
      simp only [bandedFrom] at h
      rw [Bool.and_eq_true] at h
      have ih := bandedFrom_final A i j h.2
      simpa only [List.filterMap_cons] using ih

/-- A banded alignment of `xs`, `ys` has its length difference within the band. -/
theorem isBanded_length_diff {A : Alignment α} {xs ys : List α}
    (hA : IsAlignment A xs ys) (hb : IsBanded w A) :
    |(xs.length : ℤ) - (ys.length : ℤ)| ≤ (w : ℤ) := by
  have hfin := bandedFrom_final w A 0 0 hb
  rw [hA.2.1, hA.2.2] at hfin
  simpa using hfin

/-- The diagonal alignment: match the common prefix, then gap the remainder. -/
def diagAlign : List α → List α → Alignment α
  | [], ys => ys.map (fun b => (none, some b))
  | a :: xs, [] => (a :: xs).map (fun a => (some a, none))
  | a :: xs, b :: ys => (some a, some b) :: diagAlign xs ys

/-- The diagonal alignment is valid. -/
theorem isAlignment_diagAlign (xs ys : List α) :
    IsAlignment (diagAlign xs ys) xs ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => exact ⟨by simp [diagAlign], rfl, rfl⟩
      | cons b ys =>
          refine ⟨?_, ?_, ?_⟩
          · intro c hc
            simp only [diagAlign] at hc
            rw [List.mem_map] at hc
            obtain ⟨b', _, rfl⟩ := hc
            simp
          · simp only [diagAlign]
            simp [List.filterMap_map]
          · simp only [diagAlign]
            simp [List.filterMap_map]
  | cons a xs ih =>
      cases ys with
      | nil =>
          refine ⟨?_, ?_, ?_⟩
          · intro c hc
            simp only [diagAlign] at hc
            rw [List.mem_map] at hc
            obtain ⟨a', _, rfl⟩ := hc
            simp
          · simp only [diagAlign]
            simp [List.filterMap_map]
          · simp only [diagAlign]
            simp [List.filterMap_map]
      | cons b ys =>
          have ih' := ih ys
          refine ⟨?_, ?_, ?_⟩
          · intro c hc
            simp only [diagAlign] at hc
            rw [List.mem_cons] at hc
            rcases hc with rfl | hc
            · simp
            · exact ih'.1 c hc
          · simp only [diagAlign]
            simp [List.filterMap_cons, ih'.2.1]
          · simp only [diagAlign]
            simp [List.filterMap_cons, ih'.2.2]

/-- A gap-only tail in `ys` stays in the band when its endpoints do. -/
theorem bandedFrom_map_gapY : ∀ (ys : List α) (i j : ℕ),
    |(i : ℤ) - (j : ℤ)| ≤ (w : ℤ) →
    |(i : ℤ) - (j + ys.length)| ≤ (w : ℤ) →
    bandedFrom w i j (ys.map (fun b => (none, some b))) = true
  | [], i, j, h0, _ => by
      simp only [List.map_nil, bandedFrom]
      exact decide_eq_true_eq.mpr h0
  | b :: ys, i, j, h0, hend => by
      show bandedFrom w i j
        ((none, some b) :: ys.map (fun b => (none, some b))) = true
      simp only [bandedFrom, Bool.and_eq_true]
      refine ⟨decide_eq_true_eq.mpr h0, ?_⟩
      apply bandedFrom_map_gapY ys i (j + 1)
      · have hcast : ((i : ℤ) - ((j + 1 : ℕ) : ℤ))
            = ((i : ℤ) - (j : ℤ)) - (1 : ℤ) := by
          push_cast
          ring
        rw [hcast]
        exact abs_le_of_between (a := (i : ℤ) - (j : ℤ))
          (d := ((b :: ys).length : ℤ)) (t := (1 : ℤ)) (w := (w : ℤ)) h0 (by
            have hcast2 : ((i : ℤ) - (j : ℤ)) - ((b :: ys).length : ℤ)
                = (i : ℤ) - (j + (b :: ys).length) := by
              push_cast
              ring
            rw [hcast2]
            exact hend) (by norm_num) (by simp)
      · have hlen : (b :: ys).length = ys.length + 1 := rfl
        rw [hlen] at hend
        convert hend using 2
        push_cast
        ring

/-- A gap-only tail in `xs` stays in the band when its endpoints do. -/
theorem bandedFrom_map_gapX : ∀ (xs : List α) (i j : ℕ),
    |(i : ℤ) - (j : ℤ)| ≤ (w : ℤ) →
    |(i + xs.length : ℤ) - (j : ℤ)| ≤ (w : ℤ) →
    bandedFrom w i j (xs.map (fun a => (some a, none))) = true
  | [], i, j, h0, _ => by
      simp only [List.map_nil, bandedFrom]
      exact decide_eq_true_eq.mpr h0
  | a :: xs, i, j, h0, hend => by
      show bandedFrom w i j
        ((some a, none) :: xs.map (fun a => (some a, none))) = true
      simp only [bandedFrom, Bool.and_eq_true]
      refine ⟨decide_eq_true_eq.mpr h0, ?_⟩
      apply bandedFrom_map_gapX xs (i + 1) j
      · have hcast : (((i + 1 : ℕ) : ℤ) - (j : ℤ))
            = ((i : ℤ) - (j : ℤ)) + (1 : ℤ) := by
          push_cast
          ring
        rw [hcast]
        exact abs_le_of_between_add (a := (i : ℤ) - (j : ℤ))
          (d := ((a :: xs).length : ℤ)) (t := (1 : ℤ)) (w := (w : ℤ)) h0 (by
            have hcast2 : ((i : ℤ) - (j : ℤ)) + ((a :: xs).length : ℤ)
                = (i + (a :: xs).length : ℤ) - (j : ℤ) := by
              push_cast
              ring
            rw [hcast2]
            exact hend) (by norm_num) (by simp)
      · have hlen : (a :: xs).length = xs.length + 1 := rfl
        rw [hlen] at hend
        convert hend using 2
        push_cast
        ring

/-- The diagonal alignment stays in the band whenever its start and end offsets
do: the match phase keeps the difference, the gap phases interpolate it. -/
theorem bandedFrom_diagAlign : ∀ (i j : ℕ) (xs ys : List α),
    |(i : ℤ) - (j : ℤ)| ≤ (w : ℤ) →
    |(i + xs.length : ℤ) - (j + ys.length)| ≤ (w : ℤ) →
    bandedFrom w i j (diagAlign xs ys) = true
  | i, j, [], ys, h0, hend => by
      simp only [diagAlign]
      apply bandedFrom_map_gapY w ys i j h0
      simpa using hend
  | i, j, a :: xs, [], h0, hend => by
      simp only [diagAlign]
      exact bandedFrom_map_gapX w (a :: xs) i j h0 hend
  | i, j, a :: xs, b :: ys, h0, hend => by
      simp only [diagAlign, bandedFrom, Bool.and_eq_true]
      refine ⟨decide_eq_true_eq.mpr h0, ?_⟩
      apply bandedFrom_diagAlign (i + 1) (j + 1) xs ys
      · have hcast : (((i + 1 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ)) = (i : ℤ) - (j : ℤ) := by
          push_cast
          ring
        rw [hcast]
        exact h0
      · have hlen1 : (a :: xs).length = xs.length + 1 := rfl
        have hlen2 : (b :: ys).length = ys.length + 1 := rfl
        rw [hlen1, hlen2] at hend
        have hcast : (((i + 1 : ℕ) : ℤ) + xs.length - (((j + 1 : ℕ) : ℤ) + ys.length))
            = ((i : ℤ) + (xs.length + 1) - ((j : ℤ) + (ys.length + 1))) := by
          push_cast
          ring
        rw [hcast]
        exact hend

/-- The diagonal alignment is banded when the length difference fits the band. -/
theorem isBanded_diagAlign {xs ys : List α}
    (h : |(xs.length : ℤ) - (ys.length : ℤ)| ≤ (w : ℤ)) :
    IsBanded w (diagAlign xs ys) := by
  apply bandedFrom_diagAlign w 0 0 xs ys
  · simp
  · simpa using h

/-- The banded alignment score: the maximum score over banded alignments,
`none` when no banded alignment exists. -/
def bandedScore (xs ys : List α) : Option ℤ :=
  List.argmax id (((alignments xs ys).filter (fun A => bandedFrom w 0 0 A)).map
    (alignmentScore σ gap))

/-- A banded optimum is at most the unrestricted optimum. -/
theorem bandedScore_le_nwScore {xs ys : List α} {s : ℤ}
    (h : bandedScore σ gap w xs ys = some s) : s ≤ nwScore σ gap xs ys := by
  have hmem : s ∈ (((alignments xs ys).filter
      (fun A => bandedFrom w 0 0 A)).map (alignmentScore σ gap)) :=
    List.argmax_mem (Option.mem_def.2 h)
  rw [List.mem_map] at hmem
  obtain ⟨A, hA, hAscore⟩ := hmem
  rw [List.mem_filter] at hA
  obtain ⟨hAmem, -⟩ := hA
  rw [mem_alignments] at hAmem
  rw [← hAscore]
  exact alignmentScore_le_nwScore σ gap xs ys A hAmem

/-- If some optimal alignment is banded, the banded score is the optimum. -/
theorem bandedScore_eq_nwScore_of_banded_optimal {xs ys : List α}
    (h : ∃ A, IsAlignment A xs ys ∧ IsBanded w A ∧
      alignmentScore σ gap A = nwScore σ gap xs ys) :
    bandedScore σ gap w xs ys = some (nwScore σ gap xs ys) := by
  obtain ⟨A, hA, hb, hscore⟩ := h
  have hmem : A ∈ (alignments xs ys).filter (fun A => bandedFrom w 0 0 A) := by
    rw [List.mem_filter]
    exact ⟨(mem_alignments _ _ _).mpr hA, hb⟩
  have hne : (((alignments xs ys).filter
      (fun A => bandedFrom w 0 0 A)).map (alignmentScore σ gap)) ≠ [] := by
    intro hempty
    have : alignmentScore σ gap A ∈
        (((alignments xs ys).filter
          (fun A => bandedFrom w 0 0 A)).map (alignmentScore σ gap)) :=
      List.mem_map_of_mem hmem
    rw [hempty] at this
    exact absurd this (by simp)
  obtain ⟨s, hs⟩ : ∃ s, bandedScore σ gap w xs ys = some s := by
    cases harg : List.argmax id (((alignments xs ys).filter
        (fun A => bandedFrom w 0 0 A)).map (alignmentScore σ gap)) with
    | none =>
        have hempty := List.argmax_eq_none.mp harg
        exact absurd hempty hne
    | some s => exact ⟨s, harg⟩
  have hle : s ≤ nwScore σ gap xs ys := bandedScore_le_nwScore σ gap w hs
  have hge : nwScore σ gap xs ys ≤ s := by
    rw [← hscore]
    have hmem_argmax : s ∈ List.argmax id (((alignments xs ys).filter
        (fun A => bandedFrom w 0 0 A)).map (alignmentScore σ gap)) :=
      Option.mem_def.2 hs
    have hle_argmax := List.le_of_mem_argmax (f := id)
      (List.mem_map_of_mem hmem) hmem_argmax
    exact hle_argmax
  have hseq : s = nwScore σ gap xs ys := le_antisymm hle hge
  rw [hseq] at hs
  exact hs

/-- If the lengths differ by more than `w`, no banded alignment exists. -/
theorem bandedScore_none_of_length_diff_gt {xs ys : List α}
    (h : (w : ℤ) < |(xs.length : ℤ) - (ys.length : ℤ)|) :
    bandedScore σ gap w xs ys = none := by
  cases hs : bandedScore σ gap w xs ys with
  | none => rfl
  | some s =>
      exfalso
      have hmem : s ∈ (((alignments xs ys).filter
          (fun A => bandedFrom w 0 0 A)).map (alignmentScore σ gap)) :=
        List.argmax_mem (Option.mem_def.2 hs)
      rw [List.mem_map] at hmem
      obtain ⟨A, hA, -⟩ := hmem
      rw [List.mem_filter] at hA
      obtain ⟨hAmem, hb⟩ := hA
      rw [mem_alignments] at hAmem
      have hdiff := isBanded_length_diff w hAmem hb
      linarith

/-- If the lengths differ by at most `w`, a banded alignment exists. -/
theorem bandedScore_some_of_length_diff_le {xs ys : List α}
    (h : |(xs.length : ℤ) - (ys.length : ℤ)| ≤ (w : ℤ)) :
    ∃ s, bandedScore σ gap w xs ys = some s := by
  have hmem : diagAlign xs ys ∈
      (alignments xs ys).filter (fun A => bandedFrom w 0 0 A) := by
    rw [List.mem_filter]
    exact ⟨(mem_alignments _ _ _).mpr (isAlignment_diagAlign xs ys),
      isBanded_diagAlign w h⟩
  have hne : (((alignments xs ys).filter
      (fun A => bandedFrom w 0 0 A)).map (alignmentScore σ gap)) ≠ [] := by
    intro hempty
    have : alignmentScore σ gap (diagAlign xs ys) ∈
        (((alignments xs ys).filter
          (fun A => bandedFrom w 0 0 A)).map (alignmentScore σ gap)) :=
      List.mem_map_of_mem hmem
    rw [hempty] at this
    exact absurd this (by simp)
  cases harg : List.argmax id (((alignments xs ys).filter
      (fun A => bandedFrom w 0 0 A)).map (alignmentScore σ gap)) with
  | none =>
      have hempty := List.argmax_eq_none.mp harg
      exact absurd hempty hne
  | some s => exact ⟨s, harg⟩

end Banded

end Cslib.Algorithms.Lean
