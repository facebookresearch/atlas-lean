/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring

/-!
# Simultaneous min-max by pairwise comparison

Processing disjoint pairs against running extremes costs
three comparisons per pair; the final minimum and maximum
bound every processed element. The matching adversary
lower bound is not included here.
-/

@[expose] public section

/-- Simultaneous min-max by pairwise comparison (core of
ALG-02). The state after processing pairs: current minimum,
current maximum, and the comparison count. Comparisons are
counted in units where comparing two elements costs 1.
`minmaxPairs` processes a list of pairs against initial
extremes. -/
def minmaxStep (st : ℕ × ℕ × ℕ) (p : ℕ × ℕ) : ℕ × ℕ × ℕ :=
  let (lo, hi, c) := st
  let (a, b) := p
  (min lo (min a b), max hi (max a b), c + 3)

private theorem step_fst (st : ℕ × ℕ × ℕ) (p : ℕ × ℕ) :
    (minmaxStep st p).1 = min st.1 (min p.1 p.2) := by
  obtain ⟨lo, hi, c⟩ := st
  obtain ⟨a, b⟩ := p
  simp [minmaxStep]

private theorem step_snd_fst (st : ℕ × ℕ × ℕ) (p : ℕ × ℕ) :
    (minmaxStep st p).2.1 = max st.2.1 (max p.1 p.2) := by
  obtain ⟨lo, hi, c⟩ := st
  obtain ⟨a, b⟩ := p
  simp [minmaxStep]

private theorem step_snd_snd (st : ℕ × ℕ × ℕ) (p : ℕ × ℕ) :
    (minmaxStep st p).2.2 = st.2.2 + 3 := by
  obtain ⟨lo, hi, c⟩ := st
  obtain ⟨a, b⟩ := p
  simp [minmaxStep]

private theorem foldl_lo_anti (ps : List (ℕ × ℕ)) (st : ℕ × ℕ × ℕ) :
    (ps.foldl minmaxStep st).1 ≤ st.1 := by
  induction ps generalizing st with
  | nil => simp
  | cons q qs ih =>
    simp only [List.foldl_cons]
    calc (qs.foldl minmaxStep (minmaxStep st q)).1
        ≤ (minmaxStep st q).1 := ih _
      _ = min st.1 (min q.1 q.2) := step_fst st q
      _ ≤ st.1 := min_le_left _ _

private theorem foldl_hi_mono (ps : List (ℕ × ℕ)) (st : ℕ × ℕ × ℕ) :
    st.2.1 ≤ (ps.foldl minmaxStep st).2.1 := by
  induction ps generalizing st with
  | nil => simp
  | cons q qs ih =>
    simp only [List.foldl_cons]
    calc st.2.1
        ≤ (minmaxStep st q).2.1 := by
          rw [step_snd_fst st q]
          exact le_max_left _ _
      _ ≤ (qs.foldl minmaxStep (minmaxStep st q)).2.1 := ih _

private theorem foldl_lo_mem (ps : List (ℕ × ℕ)) (st : ℕ × ℕ × ℕ)
    (p : ℕ × ℕ) (hp : p ∈ ps) :
    (ps.foldl minmaxStep st).1 ≤ min p.1 p.2 := by
  induction ps generalizing st with
  | nil => simp at hp
  | cons q qs ih =>
    simp only [List.foldl_cons]
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · calc (qs.foldl minmaxStep (minmaxStep st p)).1
          ≤ (minmaxStep st p).1 := foldl_lo_anti qs _
        _ = min st.1 (min p.1 p.2) := step_fst st p
        _ ≤ min p.1 p.2 := min_le_right _ _
    · exact ih _ hp

private theorem foldl_hi_mem (ps : List (ℕ × ℕ)) (st : ℕ × ℕ × ℕ)
    (p : ℕ × ℕ) (hp : p ∈ ps) :
    max p.1 p.2 ≤ (ps.foldl minmaxStep st).2.1 := by
  induction ps generalizing st with
  | nil => simp at hp
  | cons q qs ih =>
    simp only [List.foldl_cons]
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · calc max p.1 p.2
          ≤ (minmaxStep st p).2.1 := by
            rw [step_snd_fst st p]
            exact le_max_right _ _
        _ ≤ (qs.foldl minmaxStep (minmaxStep st p)).2.1 := foldl_hi_mono qs _
    · exact ih _ hp

/-- Processing any list of pairs from `(lo, hi)` keeps `lo`
and `hi` bounding all elements: the resulting minimum is
`≤` every seen element and every initial bound... stated as:
final `lo ≤ lo₀`, final `hi ≥ hi₀`, and count grows by
exactly `3 * pairs.length`. -/
theorem minmaxStep_count (lo hi c : ℕ) (ps : List (ℕ × ℕ)) :
    (ps.foldl minmaxStep (lo, hi, c)).2.2 = c + 3 * ps.length := by
  induction ps generalizing lo hi c with
  | nil => simp
  | cons q qs ih =>
    simp only [List.foldl_cons, List.length_cons]
    have h := ih (minmaxStep (lo, hi, c) q).1 (minmaxStep (lo, hi, c) q).2.1
      (minmaxStep (lo, hi, c) q).2.2
    have heq : ((minmaxStep (lo, hi, c) q).1, (minmaxStep (lo, hi, c) q).2.1,
        (minmaxStep (lo, hi, c) q).2.2) = minmaxStep (lo, hi, c) q := by simp
    rw [← heq]
    rw [h]
    have hs : (minmaxStep (lo, hi, c) q).2.2 = c + 3 :=
      step_snd_snd (lo, hi, c) q
    rw [hs]
    ring

/-- The final minimum is at most the initial minimum and at
most both components of every processed pair. -/
theorem minmaxStep_lo_le (lo hi c : ℕ) (ps : List (ℕ × ℕ))
    (p : ℕ × ℕ) (hp : p ∈ ps) :
    (ps.foldl minmaxStep (lo, hi, c)).1 ≤ min p.1 p.2 :=
  foldl_lo_mem ps (lo, hi, c) p hp

/-- The final maximum is at least both components of every
processed pair. -/
theorem minmaxStep_hi_ge (lo hi c : ℕ) (ps : List (ℕ × ℕ))
    (p : ℕ × ℕ) (hp : p ∈ ps) :
    max p.1 p.2 ≤ (ps.foldl minmaxStep (lo, hi, c)).2.1 :=
  foldl_hi_mem ps (lo, hi, c) p hp

end
