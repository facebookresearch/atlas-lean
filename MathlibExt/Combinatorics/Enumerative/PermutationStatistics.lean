/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Logic.Equiv.Defs

/-!
# Classical permutation statistics

Statistics of a permutation `σ` of `Fin n` in one-line notation.

* Left-to-right and right-to-left maxima and minima: `permLeftToRightMaxCount`,
  `permRightToLeftMaxCount`, `permLeftToRightMinCount`, `permRightToLeftMinCount`.
* Local statistics of three consecutive entries `σ i`, `σ (i + 1)`, `σ (i + 2)`: double ascents
  `σ i < σ (i + 1) < σ (i + 2)`, double descents `σ i > σ (i + 1) > σ (i + 2)`, peaks
  `σ i < σ (i + 1) > σ (i + 2)` and valleys `σ i > σ (i + 1) < σ (i + 2)`, as position predicates
  (`IsDoubleAscentAt`, ...) and counts (`permDoubleAscents`, ...).

## Main theorem

* `permDoubleAscents_add_permDoubleDescents_add_permPeaks_add_permValleys`: every position `i`
  with `i + 2 < n` is exactly one of the four, so the four counts sum to `n - 2`.
-/

@[expose] public section

namespace MetaMathlibExt

variable {n : ℕ}

/-! ### Left-to-right and right-to-left extrema -/

/-- The number of left-to-right maxima `lmax(σ)`: entries larger than every entry to their left.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Section 1 (statistics). -/
def permLeftToRightMaxCount (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n => ∀ j : Fin n, j < i → σ j < σ i).card

/-- The number of right-to-left maxima `rmax(σ)`: entries larger than every entry to their right.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Section 1 (statistics). -/
def permRightToLeftMaxCount (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n => ∀ j : Fin n, i < j → σ j < σ i).card

/-- The number of left-to-right minima `lmin(σ)`: entries smaller than every entry to their
left.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Section 1 (statistics). -/
def permLeftToRightMinCount (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n => ∀ j : Fin n, j < i → σ i < σ j).card

/-- The number of right-to-left minima `rmin(σ)`: entries smaller than every entry to their
right.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Section 1 (statistics). -/
def permRightToLeftMinCount (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n => ∀ j : Fin n, i < j → σ i < σ j).card

/-! ### Double ascents, double descents, peaks and valleys -/

/-- Position `i` is a double ascent of `σ`: `i + 2 < n` and `σ i < σ (i + 1) < σ (i + 2)`.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1 (`dasc`). -/
def IsDoubleAscentAt (σ : Equiv.Perm (Fin n)) (i : Fin n) : Prop :=
  ∃ h : i.val + 2 < n, σ i < σ ⟨i.val + 1, by omega⟩ ∧ σ ⟨i.val + 1, by omega⟩ < σ ⟨i.val + 2, h⟩

/-- Position `i` is a double descent of `σ`: `i + 2 < n` and `σ i > σ (i + 1) > σ (i + 2)`.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1 (`ddes`). -/
def IsDoubleDescentAt (σ : Equiv.Perm (Fin n)) (i : Fin n) : Prop :=
  ∃ h : i.val + 2 < n, σ ⟨i.val + 1, by omega⟩ < σ i ∧ σ ⟨i.val + 2, h⟩ < σ ⟨i.val + 1, by omega⟩

/-- Position `i` is a peak of `σ`: `i + 2 < n` and `σ i < σ (i + 1) > σ (i + 2)`.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1 (`pk`). -/
def IsPeakAt (σ : Equiv.Perm (Fin n)) (i : Fin n) : Prop :=
  ∃ h : i.val + 2 < n, σ i < σ ⟨i.val + 1, by omega⟩ ∧ σ ⟨i.val + 2, h⟩ < σ ⟨i.val + 1, by omega⟩

/-- Position `i` is a valley of `σ`: `i + 2 < n` and `σ i > σ (i + 1) < σ (i + 2)`.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1 (`vl`). -/
def IsValleyAt (σ : Equiv.Perm (Fin n)) (i : Fin n) : Prop :=
  ∃ h : i.val + 2 < n, σ ⟨i.val + 1, by omega⟩ < σ i ∧ σ ⟨i.val + 1, by omega⟩ < σ ⟨i.val + 2, h⟩

instance (σ : Equiv.Perm (Fin n)) : DecidablePred (IsDoubleAscentAt σ) := fun _ => by
  unfold IsDoubleAscentAt; infer_instance

instance (σ : Equiv.Perm (Fin n)) : DecidablePred (IsDoubleDescentAt σ) := fun _ => by
  unfold IsDoubleDescentAt; infer_instance

instance (σ : Equiv.Perm (Fin n)) : DecidablePred (IsPeakAt σ) := fun _ => by
  unfold IsPeakAt; infer_instance

instance (σ : Equiv.Perm (Fin n)) : DecidablePred (IsValleyAt σ) := fun _ => by
  unfold IsValleyAt; infer_instance

/-- `dasc σ`: the number of double ascents of `σ`.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1 (`dasc`). -/
def permDoubleAscents (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter (IsDoubleAscentAt σ)).card

/-- `ddes σ`: the number of double descents of `σ`.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1 (`ddes`). -/
def permDoubleDescents (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter (IsDoubleDescentAt σ)).card

/-- `pk σ`: the number of peaks of `σ`.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1 (`pk`). -/
def permPeaks (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter (IsPeakAt σ)).card

/-- `vl σ`: the number of valleys of `σ`.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1 (`vl`). -/
def permValleys (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter (IsValleyAt σ)).card

/-- The positions `i` with `i + 2 < n`, the possible positions of the four local statistics, number
`n - 2`.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1. -/
theorem card_filter_add_two_lt (n : ℕ) :
    (Finset.univ.filter fun i : Fin n => i.val + 2 < n).card = n - 2 := by
  rw [Finset.card_filter, Fin.sum_univ_eq_sum_range (fun i => if i + 2 < n then 1 else 0),
    ← Finset.card_filter]
  have : (Finset.range n).filter (fun i => i + 2 < n) = Finset.range (n - 2) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [this, Finset.card_range]

/-- Every position `i` with `i + 2 < n` is exactly one of a double ascent, a double descent, a peak
or a valley, and no other position is any of them.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1. -/
theorem ite_isDoubleAscentAt_add_ite_isDoubleDescentAt_add_ite_isPeakAt_add_ite_isValleyAt
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    ((if IsDoubleAscentAt σ i then 1 else 0) + (if IsDoubleDescentAt σ i then 1 else 0) +
        (if IsPeakAt σ i then 1 else 0) + (if IsValleyAt σ i then 1 else 0) : ℕ) =
      if i.val + 2 < n then 1 else 0 := by
  by_cases h : i.val + 2 < n
  · have hab : σ i ≠ σ ⟨i.val + 1, by omega⟩ := fun e => by
      have := congrArg Fin.val (σ.injective e); simp at this
    have hbc : σ ⟨i.val + 1, by omega⟩ ≠ σ ⟨i.val + 2, h⟩ := fun e => by
      have := congrArg Fin.val (σ.injective e); simp at this
    simp only [IsDoubleAscentAt, IsDoubleDescentAt, IsPeakAt, IsValleyAt, h, exists_true_left]
    rcases lt_or_gt_of_ne hab with hab | hab <;> rcases lt_or_gt_of_ne hbc with hbc | hbc <;>
      simp [hab, hbc, hab.asymm, hbc.asymm]
  · simp [IsDoubleAscentAt, IsDoubleDescentAt, IsPeakAt, IsValleyAt, h]

/-- The four local statistics partition the positions `i` with `i + 2 < n`:
`dasc σ + ddes σ + pk σ + vl σ = n - 2`.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1. -/
theorem permDoubleAscents_add_permDoubleDescents_add_permPeaks_add_permValleys
    (σ : Equiv.Perm (Fin n)) :
    permDoubleAscents σ + permDoubleDescents σ + permPeaks σ + permValleys σ = n - 2 := by
  simp only [permDoubleAscents, permDoubleDescents, permPeaks, permValleys, Finset.card_filter,
    ← Finset.sum_add_distrib,
    ite_isDoubleAscentAt_add_ite_isDoubleDescentAt_add_ite_isPeakAt_add_ite_isValleyAt]
  rw [← Finset.card_filter, card_filter_add_two_lt]

end MetaMathlibExt
