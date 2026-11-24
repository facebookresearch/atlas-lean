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

/-- **Number of left-to-right maxima.** For a permutation $\sigma$ of $\{0, 1, \dots, n-1\}$,
$\mathrm{lmax}(\sigma)$ is the number of positions $i$ such that $\sigma(j) < \sigma(i)$ for
every position $j < i$, that is, the number of entries larger than every entry to their left.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Section 1 (statistics). -/
def permLeftToRightMaxCount (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n => ∀ j : Fin n, j < i → σ j < σ i).card

/-- **Number of right-to-left maxima.** For a permutation $\sigma$ of $\{0, 1, \dots, n - 1\}$
written in one-line notation, $\operatorname{rmax}(\sigma)$ is the number of positions $i$ such
that $\sigma(j) < \sigma(i)$ for every position $j > i$, that is, the number of entries larger
than every entry to their right.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Section 1 (statistics). -/
def permRightToLeftMaxCount (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n => ∀ j : Fin n, i < j → σ j < σ i).card

/-- **Number of left-to-right minima.** For a permutation $\sigma$ of $\{0, 1, \dots, n - 1\}$
written in one-line notation, $\operatorname{lmin}(\sigma)$ is the number of positions $i$ such
that $\sigma(i) < \sigma(j)$ for every position $j < i$, that is, the number of entries smaller
than every entry to their left.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Section 1 (statistics). -/
def permLeftToRightMinCount (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n => ∀ j : Fin n, j < i → σ i < σ j).card

/-- **Number of right-to-left minima.** For a permutation $\sigma$ of $\{0, 1, \dots, n - 1\}$
written in one-line notation, $\operatorname{rmin}(\sigma)$ is the number of positions $i$ such
that $\sigma(i) < \sigma(j)$ for every position $j > i$, that is, the number of entries smaller
than every entry to their right.

Source: Dan Li and Sergey Kitaev, *King Permutations and Partially Ordered Patterns*,
INTEGERS 26 (2026), Article A59, Section 1 (statistics). -/
def permRightToLeftMinCount (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n => ∀ j : Fin n, i < j → σ i < σ j).card

/-! ### Double ascents, double descents, peaks and valleys -/

/-- **Double ascent of a permutation.** Let $\sigma$ be a permutation of $\{0, 1, \dots, n-1\}$.
A position $i$ is a double ascent of $\sigma$ if $i + 2 < n$ and
$\sigma(i) < \sigma(i+1) < \sigma(i+2)$.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1 (`dasc`). -/
def IsDoubleAscentAt (σ : Equiv.Perm (Fin n)) (i : Fin n) : Prop :=
  ∃ h : i.val + 2 < n, σ i < σ ⟨i.val + 1, by omega⟩ ∧ σ ⟨i.val + 1, by omega⟩ < σ ⟨i.val + 2, h⟩

/-- **Double descent of a permutation.** Let $\sigma$ be a permutation of $\{0, 1, \dots, n-1\}$.
A position $i$ is a double descent of $\sigma$ if $i + 2 < n$ and
$\sigma(i) > \sigma(i+1) > \sigma(i+2)$.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1 (`ddes`). -/
def IsDoubleDescentAt (σ : Equiv.Perm (Fin n)) (i : Fin n) : Prop :=
  ∃ h : i.val + 2 < n, σ ⟨i.val + 1, by omega⟩ < σ i ∧ σ ⟨i.val + 2, h⟩ < σ ⟨i.val + 1, by omega⟩

/-- **Peak of a permutation.** Let $\sigma$ be a permutation of $\{0, 1, \dots, n-1\}$.
A position $i$ is a peak of $\sigma$ if $i + 2 < n$ and $\sigma(i) < \sigma(i+1) > \sigma(i+2)$.
Thus the peak entry is $\sigma(i+1)$, and the position recorded is $i$, that of the first of
the three entries.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1 (`pk`). -/
def IsPeakAt (σ : Equiv.Perm (Fin n)) (i : Fin n) : Prop :=
  ∃ h : i.val + 2 < n, σ i < σ ⟨i.val + 1, by omega⟩ ∧ σ ⟨i.val + 2, h⟩ < σ ⟨i.val + 1, by omega⟩

/-- **Valley of a permutation.** Let $\sigma$ be a permutation of $\{0, 1, \dots, n-1\}$.
A position $i$ is a valley of $\sigma$ if $i + 2 < n$ and
$\sigma(i) > \sigma(i+1) < \sigma(i+2)$. Thus the valley entry is $\sigma(i+1)$, and the
position recorded is $i$, that of the first of the three entries.

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

/-- **Number of double ascents.** For a permutation $\sigma$ of $\{0, 1, \dots, n-1\}$,
$\mathrm{dasc}(\sigma)$ is the number of positions $i$ that are double ascents of $\sigma$.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1 (`dasc`). -/
def permDoubleAscents (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter (IsDoubleAscentAt σ)).card

/-- **Number of double descents.** For a permutation $\sigma$ of $\{0, 1, \dots, n-1\}$,
$\mathrm{ddes}(\sigma)$ is the number of positions $i$ that are double descents of $\sigma$.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1 (`ddes`). -/
def permDoubleDescents (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter (IsDoubleDescentAt σ)).card

/-- **Number of peaks of a permutation.** For a permutation $\sigma$ of $\{0, 1, \dots, n - 1\}$
written in one-line notation, $\operatorname{pk}(\sigma)$ is the number of positions $i$ with
$i + 2 < n$ and $\sigma(i) < \sigma(i + 1) > \sigma(i + 2)$, that is, the number of peaks of
$\sigma$.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1 (`pk`). -/
def permPeaks (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter (IsPeakAt σ)).card

/-- **Number of valleys of a permutation.** For a permutation $\sigma$ of
$\{0, 1, \dots, n - 1\}$ written in one-line notation, $\operatorname{vl}(\sigma)$ is the number
of positions $i$ with $i + 2 < n$ and $\sigma(i) > \sigma(i + 1) < \sigma(i + 2)$, that is, the
number of valleys of $\sigma$.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1 (`vl`). -/
def permValleys (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter (IsValleyAt σ)).card

/-- **Number of positions with two successors.** For every natural number $n$, exactly $n - 2$ of
the positions $i \in \{0, 1, \dots, n-1\}$ satisfy $i + 2 < n$, where $n - 2$ is truncated
subtraction (it is $0$ when $n < 2$).

These are the positions at which a permutation of $\{0, 1, \dots, n-1\}$ can have a double
ascent, a double descent, a peak or a valley.

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

/-- **Local shape of a position in a permutation.** Let $\sigma$ be a permutation of
$\{0, 1, \dots, n-1\}$ and let $i$ be a position. If $i + 2 < n$, then $i$ is exactly one of a
double ascent, a double descent, a peak or a valley of $\sigma$; otherwise $i$ is none of them.
That is, the number of these four properties that $i$ has is $1$ when $i + 2 < n$ and $0$
otherwise.

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

/-- **Sum of the four local statistics of a permutation.** Let $\sigma$ be a permutation of
$\{0, 1, \dots, n-1\}$, and write $\mathrm{dasc}(\sigma)$, $\mathrm{ddes}(\sigma)$,
$\mathrm{pk}(\sigma)$ and $\mathrm{vl}(\sigma)$ for its numbers of double ascents, double
descents, peaks and valleys. Then
$\mathrm{dasc}(\sigma) + \mathrm{ddes}(\sigma) + \mathrm{pk}(\sigma) + \mathrm{vl}(\sigma) = n - 2$,
where $n - 2$ is truncated subtraction (it is $0$ when $n < 2$).

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
