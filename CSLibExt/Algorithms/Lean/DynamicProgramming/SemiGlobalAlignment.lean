/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.SequenceAlignment

/-!
# Semi-global and overlap alignment

Two end-gap-free variants of Needleman–Wunsch, stated as maxima of `nwScore` over
candidate lists (in the style of `suffixMax` / `localScore`):

* `overlapScore`: the best alignment of a suffix of one sequence against a prefix
  of the other (in either direction). This is the score used when two reads
  overlap partially, e.g. in genome assembly.
* `fittingScore`: the best global alignment of `xs` against a substring (infix) of
  `ys`, i.e. the pattern `xs` fitted into the text `ys` with free end gaps in `ys`.
  This is the score used when a short read is mapped into a longer reference.

Main results:

* `nwScore_le_overlapScore`, `overlapScore_le`, `exists_nwScore_eq_overlapScore`:
  the overlap score bounds, and is attained by, a suffix–prefix pair.
* `nwScore_le_fittingScore`, `fittingScore_le`, `exists_nwScore_eq_fittingScore`:
  the fitting score bounds, and is attained by, an infix of `ys`.
* `overlapScore_le_localScore`, `fittingScore_le_localScore`: both scores are at
  most the local (`Smith–Waterman`) score, since every overlap / fitting candidate
  is an infix pair.

Unlike `overlapScore`, `fittingScore` is a genuine maximum over the nonempty
infix list, not floored at `0`: it can be negative when every fitting alignment
scores negatively.

Hirschberg linear-space reconstruction, banded alignment, and multiple sequence
alignment are future work.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean

universe u

variable {α : Type u}

section SemiGlobal

variable (σ : α → α → ℤ) (gap : ℤ)

/-- **The floored list maximum is nonnegative.** For every list $L$ of integers, the maximum of
$L$ with floor $0$ (which is $0$ for the empty list) is at least $0$. -/
theorem zero_le_listMax {xs : List ℤ} : 0 ≤ listMax xs := by
  induction xs with
  | nil => exact le_rfl
  | cons a as ih =>
      show 0 ≤ max a (listMax as)
      exact le_trans ih (le_max_right _ _)


/-- Local copies of the `listMax` API: the base file keeps its helper lemmas
`private`, so the candidate-maximum lemmas here use these. -/
private theorem listMax_le_of_all_le' {xs : List ℤ} {y : ℤ}
    (h : ∀ a ∈ xs, a ≤ y) (hy : 0 ≤ y) : listMax xs ≤ y := by
  induction xs with
  | nil => exact hy
  | cons a as ih =>
    simp only [listMax, List.foldr_cons]
    exact max_le (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

private theorem le_listMax_of_mem' {xs : List ℤ} {a : ℤ} (ha : a ∈ xs) : a ≤ listMax xs := by
  induction xs with
  | nil => simp at ha
  | cons b bs ih =>
    rw [listMax, List.foldr_cons]
    cases List.mem_cons.mp ha with
    | inl h => rw [h]; exact le_max_left _ _
    | inr h => exact le_trans (ih h) (le_max_right _ _)

/-- The list maximum is `0` or an element of the list. -/
private theorem listMax_mem' {xs : List ℤ} : listMax xs ∈ 0 :: xs := by
  induction xs with
  | nil => exact List.mem_cons_self
  | cons b bs ih =>
    show max b (listMax bs) ∈ 0 :: b :: bs
    by_cases h : b ≤ listMax bs
    · rw [max_eq_right h]
      rcases List.mem_cons.mp ih with h0 | hbs
      · rw [← h0]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hbs)
    · rw [max_eq_left (le_of_not_ge h)]
      exact List.mem_cons_of_mem _ List.mem_cons_self

/-- Private `foldl max` API: the seed is itself a candidate, so unlike `listMax`
there is no `0` floor. Used for `fittingScore`, whose seed is the empty infix's
score. Stated about `List.foldl` directly (a public function) so the public
`fittingScore` can use them. -/
private theorem seed_le_foldl_max (seed : ℤ) (xs : List ℤ) :
    seed ≤ List.foldl max seed xs := by
  revert seed
  induction xs with
  | nil => intro seed; exact le_rfl
  | cons b bs ih =>
    intro seed
    simp only [List.foldl_cons]
    exact le_trans (le_max_left _ _) (ih _)

private theorem le_foldl_max_of_mem {seed a : ℤ} {xs : List ℤ} (ha : a ∈ xs) :
    a ≤ List.foldl max seed xs := by
  revert seed ha
  induction xs with
  | nil => intro seed ha; simp at ha
  | cons b bs ih =>
    intro seed ha
    simp only [List.foldl_cons]
    cases List.mem_cons.mp ha with
    | inl h => rw [h]; exact le_trans (le_max_right _ _) (seed_le_foldl_max _ _)
    | inr h => exact ih h

private theorem foldl_max_le_of_all_le {seed y : ℤ} {xs : List ℤ}
    (hseed : seed ≤ y) (h : ∀ a ∈ xs, a ≤ y) : List.foldl max seed xs ≤ y := by
  revert seed hseed h
  induction xs with
  | nil => intro seed hseed h; exact hseed
  | cons b bs ih =>
    intro seed hseed h
    simp only [List.foldl_cons]
    exact ih (max_le hseed (h b (by simp))) (fun a ha => h a (by simp [ha]))

private theorem foldl_max_eq_or_mem {seed : ℤ} {xs : List ℤ} :
    List.foldl max seed xs = seed ∨ ∃ a ∈ xs, List.foldl max seed xs = a := by
  revert seed
  induction xs with
  | nil => intro seed; left; rfl
  | cons b bs ih =>
    intro seed
    simp only [List.foldl_cons]
    rcases ih with h | ⟨a, ha, hEq⟩
    · rcases le_total seed b with hle | hle
      · right
        refine ⟨b, by simp, ?_⟩
        rw [h]
        exact max_eq_right hle
      · left
        rw [h]
        exact max_eq_left hle
    · right
      exact ⟨a, List.mem_cons_of_mem _ ha, hEq⟩

/-- **Overlap pairs.** The overlap pairs of sequences $x$ and $y$ are the pairs $(x', y')$ in
which $x'$ is a suffix of $x$ and $y'$ is a prefix of $y$, or $x'$ is a prefix of $x$ and
$y'$ is a suffix of $y$. Prefixes and suffixes include the empty sequence and the whole
sequence; the pairs are listed with the suffix–prefix pairs first, and the list can contain
repetitions. -/
def overlapPairs (xs ys : List α) : List (List α × List α) :=
  (xs.tails.product ys.inits) ++ (xs.inits.product ys.tails)

theorem mem_overlapPairs {xs' ys' xs ys : List α} :
    (xs', ys') ∈ overlapPairs xs ys ↔
      (xs' <:+ xs ∧ ys' <+: ys) ∨ (xs' <+: xs ∧ ys' <:+ ys) := by
  simp [overlapPairs, List.mem_append, List.mem_product, List.mem_tails, List.mem_inits]

/-- **Overlap alignment score.** Given a substitution score $\sigma$ and a gap score $g$, the
overlap score of sequences $s$ and $t$ is the maximum, with floor $0$, of the Needleman–Wunsch
scores of the overlap pairs of $s$ and $t$: the pairs $(s', t')$ where $s'$ is a suffix of $s$
and $t'$ a prefix of $t$, or $s'$ is a prefix of $s$ and $t'$ a suffix of $t$.

The pair of two empty sequences is an overlap pair with score $0$, so the floor never changes
the value: this is the best alignment score of a suffix of one sequence against a prefix of the
other. -/
def overlapScore (xs ys : List α) : ℤ :=
  listMax ((overlapPairs xs ys).map (fun p => nwScore σ gap p.1 p.2))

/-- **Overlap-pair scores are at most the overlap score.** Let $\sigma$ be a substitution
score and $g$ a gap score. If $(x', y')$ is an overlap pair of sequences $x$ and $y$, then the
Needleman–Wunsch score of $x'$ against $y'$ is at most the overlap score of $x$ and $y$, both
taken with $\sigma$ and $g$. -/
theorem nwScore_le_overlapScore {xs' ys' xs ys : List α}
    (h : (xs', ys') ∈ overlapPairs xs ys) :
    nwScore σ gap xs' ys' ≤ overlapScore σ gap xs ys := by
  unfold overlapScore
  apply le_listMax_of_mem'
  exact List.mem_map_of_mem h

/-- **Upper bounds for the overlap score.** Fix a substitution score $\sigma$ and a gap score
$g$, and sequences $s$ and $t$. If an integer $b$ is at least the Needleman–Wunsch score of
every overlap pair of $s$ and $t$ (a suffix of $s$ with a prefix of $t$, or a prefix of $s$
with a suffix of $t$), then the overlap score of $s$ and $t$ is at most $b$. -/
theorem overlapScore_le {xs ys : List α} {y : ℤ}
    (h : ∀ p ∈ overlapPairs xs ys, nwScore σ gap p.1 p.2 ≤ y) :
    overlapScore σ gap xs ys ≤ y := by
  unfold overlapScore
  apply listMax_le_of_all_le' _ ?_
  · intro a ha
    rw [List.mem_map] at ha
    obtain ⟨p, hp, rfl⟩ := ha
    exact h p hp
  · have h0 := h ([], [])
      (mem_overlapPairs.mpr (Or.inl ⟨List.nil_suffix (l := xs), List.nil_prefix (l := ys)⟩))
    have h00 : nwScore σ gap [] [] = 0 := rfl
    rw [h00] at h0
    exact h0

/-- **The overlap score is attained.** Let $\sigma$ be a substitution score and $g$ a gap
score. For all sequences $x$ and $y$ there is an overlap pair $(x', y')$ of $x$ and $y$ such
that the Needleman–Wunsch score of $x'$ against $y'$ (with $\sigma$ and $g$) equals the
overlap score of $x$ and $y$. -/
theorem exists_nwScore_eq_overlapScore (xs ys : List α) :
    ∃ p ∈ overlapPairs xs ys, nwScore σ gap p.1 p.2 = overlapScore σ gap xs ys := by
  have hmem := listMax_mem'
    (xs := (overlapPairs xs ys).map (fun p => nwScore σ gap p.1 p.2))
  rw [List.mem_cons] at hmem
  rcases hmem with h0 | hmem
  · refine ⟨([], []), ?_, ?_⟩
    · exact mem_overlapPairs.mpr (Or.inl ⟨List.nil_suffix (l := xs), List.nil_prefix (l := ys)⟩)
    · have h00 : nwScore σ gap [] [] = 0 := rfl
      exact h00.trans h0.symm
  · rw [List.mem_map] at hmem
    obtain ⟨p, hp, hpEq⟩ := hmem
    exact ⟨p, hp, hpEq⟩

/-- **The overlap score is nonnegative.** For every substitution score $\sigma$, gap
score $g$ and sequences $s$ and $t$, the overlap score of $s$ and $t$ is at least $0$.

The pair of two empty sequences is an overlap pair, and its score is $0$. -/
theorem overlapScore_nonneg (xs ys : List α) : 0 ≤ overlapScore σ gap xs ys :=
  zero_le_listMax

/-- **Infixes.** The infixes of a sequence $y$ are its contiguous substrings: the sequences
$l$ such that $y$ is the concatenation of $s$, $l$ and $t$ for some sequences $s$ and $t$,
including the empty sequence and $y$ itself. They are listed as the suffixes of the prefixes
of $y$, so the list can contain repetitions. -/
def infixes (ys : List α) : List (List α) :=
  ys.inits.flatMap (fun pre => pre.tails)

theorem mem_infixes {l ys : List α} : l ∈ infixes ys ↔ ∃ s t, s ++ l ++ t = ys := by
  constructor
  · intro h
    rw [infixes, List.mem_flatMap] at h
    obtain ⟨pre, hpre, hl⟩ := h
    rw [List.mem_inits] at hpre
    rw [List.mem_tails] at hl
    obtain ⟨t, ht⟩ := hpre
    obtain ⟨s, hs⟩ := hl
    exact ⟨s, t, by rw [hs]; exact ht⟩
  · rintro ⟨s, t, hst⟩
    rw [infixes, List.mem_flatMap]
    exact ⟨s ++ l, (List.mem_inits _ _).mpr ⟨t, hst⟩,
      (List.mem_tails _ _).mpr ⟨s, rfl⟩⟩

/-- **Fitting score.** Let $\sigma$ be a substitution score and $g$ a gap score. The fitting
score of a sequence $x$ against a sequence $y$ is the maximum, over all infixes $l$ of $y$
(including the empty one), of the Needleman–Wunsch score of $x$ against $l$ with $\sigma$ and
$g$: the best global alignment score of $x$ against a substring of $y$.

The empty infix is always a candidate, so the maximum is attained. Unlike the overlap score,
the fitting score is not floored at $0$: it can be negative when every fitting alignment
scores negatively. -/
def fittingScore (xs ys : List α) : ℤ :=
  ((infixes ys).map (fun l => nwScore σ gap xs l)).foldl max (nwScore σ gap xs [])

/-- **Infix scores are at most the fitting score.** Let $\sigma$ be a substitution score and
$g$ a gap score. If $l$ is an infix of a sequence $y$, then for every sequence $x$ the
Needleman–Wunsch score of $x$ against $l$ is at most the fitting score of $x$ against $y$,
both taken with $\sigma$ and $g$. -/
theorem nwScore_le_fittingScore {l xs ys : List α} (h : l ∈ infixes ys) :
    nwScore σ gap xs l ≤ fittingScore σ gap xs ys := by
  unfold fittingScore
  exact le_foldl_max_of_mem (List.mem_map_of_mem h)

/-- **Upper bounds on the fitting score.** Let $\sigma$ be a substitution score, $g$ a gap
score, $x$ and $y$ sequences and $b$ an integer. If the Needleman–Wunsch score of $x$ against
every infix of $y$ (with $\sigma$ and $g$) is at most $b$, then the fitting score of $x$
against $y$ is at most $b$. -/
theorem fittingScore_le {xs ys : List α} {y : ℤ}
    (h : ∀ l ∈ infixes ys, nwScore σ gap xs l ≤ y) :
    fittingScore σ gap xs ys ≤ y := by
  unfold fittingScore
  apply foldl_max_le_of_all_le
  · exact h [] (mem_infixes.mpr ⟨ys, [], by simp⟩)
  · intro a ha
    rw [List.mem_map] at ha
    obtain ⟨l, hl, rfl⟩ := ha
    exact h l hl

/-- **The fitting score is attained.** Let $\sigma$ be a substitution score and $g$ a gap
score. For all sequences $x$ and $y$ there is an infix $l$ of $y$ such that the
Needleman–Wunsch score of $x$ against $l$ (with $\sigma$ and $g$) equals the fitting score of
$x$ against $y$. -/
theorem exists_nwScore_eq_fittingScore (xs ys : List α) :
    ∃ l ∈ infixes ys, nwScore σ gap xs l = fittingScore σ gap xs ys := by
  have hmem := foldl_max_eq_or_mem
    (seed := nwScore σ gap xs [])
    (xs := (infixes ys).map (fun l => nwScore σ gap xs l))
  rcases hmem with h0 | ⟨a, ha, hEq⟩
  · exact ⟨[], mem_infixes.mpr ⟨ys, [], by simp⟩, h0.symm⟩
  · rw [List.mem_map] at ha
    obtain ⟨l, hl, rfl⟩ := ha
    exact ⟨l, hl, hEq.symm⟩

/-- **The overlap score is at most the local score.** Let $\sigma$ be a substitution score
and $g$ a gap score. For all sequences $x$ and $y$, the overlap score of $x$ and $y$ is at
most the local score of $x$ and $y$, both taken with $\sigma$ and $g$.

Every overlap pair is an infix pair. -/
theorem overlapScore_le_localScore (xs ys : List α) :
    overlapScore σ gap xs ys ≤ localScore σ gap xs ys := by
  apply overlapScore_le
  intro p hp
  rw [mem_overlapPairs] at hp
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact nwScore_le_localScore σ gap
      (mem_infixPairs.mpr ⟨xs, p.2, ⟨[], by simp⟩, h2, h1,
        ⟨[], by simp⟩⟩)
  · exact nwScore_le_localScore σ gap
      (mem_infixPairs.mpr ⟨p.1, ys, h1, ⟨[], by simp⟩, ⟨[], by simp⟩, h2⟩)

/-- **The fitting score is at most the local score.** Let $\sigma$ be a substitution score
and $g$ a gap score. For all sequences $x$ and $y$, the fitting score of $x$ against $y$ is at
most the local score of $x$ and $y$, both taken with $\sigma$ and $g$.

Every fitting candidate, all of $x$ against an infix of $y$, is an infix pair. -/
theorem fittingScore_le_localScore (xs ys : List α) :
    fittingScore σ gap xs ys ≤ localScore σ gap xs ys := by
  apply fittingScore_le
  intro l hl
  rw [mem_infixes] at hl
  obtain ⟨s, t, hst⟩ := hl
  exact nwScore_le_localScore σ gap
    (mem_infixPairs.mpr ⟨xs, s ++ l, ⟨[], by simp⟩, ⟨t, hst⟩, ⟨[], by simp⟩,
      ⟨s, rfl⟩⟩)

end SemiGlobal

end Cslib.Algorithms.Lean
