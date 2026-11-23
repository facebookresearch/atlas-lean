/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Interval.Set.Basic

import Mathlib.Algebra.Order.GroupWithZero.Basic

/-!
# Recall at a cutoff

For a finite candidate universe `Fin N`, a relevance predicate `rel`, and a
ranked prefix `r : Fin k → Fin N`, recall at `k` is the number of relevant
ranked positions divided by the number of relevant candidates in the whole
universe. When there are no relevant candidates, recall is assigned value `0`
by convention.

## Main declarations

* `recallAt`: relevant ranked positions over all relevant candidates.
* `recallAt_eq_zero_of_no_relevant`: the no-relevant-candidates convention.
* `recallAt_mem_Icc`: recall lies in `[0, 1]` for an injective ranked prefix.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.InformationRetrieval

/-- Recall at cutoff `k` for a ranked prefix `r`.

`rel` is the relevance predicate on the finite candidate universe `Fin N`.
The numerator counts relevant ranked positions and the denominator counts all
relevant candidates. The selected convention when there are no relevant
candidates is `0`. The upper-bound theorem uses the standard ranked-prefix
condition that `r` is injective. -/
noncomputable def recallAt {N k : ℕ} (rel : Fin N → Prop) [DecidablePred rel]
    (r : Fin k → Fin N) : ℝ :=
  if (Finset.univ.filter rel).card = 0 then 0
  else ((Finset.univ.filter fun i => rel (r i)).card : ℝ) /
    ((Finset.univ.filter rel).card : ℝ)

/-- Recall is zero by convention when there are no relevant candidates. -/
theorem recallAt_eq_zero_of_no_relevant {N k : ℕ} (rel : Fin N → Prop)
    [DecidablePred rel] (r : Fin k → Fin N)
    (hrel : (Finset.univ.filter rel).card = 0) : recallAt rel r = 0 := by
  simp [recallAt, hrel]

/-- Recall at a cutoff lies in `[0, 1]` for an injective ranked prefix. -/
theorem recallAt_mem_Icc {N k : ℕ} (rel : Fin N → Prop) [DecidablePred rel]
    {r : Fin k → Fin N} (hr : Function.Injective r) :
    recallAt rel r ∈ Set.Icc (0 : ℝ) 1 := by
  unfold recallAt
  split_ifs with h
  · exact Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩
  · have hcard : (Finset.univ.filter fun i => rel (r i)).card ≤
        (Finset.univ.filter rel).card := by
      have hsub : Finset.image r (Finset.univ.filter fun i => rel (r i)) ⊆
          Finset.univ.filter rel := by
        intro y hy
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
          true_and] at hy ⊢
        obtain ⟨i, hi, rfl⟩ := hy
        exact hi
      have hle := Finset.card_le_card hsub
      rwa [Finset.card_image_of_injective _ hr] at hle
    have hpos : (0 : ℝ) < ((Finset.univ.filter rel).card : ℝ) :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero h)
    have hle : ((Finset.univ.filter fun i => rel (r i)).card : ℝ) ≤
        ((Finset.univ.filter rel).card : ℝ) := Nat.cast_le.mpr hcard
    refine Set.mem_Icc.mpr ⟨?_, ?_⟩
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · exact (div_le_one hpos).mpr hle

end Cslib.InformationRetrieval
