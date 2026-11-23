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
import Mathlib.Data.Fintype.Card

/-!
# Precision at a cutoff

For a finite candidate universe `Fin N`, a relevance predicate `rel`, and a
ranked prefix `r : Fin k → Fin N`, precision at `k` is the fraction of ranked
positions whose candidate is relevant. The empty cutoff is assigned value `0`
by convention.

## Main declarations

* `precisionAt`: fraction of relevant positions in a ranked prefix.
* `precisionAt_zero_cutoff`: the empty-cutoff convention.
* `precisionAt_mem_Icc`: precision lies in `[0, 1]`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.InformationRetrieval

/-- Precision at cutoff `k` for a ranked prefix `r`.

`rel` is the relevance predicate on the finite candidate universe `Fin N`.
The numerator counts relevant ranked positions. The selected convention for
an empty cutoff is `0`. -/
noncomputable def precisionAt {N k : ℕ} (rel : Fin N → Prop) [DecidablePred rel]
    (r : Fin k → Fin N) : ℝ :=
  if k = 0 then 0
  else ((Finset.univ.filter fun i => rel (r i)).card : ℝ) / (k : ℝ)

/-- Precision at an empty cutoff is zero by convention. -/
theorem precisionAt_zero_cutoff {N : ℕ} (rel : Fin N → Prop) [DecidablePred rel]
    (r : Fin 0 → Fin N) : precisionAt rel r = 0 := by
  simp [precisionAt]

/-- Precision at a cutoff lies in `[0, 1]`. -/
theorem precisionAt_mem_Icc {N k : ℕ} (rel : Fin N → Prop) [DecidablePred rel]
    (r : Fin k → Fin N) : precisionAt rel r ∈ Set.Icc (0 : ℝ) 1 := by
  unfold precisionAt
  split
  · exact Set.left_mem_Icc.mpr zero_le_one
  · rename_i hk
    have hle : (Finset.univ.filter fun i => rel (r i)).card ≤ k :=
      calc (Finset.univ.filter fun i => rel (r i)).card
          ≤ Finset.univ.card := Finset.card_filter_le _ _
        _ = k := by rw [Finset.card_univ, Fintype.card_fin]
    have hleR : ((Finset.univ.filter fun i => rel (r i)).card : ℝ) ≤ (k : ℝ) :=
      Nat.cast_le.mpr hle
    have hkpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
    refine Set.mem_Icc.mpr ⟨?_, ?_⟩
    · exact div_nonneg (Nat.cast_nonneg _) hkpos.le
    · rw [div_le_one hkpos]
      exact hleR

end Cslib.InformationRetrieval
