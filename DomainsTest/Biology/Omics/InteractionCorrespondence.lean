/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Omics.InteractionCorrespondence
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Tests for corresponding genomic interactions between two replicates.

One interaction of replicate 1, with anchors `[100, 200]` and `[5000, 5100]` on chromosome `1`,
and four interactions of replicate 2, with the gaps `max start - min stop - 1` of their anchors to
those of the interaction of replicate 1:

| interaction | anchor A | anchor B | gap A | gap B | corresponds (gap -1) | (gap 50) |
|---|---|---|---|---|---|---|
| `0` | `[150, 250]` | `[5050, 5150]` | -51 | -51 | yes | yes |
| `1` | `[180, 300]` | `[4900, 5010]` | -21 | -11 | yes | yes |
| `2` | `[240, 300]` | `[5120, 5200]` | 39 | 19 | no | yes |
| `3` | `[150, 250]` (chromosome `2`) | `[5050, 5150]` | — | -51 | no | no |

* the gap convention: overlapping anchors have a negative gap; a maximal gap of `-1`, IDR2D's
  default, asks for overlap; anchors that share one position have gap `-1`, adjacent anchors gap
  `0`, and a gap of `39` is within a maximal gap of `50`; anchors on different chromosomes never
  correspond;
* with the rank sum as ambiguity-resolution value, where interaction `j` of replicate 2 has rank
  `j + 1` and the interaction of replicate 1 rank `1`, interaction `0` is the resolved partner
  among the two that overlap, and with a maximal gap of `50` too, since interaction `2` has a
  larger rank;
* with the values in the reverse order, interaction `1` is the resolved partner instead, and
  interaction `0` is not;
* the resolved partner exists and, the values being distinct, is unique;
* the single pair `(0, 0)` is a resolved correspondence, and the empty set is not, as the
  interaction of replicate 1 has corresponding interactions and no competitor; a resolved
  correspondence exists. -/

open Domains.Biology.Omics.InteractionCorrespondence

namespace DomainsTest.Biology.Omics.InteractionCorrespondence

/-- The interaction of replicate 1. -/
def x₁ : Unit → Anchor ℕ × Anchor ℕ :=
  fun _ => (⟨1, 100, 200, by norm_num⟩, ⟨1, 5000, 5100, by norm_num⟩)

/-- The four interactions of replicate 2. -/
def x₂ : Fin 4 → Anchor ℕ × Anchor ℕ :=
  ![(⟨1, 150, 250, by norm_num⟩, ⟨1, 5050, 5150, by norm_num⟩),
    (⟨1, 180, 300, by norm_num⟩, ⟨1, 4900, 5010, by norm_num⟩),
    (⟨1, 240, 300, by norm_num⟩, ⟨1, 5120, 5200, by norm_num⟩),
    (⟨2, 150, 250, by norm_num⟩, ⟨1, 5050, 5150, by norm_num⟩)]

/-! ### The gap convention -/

/-- Anchors sharing one position overlap: their gap is `-1`. -/
example : Anchor.WithinGap (-1) (⟨1, 100, 200, by norm_num⟩ : Anchor ℕ)
    ⟨1, 200, 300, by norm_num⟩ := by
  norm_num [Anchor.WithinGap]

/-- Adjacent anchors have gap `0`: within a maximal gap of `0`, but not of `-1`. -/
example : Anchor.WithinGap 0 (⟨1, 100, 200, by norm_num⟩ : Anchor ℕ)
    ⟨1, 201, 300, by norm_num⟩ ∧
    ¬Anchor.WithinGap (-1) (⟨1, 100, 200, by norm_num⟩ : Anchor ℕ) ⟨1, 201, 300, by norm_num⟩ := by
  norm_num [Anchor.WithinGap]

theorem corresponds_overlap_iff (j : Fin 4) :
    Corresponds (-1) (x₁ ()) (x₂ j) ↔ j = 0 ∨ j = 1 := by
  fin_cases j <;> simp [Corresponds, Anchor.WithinGap, x₁, x₂]

theorem corresponds_fifty_iff (j : Fin 4) :
    Corresponds 50 (x₁ ()) (x₂ j) ↔ j = 0 ∨ j = 1 ∨ j = 2 := by
  fin_cases j <;> simp [Corresponds, Anchor.WithinGap, x₁, x₂]

/-! ### Ambiguity resolution -/

/-- The sum of the ranks: the interaction of replicate 1 has rank `1`, interaction `j` of
replicate 2 rank `j + 1`. -/
def rankSum : Unit → Fin 4 → ℝ := fun _ j => 1 + ((j : ℕ) + 1 : ℕ)

/-- The values in the reverse order. -/
def reversed : Unit → Fin 4 → ℝ := fun _ j => -rankSum () j

theorem isResolvedPartner_rankSum_zero : IsResolvedPartner (-1) x₁ x₂ rankSum () 0 := by
  refine ⟨(corresponds_overlap_iff 0).2 (Or.inl rfl), fun j hj => ?_⟩
  rcases (corresponds_overlap_iff j).1 hj with rfl | rfl <;> norm_num [rankSum]

example : IsResolvedPartner 50 x₁ x₂ rankSum () 0 := by
  refine ⟨(corresponds_fifty_iff 0).2 (Or.inl rfl), fun j hj => ?_⟩
  rcases (corresponds_fifty_iff j).1 hj with rfl | rfl | rfl <;> norm_num [rankSum]

example : IsResolvedPartner (-1) x₁ x₂ reversed () 1 := by
  refine ⟨(corresponds_overlap_iff 1).2 (Or.inr rfl), fun j hj => ?_⟩
  rcases (corresponds_overlap_iff j).1 hj with rfl | rfl <;> norm_num [reversed, rankSum]

example : ¬IsResolvedPartner (-1) x₁ x₂ reversed () 0 := by
  rintro ⟨_, h⟩
  have := h 1 ((corresponds_overlap_iff 1).2 (Or.inr rfl))
  norm_num [reversed, rankSum] at this

example : ∃ j, IsResolvedPartner (-1) x₁ x₂ rankSum () j :=
  exists_isResolvedPartner rankSum ⟨0, (corresponds_overlap_iff 0).2 (Or.inl rfl)⟩

example {j : Fin 4} (hj : IsResolvedPartner (-1) x₁ x₂ rankSum () j) : j = 0 := by
  refine IsResolvedPartner.unique (fun a b hab => ?_) hj isResolvedPartner_rankSum_zero
  have : ((a : ℕ) : ℝ) = (b : ℕ) := by simpa [rankSum] using hab
  exact Fin.ext (by exact_mod_cast this)

/-! ### Resolved correspondences -/

example : IsResolvedCorrespondence (-1) x₁ x₂ rankSum {((), 0)} := by
  refine ⟨fun p hp => ?_, fun p hp q hq => ?_, fun i _ => Or.inl ⟨0, rfl⟩⟩
  · rw [Set.mem_singleton_iff] at hp
    subst hp
    exact isResolvedPartner_rankSum_zero
  · rw [Set.mem_singleton_iff] at hp hq
    subst hp hq
    simp

/-- The empty set pairs nothing, though the interaction of replicate 1 has corresponding
interactions of replicate 2 and no competitor for them. -/
example : ¬IsResolvedCorrespondence (-1) x₁ x₂ rankSum ∅ := by
  rintro ⟨-, -, h⟩
  rcases h () ⟨0, (corresponds_overlap_iff 0).2 (Or.inl rfl)⟩ with ⟨_, h⟩ | ⟨_, -, _, h⟩ <;>
    simp at h

example : ∃ P, IsResolvedCorrespondence 50 x₁ x₂ rankSum P :=
  exists_isResolvedCorrespondence 50 x₁ x₂ rankSum

end DomainsTest.Biology.Omics.InteractionCorrespondence
