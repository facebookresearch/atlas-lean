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
and four interactions of replicate 2:

| interaction | anchor A | anchor B | gap A | gap B | corresponds (gap 0) | (gap 50) |
|---|---|---|---|---|---|---|
| `0` | `[150, 250]` | `[5050, 5150]` | -50 | -50 | yes | yes |
| `1` | `[180, 300]` | `[4900, 5010]` | -20 | -10 | yes | yes |
| `2` | `[240, 300]` | `[5120, 5200]` | 40 | 20 | no | yes |
| `3` | `[150, 250]` (chromosome `2`) | `[5050, 5150]` | — | -50 | no | no |

* the gap convention: overlapping anchors have a nonpositive gap, and a gap of `40` is within a
  maximal gap of `50` but not `0`; anchors on different chromosomes never correspond;
* with the rank sum as ambiguity-resolution value, where interaction `j` of replicate 2 has rank
  `j + 1` and the interaction of replicate 1 rank `1`, interaction `0` is the resolved partner
  among the two that overlap, and with a maximal gap of `50` too, since interaction `2` has a
  larger rank;
* with the values in the reverse order, interaction `1` is the resolved partner instead, and
  interaction `0` is not;
* the resolved partner exists and, the values being distinct, is unique;
* the single pair `(0, 0)` is a resolved correspondence. -/

open Domains.Biology.Omics.InteractionCorrespondence

namespace DomainsTest.Biology.Omics.InteractionCorrespondence

/-- The interaction of replicate 1. -/
def x₁ : Unit → Anchor ℕ × Anchor ℕ := fun _ => (⟨1, 100, 200⟩, ⟨1, 5000, 5100⟩)

/-- The four interactions of replicate 2. -/
def x₂ : Fin 4 → Anchor ℕ × Anchor ℕ :=
  ![(⟨1, 150, 250⟩, ⟨1, 5050, 5150⟩), (⟨1, 180, 300⟩, ⟨1, 4900, 5010⟩),
    (⟨1, 240, 300⟩, ⟨1, 5120, 5200⟩), (⟨2, 150, 250⟩, ⟨1, 5050, 5150⟩)]

/-- The sum of the ranks: the interaction of replicate 1 has rank `1`, interaction `j` of
replicate 2 rank `j + 1`. -/
def rankSum : Unit → Fin 4 → ℝ := fun _ j => 1 + ((j : ℕ) + 1 : ℕ)

/-- The values in the reverse order. -/
def reversed : Unit → Fin 4 → ℝ := fun _ j => -rankSum () j

theorem corresponds_zero_iff (j : Fin 4) : Corresponds 0 (x₁ ()) (x₂ j) ↔ j = 0 ∨ j = 1 := by
  fin_cases j <;> simp [Corresponds, Anchor.WithinGap, x₁, x₂]

theorem corresponds_fifty_iff (j : Fin 4) :
    Corresponds 50 (x₁ ()) (x₂ j) ↔ j = 0 ∨ j = 1 ∨ j = 2 := by
  fin_cases j <;> simp [Corresponds, Anchor.WithinGap, x₁, x₂]

example : IsResolvedPartner 0 x₁ x₂ rankSum () 0 := by
  refine ⟨(corresponds_zero_iff 0).2 (Or.inl rfl), fun j hj => ?_⟩
  rcases (corresponds_zero_iff j).1 hj with rfl | rfl <;> norm_num [rankSum]

example : IsResolvedPartner 50 x₁ x₂ rankSum () 0 := by
  refine ⟨(corresponds_fifty_iff 0).2 (Or.inl rfl), fun j hj => ?_⟩
  rcases (corresponds_fifty_iff j).1 hj with rfl | rfl | rfl <;> norm_num [rankSum]

example : IsResolvedPartner 0 x₁ x₂ reversed () 1 := by
  refine ⟨(corresponds_zero_iff 1).2 (Or.inr rfl), fun j hj => ?_⟩
  rcases (corresponds_zero_iff j).1 hj with rfl | rfl <;> norm_num [reversed, rankSum]

example : ¬IsResolvedPartner 0 x₁ x₂ reversed () 0 := by
  rintro ⟨_, h⟩
  have := h 1 ((corresponds_zero_iff 1).2 (Or.inr rfl))
  norm_num [reversed, rankSum] at this

example : ∃ j, IsResolvedPartner 0 x₁ x₂ rankSum () j :=
  exists_isResolvedPartner rankSum ⟨0, (corresponds_zero_iff 0).2 (Or.inl rfl)⟩

example {j : Fin 4} (hj : IsResolvedPartner 0 x₁ x₂ rankSum () j) : j = 0 := by
  have h0 : IsResolvedPartner 0 x₁ x₂ rankSum () 0 := by
    refine ⟨(corresponds_zero_iff 0).2 (Or.inl rfl), fun j hj => ?_⟩
    rcases (corresponds_zero_iff j).1 hj with rfl | rfl <;> norm_num [rankSum]
  refine IsResolvedPartner.unique (fun a b hab => ?_) hj h0
  have : ((a : ℕ) : ℝ) = (b : ℕ) := by simpa [rankSum] using hab
  exact Fin.ext (by exact_mod_cast this)

example : IsResolvedCorrespondence 0 x₁ x₂ rankSum {((), 0)} := by
  refine ⟨fun p hp => ?_, fun p hp q hq => ?_⟩
  · rw [Set.mem_singleton_iff] at hp
    subst hp
    refine ⟨(corresponds_zero_iff 0).2 (Or.inl rfl), fun j hj => ?_⟩
    rcases (corresponds_zero_iff j).1 hj with rfl | rfl <;> norm_num [rankSum]
  · rw [Set.mem_singleton_iff] at hp hq
    subst hp hq
    simp

end DomainsTest.Biology.Omics.InteractionCorrespondence
