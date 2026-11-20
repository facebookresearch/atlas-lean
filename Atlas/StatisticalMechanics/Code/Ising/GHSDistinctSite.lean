/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































































import Mathlib
import Code.Ising.GKS
import Code.Ising.GKS2
import Code.Ising.AizenmanBarsky

open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]















theorem ghsQFactor_single_nonneg (B : Finset V) (q : ConfigSpace V) :
    0 ≤ 1 - spinProd B q :=
  one_sub_spinProd_nonneg B q

variable (G : SimpleGraph V) [DecidableRel G.Adj]














theorem dup_single_pairing_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (A B : Finset V) :
    isingExpectation G β h (spinProd A) * isingExpectation G β h (spinProd B)
      ≤ isingExpectation G β h (spinProd (A ∆ B)) :=
  gks_second G β h hβ hh A B





















noncomputable def ghsQFactor (q : ConfigSpace V) (o x y : V) : ℝ :=
  1 - spin q x * spin q y - spin q o * spin q y - spin q o * spin q x




theorem ghsQFactor_eq (q : ConfigSpace V) (o x y : V) :
    ghsQFactor q o x y
      = 1 - spin q x * spin q y - spin q o * spin q y - spin q o * spin q x := rfl





theorem ghsQFactor_const_one (o x y : V) :
    ghsQFactor (fun _ => true) o x y = -2 := by
  unfold ghsQFactor spin
  norm_num







theorem ghsQFactor_single_flip {o x y : V} (hox : o ≠ x) (hxy : x ≠ y) :
    ghsQFactor (fun z => decide (z ≠ x)) o x y = 2 := by
  unfold ghsQFactor spin
  have ho : ((fun z => decide (z ≠ x)) o = true) := by simp [hox]
  have hx : ¬ ((fun z => decide (z ≠ x)) x = true) := by simp
  have hy : ((fun z => decide (z ≠ x)) y = true) := by simp [Ne.symm hxy]
  rw [if_pos ho, if_neg hx, if_pos hy]
  norm_num












theorem ghsQFactor_not_signDefinite {o x y : V} (hox : o ≠ x) (hxy : x ≠ y) :
    (∃ q : ConfigSpace V, ghsQFactor q o x y < 0)
      ∧ (∃ q : ConfigSpace V, 0 < ghsQFactor q o x y) := by
  refine ⟨⟨fun _ => true, ?_⟩, ⟨fun z => decide (z ≠ x), ?_⟩⟩
  · rw [ghsQFactor_const_one]; norm_num
  · rw [ghsQFactor_single_flip hox hxy]; norm_num















theorem dup_signDefinite_iff_single (B : Finset V) {o x y : V}
    (hox : o ≠ x) (hxy : x ≠ y) :
    (∀ q : ConfigSpace V, 0 ≤ 1 - spinProd B q)
      ∧ ¬ (∀ q : ConfigSpace V, 0 ≤ ghsQFactor q o x y) := by
  refine ⟨fun q => ghsQFactor_single_nonneg B q, ?_⟩
  intro hall
  obtain ⟨⟨q, hq⟩, _⟩ := ghsQFactor_not_signDefinite (o := o) (x := x) (y := y) hox hxy
  exact absurd (hall q) (not_le.mpr hq)

end Ising

end StatMech
