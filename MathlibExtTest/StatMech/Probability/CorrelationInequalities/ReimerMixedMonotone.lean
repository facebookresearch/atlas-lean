/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.ReimerMixedMonotone

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.ReimerButterfly`

On `ConfigSpace (Fin 2)`, with the increasing event `open0 = {ω | ω 0}` and the decreasing event
`closed1 = {ω | ¬ ω 1}` (both hypotheses proved):
* `disjointOccurrence_eq_inter_of_mixed`: `open0 □ closed1 = open0 ∩ closed1`, and the
  configuration `(1, 0)` lies in it;
* `reimerMixed_inequality` at `p = 1/2` and `reimerMixed_wprob` for the uniform weight;
* `wprob_fkg_pos` (Harris for product weights) and `wprob_fkg_neg`;
* `pweight_fkgLatticeCondition` for the uniform weight.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerButterfly

open _root_.StatMech

/-- The event "coordinate `0` is open" on two coordinates. -/
def open0 : Set (ConfigSpace (Fin 2)) := {ω | ω 0 = true}

-- `open0` is increasing.
theorem isIncreasing_open0 : IsIncreasing open0 := by
  intro x y hxy hx
  have h := hxy 0
  simp only [open0, Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact top_le_iff.mp h

/-- The event "coordinate `1` is closed" on two coordinates. -/
def closed1 : Set (ConfigSpace (Fin 2)) := {ω | ω 1 = false}

-- `closed1` is decreasing.
theorem isDecreasing_closed1 : IsDecreasing closed1 := by
  intro x y hxy hx
  have h := hxy 1
  simp only [closed1, Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact le_bot_iff.mp h

/-- The uniform coordinate weight. -/
noncomputable def half : Fin 2 → Bool → ℝ := fun _ _ => 1 / 2

-- `open0 □ closed1 = open0 ∩ closed1`.
example : disjointOccurrence open0 closed1 = open0 ∩ closed1 :=
  disjointOccurrence_eq_inter_of_mixed isIncreasing_open0 isDecreasing_closed1

-- The configuration `(1, 0)` lies in `open0 □ closed1`.
example : ![true, false] ∈ disjointOccurrence open0 closed1 := by
  rw [disjointOccurrence_eq_inter_of_mixed isIncreasing_open0 isDecreasing_closed1]
  exact ⟨rfl, rfl⟩

-- `reimerMixed_inequality` with every hypothesis instantiated at `p = 1/2`.
example : (bernoulliProductMeasure (E := Fin 2) (1 / 2) (by norm_num)).real
      (disjointOccurrence open0 closed1)
    ≤ (bernoulliProductMeasure (E := Fin 2) (1 / 2) (by norm_num)).real open0
      * (bernoulliProductMeasure (E := Fin 2) (1 / 2) (by norm_num)).real closed1 :=
  reimerMixed_inequality _ isIncreasing_open0 isDecreasing_closed1

-- `reimerMixed_wprob` for the uniform weight.
example : wprob half (disjointOccurrence open0 closed1) ≤ wprob half open0 * wprob half closed1 :=
  reimerMixed_wprob half (fun _ _ => by norm_num [half]) (fun _ => by norm_num [half])
    isIncreasing_open0 isDecreasing_closed1

-- `wprob_fkg_pos`: Harris for the uniform weight and the self-pair `open0, open0`.
example : wprob half open0 * wprob half open0 ≤ wprob half (open0 ∩ open0) :=
  wprob_fkg_pos half (fun _ _ => by norm_num [half]) (fun _ => by norm_num [half])
    isIncreasing_open0 isIncreasing_open0

-- `wprob_fkg_neg`: an increasing and a decreasing event are negatively correlated.
example : wprob half (open0 ∩ closed1) ≤ wprob half open0 * wprob half closed1 :=
  wprob_fkg_neg half (fun _ _ => by norm_num [half]) (fun _ => by norm_num [half])
    isIncreasing_open0 isDecreasing_closed1

-- Product weights satisfy the FKG lattice condition.
example : FKGLatticeCondition (pweight half) := pweight_fkgLatticeCondition half

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerButterfly
