/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.BK

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.BK`

* `bk_inequality` (van den Berg–Kesten) is applied under the product Bernoulli(`1/2`) measure on
  `ConfigSpace (Fin 2)` to the increasing events `open0 = {ω | ω 0}` and `open1 = {ω | ω 1}`, with
  both `IsIncreasing` hypotheses proved; `open0 □ open1` is computed to be `open0 ∩ open1`, so
  the conclusion reads `P(open0 ∩ open1) ≤ P(open0) P(open1)`.
* `bk_wprob_general` is applied to the uniform weight `φ = 1/2`; `wprob` and `pweight` are
  computed (`wprob φ open0 = 1/2`, `wprob φ (open0 ∩ open1) = 1/4`), giving the concrete instance
  `1/4 ≤ 1/2 * 1/2` of BK.
* `bk_wprob` is applied with `n = 2` to the self-pair `open0, open0`.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.BK

open _root_.StatMech

/-- The event "coordinate `0` is open" on two coordinates. -/
def open0 : Set (ConfigSpace (Fin 2)) := {ω | ω 0 = true}

/-- The event "coordinate `1` is open" on two coordinates. -/
def open1 : Set (ConfigSpace (Fin 2)) := {ω | ω 1 = true}

/-- The uniform coordinate weight `φ x b = 1/2`. -/
noncomputable def half : Fin 2 → Bool → ℝ := fun _ _ => 1 / 2

-- `open0` is increasing.
theorem isIncreasing_open0 : IsIncreasing open0 := by
  intro x y hxy hx
  have h := hxy 0
  simp only [open0, Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact top_le_iff.mp h

-- `open1` is increasing.
theorem isIncreasing_open1 : IsIncreasing open1 := by
  intro x y hxy hx
  have h := hxy 1
  simp only [open1, Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact top_le_iff.mp h

-- `open0 □ open1 = open0 ∩ open1`.
theorem disjointOccurrence_open0_open1 :
    disjointOccurrence open0 open1 = open0 ∩ open1 := by
  refine subset_antisymm (disjointOccurrence_subset_inter _ _) ?_
  rintro ω ⟨h0, h1⟩
  refine ⟨{0}, {1}, by simp, ?_, ?_⟩
  · intro ω' h
    exact (h 0 rfl).trans h0
  · intro ω' h
    exact (h 1 rfl).trans h1

-- `bk_inequality` with every hypothesis instantiated: `p = 1/2` and two increasing events.
example : (bernoulliProductMeasure (E := Fin 2) (1 / 2) (by norm_num)).real (open0 ∩ open1)
    ≤ (bernoulliProductMeasure (E := Fin 2) (1 / 2) (by norm_num)).real open0
      * (bernoulliProductMeasure (E := Fin 2) (1 / 2) (by norm_num)).real open1 := by
  rw [← disjointOccurrence_open0_open1]
  exact bk_inequality _ isIncreasing_open0 isIncreasing_open1

-- `bk_inequality` at the endpoint `p = 1`.
example : (bernoulliProductMeasure (E := Fin 2) 1 le_rfl).real (disjointOccurrence open0 open1)
    ≤ (bernoulliProductMeasure (E := Fin 2) 1 le_rfl).real open0
      * (bernoulliProductMeasure (E := Fin 2) 1 le_rfl).real open1 :=
  bk_inequality _ isIncreasing_open0 isIncreasing_open1

/-- A sum over `ConfigSpace (Fin 2)` is a sum over the four configurations. -/
theorem sum_config_fin2 (f : ConfigSpace (Fin 2) → ℝ) :
    ∑ ω, f ω = f ![false, false] + f ![false, true] + f ![true, false] + f ![true, true] := by
  rw [← (finTwoArrowEquiv Bool).symm.sum_comp, Fintype.sum_prod_type]
  simp [finTwoArrowEquiv_symm_apply]
  ring

-- `pweight` of the uniform weight is `1/4` on every configuration.
example (ω : ConfigSpace (Fin 2)) : pweight half ω = 1 / 4 := by
  simp only [pweight, half, Fin.prod_univ_two]
  norm_num

-- `wprob half open0 = 1/2`.
theorem wprob_open0 : wprob half open0 = 1 / 2 := by
  rw [wprob, sum_config_fin2]
  simp [pweight, half, open0, Set.indicator]
  norm_num

-- `wprob half open1 = 1/2`.
theorem wprob_open1 : wprob half open1 = 1 / 2 := by
  rw [wprob, sum_config_fin2]
  simp [pweight, half, open1, Set.indicator]
  norm_num

-- `wprob half (open0 ∩ open1) = 1/4`.
theorem wprob_open0_inter_open1 : wprob half (open0 ∩ open1) = 1 / 4 := by
  rw [wprob, sum_config_fin2]
  simp [pweight, half, open0, open1, Set.indicator]
  norm_num

-- `bk_wprob_general` with the uniform weight; the conclusion evaluates to `1/4 ≤ 1/2 * 1/2`.
example : (1 / 4 : ℝ) ≤ 1 / 2 * (1 / 2) := by
  have h := bk_wprob_general half (fun _ _ => by norm_num [half]) (fun _ => by norm_num [half])
    isIncreasing_open0 isIncreasing_open1
  rwa [disjointOccurrence_open0_open1, wprob_open0_inter_open1, wprob_open0, wprob_open1] at h

-- `bk_wprob` with `n = 2` for the self-pair `open0, open0`.
example : wprob half (disjointOccurrence open0 open0) ≤ wprob half open0 * wprob half open0 :=
  bk_wprob 2 half (fun _ _ => by norm_num [half]) (fun _ => by norm_num [half]) open0 open0
    isIncreasing_open0 isIncreasing_open0

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.BK
