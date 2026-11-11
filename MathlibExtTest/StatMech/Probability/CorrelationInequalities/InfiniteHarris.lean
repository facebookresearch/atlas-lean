/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.InfiniteHarris

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.InfiniteHarris`

On `ConfigSpace ℕ` with `openAt 0` and `openAt 1` (`IsIncreasing` and `DependsOn {0, 1}`
proved): `ih_harris_of_finite_dependsOn` at `p = 1/2`, `ih_dependsOn_inter`, and
`ih_harris_iInter_of_antitone` for constant sequences, with its stage hypothesis supplied by
`ih_harris_of_finite_dependsOn` and measurability proved.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.InfiniteHarris

open _root_.StatMech

/-- The event "coordinate `i` is open" on `ConfigSpace ℕ`. -/
def openAt (i : ℕ) : Set (ConfigSpace ℕ) := {ω | ω i = true}

-- `openAt i` is increasing.
theorem isIncreasing_openAt (i : ℕ) : IsIncreasing (openAt i) := by
  intro x y hxy hx
  have h := hxy i
  simp only [openAt, Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact top_le_iff.mp h

-- `openAt i` depends only on the finite window `{0, 1}` when `i ≤ 1`.
theorem dependsOn_openAt (i : ℕ) (hi : i ∈ ({0, 1} : Finset ℕ)) :
    _root_.StatMech.DependsOn (openAt i) (({0, 1} : Finset ℕ) : Set ℕ) := by
  intro ω ω' h
  have := h i (by exact_mod_cast hi)
  simp [openAt, this]

-- The Harris inequality on `ℕ` with all hypotheses instantiated.
example : (bernoulliProductMeasure (E := ℕ) (1 / 2) (by norm_num)).real (openAt 0)
      * (bernoulliProductMeasure (E := ℕ) (1 / 2) (by norm_num)).real (openAt 1)
    ≤ (bernoulliProductMeasure (E := ℕ) (1 / 2) (by norm_num)).real (openAt 0 ∩ openAt 1) :=
  ih_harris_of_finite_dependsOn _ {0, 1} (dependsOn_openAt 0 (by simp))
    (dependsOn_openAt 1 (by simp)) (isIncreasing_openAt 0) (isIncreasing_openAt 1)

-- `openAt i` is measurable.
theorem measurableSet_openAt (i : ℕ) : MeasurableSet (openAt i) :=
  measurableSet_eq_fun (measurable_pi_apply i) measurable_const

-- `ih_harris_iInter_of_antitone` for constant sequences.
example : (bernoulliProductMeasure (E := ℕ) (1 / 2) (by norm_num)).real (⋂ _n : ℕ, openAt 0)
      * (bernoulliProductMeasure (E := ℕ) (1 / 2) (by norm_num)).real (⋂ _n : ℕ, openAt 1)
    ≤ (bernoulliProductMeasure (E := ℕ) (1 / 2) (by norm_num)).real
      ((⋂ _n : ℕ, openAt 0) ∩ ⋂ _n : ℕ, openAt 1) :=
  ih_harris_iInter_of_antitone _ (fun _ => openAt 0) (fun _ => openAt 1) antitone_const
    antitone_const (fun _ => measurableSet_openAt 0) (fun _ => measurableSet_openAt 1)
    (fun _ => ih_harris_of_finite_dependsOn _ {0, 1} (dependsOn_openAt 0 (by simp))
      (dependsOn_openAt 1 (by simp)) (isIncreasing_openAt 0) (isIncreasing_openAt 1))

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.InfiniteHarris
