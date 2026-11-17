/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Expected project duration versus path means

## i. Overview

For a finite nonempty family of paths, each a multiset of jobs with
integrable real durations, the expected longest path duration is at
least the largest expected path duration. Dependence between jobs is
arbitrary; no independence or integer-time model is assumed.

## ii. Key results

- `ExpectedDuration.integral_sup_pathDuration_ge`: the bound.

## iii. Table of contents

- A. Path durations

## iv. References

- Critical-path method background: J. E. Kelley and M. R. Walker,
  critical-path planning and scheduling, 1959 (expected-maximum form
  as stated here).

## A. Path durations
-/

@[expose] public section

namespace ExpectedDuration

open MeasureTheory

/-- Duration of path `p`: the sum of its job durations over the job
list `path p`, counting each listed occurrence (multiset sum). -/
noncomputable def pathDuration {ι κ Ω : Type*} (D : κ → Ω → ℝ)
    (path : ι → Multiset κ) (p : ι) (ω : Ω) : ℝ :=
  ((path p).map fun j => D j ω).sum

theorem integrable_multiset_sum {κ Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (D : κ → Ω → ℝ) (hD : ∀ j : κ, Integrable (D j) μ)
    (m : Multiset κ) :
    Integrable (fun ω => (m.map fun j => D j ω).sum) μ := by
  refine Multiset.induction_on m ?_ ?_
  · simp only [Multiset.map_zero, Multiset.sum_zero]
    exact integrable_zero _ _ _
  · intro a s ih
    simp only [Multiset.map_cons, Multiset.sum_cons]
    exact (hD a).add ih

theorem integral_multiset_sum {κ Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (D : κ → Ω → ℝ) (hD : ∀ j : κ, Integrable (D j) μ)
    (m : Multiset κ) :
    (∫ ω, (m.map fun j => D j ω).sum ∂μ)
      = (m.map fun j => ∫ ω, D j ω ∂μ).sum := by
  refine Multiset.induction_on m ?_ ?_
  · simp only [Multiset.map_zero, Multiset.sum_zero]
    exact integral_zero _ _
  · intro a s ih
    simp only [Multiset.map_cons, Multiset.sum_cons]
    rw [integral_add (hD a) (integrable_multiset_sum μ D hD s), ih]

theorem bddAbove_range_pathDuration {ι κ Ω : Type*} [MeasurableSpace Ω]
    [Fintype ι] (D : κ → Ω → ℝ) (path : ι → Multiset κ) (ω : Ω) :
    BddAbove (Set.range fun p : ι => pathDuration D path p ω) := by
  have hfin : (Set.range fun p : ι => pathDuration D path p ω).Finite := by
    rw [← Set.image_univ]
    exact Set.finite_univ.image _
  exact hfin.bddAbove

theorem integrable_sup'_pathDuration {ι κ Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (D : κ → Ω → ℝ) (path : ι → Multiset κ)
    (hD : ∀ j : κ, Integrable (D j) μ) (s : Finset ι) :
    ∀ H : s.Nonempty,
      Integrable (fun ω => s.sup' H (fun p => pathDuration D path p ω)) μ := by
  classical
  have hInt : ∀ p : ι, Integrable (fun ω => pathDuration D path p ω) μ :=
    fun p => integrable_multiset_sum μ D hD (path p)
  refine Finset.induction_on s ?_ ?_
  · intro H
    exact absurd H Finset.not_nonempty_empty
  · intro b t _hbt ih H
    by_cases ht : t.Nonempty
    · have heq : (fun ω => Finset.sup' (insert b t) H (fun p => pathDuration D path p ω))
          = fun ω => pathDuration D path b ω ⊔ t.sup' ht (fun p => pathDuration D path p ω) := by
        funext ω
        exact Finset.sup'_insert ht _
      rw [heq]
      exact (hInt b).sup (ih ht)
    · have hs0 : t = ∅ := Finset.eq_empty_of_forall_notMem (fun x hx => ht ⟨x, hx⟩)
      subst hs0
      have heq : (fun ω => Finset.sup' (insert b ∅) H (fun p => pathDuration D path p ω))
          = fun ω => pathDuration D path b ω := by
        funext ω
        exact Finset.sup'_singleton _
      rw [heq]
      exact hInt b

theorem integrable_iSup_pathDuration {ι κ Ω : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] (μ : Measure Ω) (D : κ → Ω → ℝ)
    (path : ι → Multiset κ) (hD : ∀ j : κ, Integrable (D j) μ) :
    Integrable (fun ω => ⨆ p : ι, pathDuration D path p ω) μ := by
  classical
  have Huniv : (Finset.univ : Finset ι).Nonempty :=
    Finset.univ_nonempty_iff.mpr inferInstance
  have hconn : (fun ω => ⨆ p : ι, pathDuration D path p ω)
      = fun ω => Finset.univ.sup' Huniv (fun p => pathDuration D path p ω) := by
    funext ω
    apply le_antisymm
    · exact ciSup_le fun p =>
        Finset.le_sup' (fun p => pathDuration D path p ω) (Finset.mem_univ p)
    · have hb := bddAbove_range_pathDuration D path ω
      have gen : ∀ (s : Finset ι) (H' : s.Nonempty),
          s.sup' H' (fun p => pathDuration D path p ω)
            ≤ ⨆ p : ι, pathDuration D path p ω := by
        intro s
        refine Finset.induction_on s ?_ ?_
        · intro H'
          exact absurd H' Finset.not_nonempty_empty
        · intro b t _hbt ih H'
          by_cases ht : t.Nonempty
          · rw [Finset.sup'_insert ht (fun p => pathDuration D path p ω)]
            exact sup_le (le_ciSup hb b) (ih ht)
          · have hs0 : t = ∅ := Finset.eq_empty_of_forall_notMem (fun x hx => ht ⟨x, hx⟩)
            subst hs0
            have hsing : Finset.sup' (insert b ∅) H' (fun p => pathDuration D path p ω)
                = pathDuration D path b ω := Finset.sup'_singleton _
            rw [hsing]
            exact le_ciSup hb b
      exact gen _ Huniv
  rw [hconn]
  exact integrable_sup'_pathDuration μ D path hD _ Huniv

/-- Expected-maximum lower bound: for a finite nonempty family of paths
of integrable job durations, the expected longest path duration is at
least the largest expected path duration, which is the largest sum of
expected job durations over the listed jobs. Dependence between jobs
is arbitrary. -/
theorem integral_sup_pathDuration_ge {ι κ Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Fintype ι] [Nonempty ι]
    (D : κ → Ω → ℝ) (path : ι → Multiset κ)
    (hD : ∀ j : κ, Integrable (D j) μ) :
    (∫ ω, ⨆ p : ι, pathDuration D path p ω ∂μ)
      ≥ ⨆ p : ι, ((path p).map fun j => ∫ ω, D j ω ∂μ).sum := by
  have hInt : ∀ p : ι, Integrable (fun ω => pathDuration D path p ω) μ :=
    fun p => integrable_multiset_sum μ D hD (path p)
  have hSup : Integrable (fun ω => ⨆ p : ι, pathDuration D path p ω) μ :=
    integrable_iSup_pathDuration μ D path hD
  have hle : ∀ p : ι, (∫ ω, pathDuration D path p ω ∂μ)
      ≤ ∫ ω, (⨆ p' : ι, pathDuration D path p' ω) ∂μ := by
    intro p
    apply integral_mono (hInt p) hSup
    intro ω
    exact le_ciSup (bddAbove_range_pathDuration D path ω) p
  apply ciSup_le
  intro p
  rw [← integral_multiset_sum μ D hD (path p)]
  exact hle p

end ExpectedDuration
