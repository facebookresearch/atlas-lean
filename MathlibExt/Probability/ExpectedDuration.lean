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
import Mathlib.Data.Fintype.Order
import Mathlib.MeasureTheory.Function.L1Space.Integrable

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

- Historical background only: J. E. Kelley and M. R. Walker,
  critical-path planning and scheduling, 1959 (deterministic CPM;
  the stochastic inequality here is the elementary integral bound
  proved in this module).

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

theorem integrable_ms_sum {κ Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : κ → Ω → ℝ) (hD : ∀ j : κ, Integrable (D j) μ) (m : Multiset κ) :
    Integrable (fun ω => (m.map fun j => D j ω).sum) μ := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    exact (hD a).add ih

theorem integral_ms_sum {κ Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : κ → Ω → ℝ) (hD : ∀ j : κ, Integrable (D j) μ) (m : Multiset κ) :
    (∫ ω, (m.map fun j => D j ω).sum ∂μ)
      = (m.map fun j => ∫ ω, D j ω ∂μ).sum := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    rw [integral_add (hD a) (integrable_ms_sum μ D hD s), ih]

theorem integrable_sup_aux {ι κ Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [Fintype ι] (D : κ → Ω → ℝ) (path : ι → Multiset κ)
    (hD : ∀ j : κ, Integrable (D j) μ) (s : Finset ι) (hs : s.Nonempty) :
    Integrable (fun ω => ⨆ p : { p // p ∈ s }, pathDuration D path p ω) μ := by
  classical
  revert hs
  induction s using Finset.induction with
  | empty =>
    intro hs
    obtain ⟨x, hx⟩ := hs
    exact absurd hx (Finset.notMem_empty x)
  | insert a s _has ih =>
    intro _
    by_cases hs' : s.Nonempty
    · have hne_ins : Nonempty { p // p ∈ insert a s } := ⟨⟨a, Finset.mem_insert_self a s⟩⟩
      have hne_s : Nonempty { p // p ∈ s } := by
        obtain ⟨x, hx⟩ := hs'
        exact ⟨⟨x, hx⟩⟩
      have heq : (fun ω => ⨆ p : { p // p ∈ insert a s }, pathDuration D path p ω)
          = (fun ω => pathDuration D path a ω)
            ⊔ (fun ω => ⨆ p : { p // p ∈ s }, pathDuration D path p ω) := by
        funext ω
        show (⨆ p : { p // p ∈ insert a s }, pathDuration D path p ω)
          = pathDuration D path a ω ⊔ (⨆ p : { p // p ∈ s }, pathDuration D path p ω)
        have hBdd_s : BddAbove (Set.range fun q : { p // p ∈ s } => pathDuration D path q ω) :=
          Finite.bddAbove_range _
        have hBdd_ins : BddAbove (Set.range fun q : { p // p ∈ insert a s } => pathDuration D path q ω) :=
          Finite.bddAbove_range _
        apply le_antisymm
        · refine @ciSup_le ℝ _ _ hne_ins _ _ (fun p => ?_)
          obtain ⟨p, hp⟩ := p
          rcases Finset.mem_insert.mp hp with rfl | hp
          · exact le_sup_left
          · exact (le_ciSup hBdd_s ⟨p, hp⟩).trans le_sup_right
        · refine sup_le (le_ciSup hBdd_ins ⟨a, Finset.mem_insert_self a s⟩) ?_
          refine @ciSup_le ℝ _ _ hne_s _ _ (fun p => ?_)
          obtain ⟨p, hp⟩ := p
          exact le_ciSup hBdd_ins ⟨p, Finset.mem_insert_of_mem hp⟩
      rw [heq]
      exact (integrable_ms_sum μ D hD (path a)).sup (ih hs')
    · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
      have hne_ins : Nonempty { p // p ∈ insert a s } := ⟨⟨a, Finset.mem_insert_self a s⟩⟩
      have heq : (fun ω => ⨆ p : { p // p ∈ insert a s }, pathDuration D path p ω)
          = (fun ω => pathDuration D path a ω) := by
        funext ω
        show (⨆ p : { p // p ∈ insert a s }, pathDuration D path p ω)
          = pathDuration D path a ω
        have hBdd_ins : BddAbove (Set.range fun q : { p // p ∈ insert a s } => pathDuration D path q ω) :=
          Finite.bddAbove_range _
        apply le_antisymm
        · refine @ciSup_le ℝ _ _ hne_ins _ _ (fun p => ?_)
          obtain ⟨p, hp⟩ := p
          rcases Finset.mem_insert.mp hp with rfl | hp
          · exact le_rfl
          · rw [hs0] at hp
            exact absurd hp (Finset.notMem_empty p)
        · exact le_ciSup hBdd_ins ⟨a, Finset.mem_insert_self a s⟩
      rw [heq]
      exact integrable_ms_sum μ D hD (path a)

theorem integrable_sup_pathDuration {ι κ Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [Fintype ι] [Nonempty ι] (D : κ → Ω → ℝ) (path : ι → Multiset κ)
    (hD : ∀ j : κ, Integrable (D j) μ) :
    Integrable (fun ω => ⨆ p : ι, pathDuration D path p ω) μ := by
  have hUniv := integrable_sup_aux μ D path hD Finset.univ Finset.univ_nonempty
  have hne_univ : Nonempty { p // p ∈ (Finset.univ : Finset ι) } := by
    obtain ⟨x, hx⟩ := Finset.univ_nonempty (α := ι)
    exact ⟨⟨x, hx⟩⟩
  have heq : (fun ω => ⨆ p : ι, pathDuration D path p ω)
      = (fun ω => ⨆ p : { p // p ∈ (Finset.univ : Finset ι) }, pathDuration D path p ω) := by
    funext ω
    show (⨆ p : ι, pathDuration D path p ω)
      = (⨆ p : { p // p ∈ (Finset.univ : Finset ι) }, pathDuration D path p ω)
    have hBdd_ι : BddAbove (Set.range fun q : ι => pathDuration D path q ω) :=
      Finite.bddAbove_range _
    have hBdd_univ : BddAbove (Set.range fun q : { p // p ∈ (Finset.univ : Finset ι) } => pathDuration D path q ω) :=
      Finite.bddAbove_range _
    apply le_antisymm
    · refine ciSup_le (fun p => ?_)
      exact le_ciSup hBdd_univ ⟨p, Finset.mem_univ p⟩
    · refine @ciSup_le ℝ _ _ hne_univ _ _ (fun p => ?_)
      obtain ⟨p, -⟩ := p
      exact le_ciSup hBdd_ι p
  rw [heq]
  exact hUniv

/-- Integral form for an arbitrary measure: the integral of the
longest path duration is at least the largest integrated path
duration, the largest sum of integrated job durations over the listed
jobs. Dependence between jobs is arbitrary. -/
theorem integral_sup_pathDuration_ge_of_measure {ι κ Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω)
    [Fintype ι] [Nonempty ι]
    (D : κ → Ω → ℝ) (path : ι → Multiset κ)
    (hD : ∀ j : κ, Integrable (D j) μ) :
    (∫ ω, ⨆ p : ι, pathDuration D path p ω ∂μ)
      ≥ ⨆ p : ι, ((path p).map fun j => ∫ ω, D j ω ∂μ).sum := by
  have hSup : Integrable (fun ω => ⨆ p : ι, pathDuration D path p ω) μ :=
    integrable_sup_pathDuration μ D path hD
  have hEq : ∀ p : ι, (∫ ω, pathDuration D path p ω ∂μ)
      = ((path p).map fun j => ∫ ω, D j ω ∂μ).sum :=
    fun p => integral_ms_sum μ D hD (path p)
  refine ciSup_le (fun p => ?_)
  rw [← hEq p]
  have hle : (fun ω => pathDuration D path p ω)
      ≤ (fun ω => ⨆ q : ι, pathDuration D path q ω) := by
    intro ω
    have hBdd : BddAbove (Set.range fun q : ι => pathDuration D path q ω) :=
      Finite.bddAbove_range _
    exact le_ciSup hBdd p
  exact integral_mono (integrable_ms_sum μ D hD (path p)) hSup hle

/-- Expected-maximum lower bound on a probability space: the expected
longest path duration is at least the largest expected path duration.
This is the source-faithful headline; the proof is the arbitrary-
measure integral form above. -/
theorem integral_sup_pathDuration_ge {ι κ Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Fintype ι] [Nonempty ι]
    (D : κ → Ω → ℝ) (path : ι → Multiset κ)
    (hD : ∀ j : κ, Integrable (D j) μ) :
    (∫ ω, ⨆ p : ι, pathDuration D path p ω ∂μ)
      ≥ ⨆ p : ι, ((path p).map fun j => ∫ ω, D j ω ∂μ).sum := by
  exact integral_sup_pathDuration_ge_of_measure μ D path hD

end ExpectedDuration
