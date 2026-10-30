/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.TopologicalAnnihilator

import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Tests for topological annihilators and the bipolar theorem

Concrete checks on `ℝ × ℝ` and on `ℝ`:

* the annihilator of the `x`-axis `span {(1, 0)}` contains the second
  coordinate functional but not the first;
* the bipolar theorem recovers the `x`-axis from its double annihilator;
* the annihilator of `⊥` is `⊤` and the annihilator of `⊤` is `⊥`,
  in both `ℝ × ℝ` and `ℝ`;
* separation: the point `(0, 1)` outside the `x`-axis is separated by an
  annihilating functional with nonzero value there.
-/

namespace MathlibExtTest.Analysis.FunctionalAnalysis.TopologicalAnnihilatorTests

open Submodule

/-- The `x`-axis in `ℝ × ℝ`, as a submodule. -/
private abbrev xAxis : Submodule ℝ (ℝ × ℝ) := span ℝ ({(1, 0)} : Set (ℝ × ℝ))

/-- The second coordinate functional vanishes on the `x`-axis, so it lies
in the annihilator of the `x`-axis. -/
private theorem snd_mem_xAxis_annihilator :
    ContinuousLinearMap.snd ℝ ℝ ℝ ∈ xAxis.topologicalAnnihilator := by
  rw [mem_topologicalAnnihilator]
  intro x hx
  rw [Submodule.mem_span_singleton] at hx
  obtain ⟨a, rfl⟩ := hx
  simp

/-- The first coordinate functional does not vanish on the `x`-axis, so it
is not in the annihilator. -/
private theorem fst_notMem_xAxis_annihilator :
    ContinuousLinearMap.fst ℝ ℝ ℝ ∉ xAxis.topologicalAnnihilator := by
  rw [mem_topologicalAnnihilator]
  push Not
  exact ⟨(1, 0), Submodule.subset_span (by simp), by simp⟩

/-- The `x`-axis is closed, being finite-dimensional. -/
private theorem xAxis_closed : IsClosed (xAxis : Set (ℝ × ℝ)) :=
  Submodule.closed_of_finiteDimensional xAxis

/-- **Bipolar theorem on the `x`-axis:** the double annihilator of the
`x`-axis is the `x`-axis itself. -/
private theorem xAxis_bipolar :
    xAxis.topologicalAnnihilator.topologicalCoannihilator = xAxis := by
  rw [topologicalAnnihilator_topologicalCoannihilator_eq_topologicalClosure]
  exact xAxis_closed.submodule_topologicalClosure_eq

/-- Separation on the `x`-axis: there is an annihilating functional with
nonzero value at `(0, 1)`, which lies outside the `x`-axis. -/
private theorem xAxis_separation :
    ∃ f ∈ xAxis.topologicalAnnihilator, f (0, 1) ≠ 0 := by
  apply exists_mem_topologicalAnnihilator_apply_ne_zero
  rw [xAxis_closed.submodule_topologicalClosure_eq]
  intro h
  rw [xAxis, Submodule.mem_span_singleton] at h
  obtain ⟨a, ha⟩ := h
  have hfst := congrArg Prod.fst ha
  simp at hfst
  have hsnd := congrArg Prod.snd ha
  simp [hfst] at hsnd

/-- The annihilator of `⊥` in `ℝ × ℝ` is everything. -/
private theorem bot_annihilator :
    (⊥ : Submodule ℝ (ℝ × ℝ)).topologicalAnnihilator = ⊤ :=
  topologicalAnnihilator_bot

/-- The annihilator of `⊤` in `ℝ × ℝ` is zero. -/
private theorem top_annihilator :
    (⊤ : Submodule ℝ (ℝ × ℝ)).topologicalAnnihilator = ⊥ :=
  topologicalAnnihilator_top

/-- The annihilator of `⊥` in `ℝ` is everything. -/
private theorem bot_annihilator_real :
    (⊥ : Submodule ℝ ℝ).topologicalAnnihilator = ⊤ :=
  topologicalAnnihilator_bot

/-- The annihilator of `⊤` in `ℝ` is zero. -/
private theorem top_annihilator_real :
    (⊤ : Submodule ℝ ℝ).topologicalAnnihilator = ⊥ :=
  topologicalAnnihilator_top

/-- The zero subspace of `ℝ` is not dense, so its annihilator is nonzero:
the annihilator/density criterion in the negative direction. -/
private theorem bot_not_dense_real :
    (⊥ : Submodule ℝ ℝ).topologicalAnnihilator ≠ ⊥ := by
  intro h
  have hid : (ContinuousLinearMap.id ℝ ℝ) ∈
      (⊥ : Submodule ℝ ℝ).topologicalAnnihilator := by
    rw [topologicalAnnihilator_bot]
    trivial
  rw [h, Submodule.mem_bot ℝ] at hid
  exact absurd (congrArg (· (1 : ℝ)) hid) (by simp)

end MathlibExtTest.Analysis.FunctionalAnalysis.TopologicalAnnihilatorTests
