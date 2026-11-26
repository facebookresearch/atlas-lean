/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.LaplaceHarnack
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Tests for Harnack's inequality

We use a single Harnack constant for the identity and the zero function on the positive
half-line, and specialize the theorem to a zero-dimensional domain.
-/

open InnerProductSpace Laplacian Set
open MathlibExt.Analysis.PDE.LaplaceMeanValueWanted

-- The wanted API does not require a measurable-space instance on E.
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V) (hVconn : IsConnected V)
    (hVc : IsCompact (closure V)) (hVU : closure V ⊆ U) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : E → ℝ, HarmonicOnNhd u U → (∀ x ∈ U, 0 ≤ u x) →
      ∀ x ∈ V, ∀ y ∈ V, u x ≤ C * u y :=
  harnack_inequality hU (hV := hV) hVconn hVc hVU

example : ∃ C : ℝ, 0 < C ∧ (∀ x ∈ Ioo (1 : ℝ) 3, ∀ y ∈ Ioo (1 : ℝ) 3, x ≤ C * y) ∧
    (∀ x ∈ Ioo (1 : ℝ) 3, ∀ y ∈ Ioo (1 : ℝ) 3, (0 : ℝ) ≤ C * 0) := by
  have hclosure : closure (Ioo (1 : ℝ) 3) = Icc 1 3 := closure_Ioo (by norm_num)
  have hsub : closure (Ioo (1 : ℝ) 3) ⊆ Ioi 0 := by
    rw [hclosure]
    intro x hx
    exact zero_lt_one.trans_le hx.1
  obtain ⟨C, hC, h⟩ := harnack_inequality isOpen_Ioi isOpen_Ioo
    (isConnected_Ioo (by norm_num)) (hclosure ▸ isCompact_Icc) hsub
  have hid : HarmonicOnNhd (fun x : ℝ ↦ x) (Ioi 0) := by
    intro x _
    refine ⟨contDiffAt_id, Filter.Eventually.of_forall fun y ↦ ?_⟩
    change Δ (fun z : ℝ ↦ z) y = 0
    simp [laplacian_eq_iteratedDeriv_real, iteratedDeriv_fun_id]
  exact ⟨C, hC, h _ hid (fun _ hx ↦ hx.le), h _ (harmonicOnNhd_const 0) (fun _ _ ↦ le_rfl)⟩

example : ∃ C : ℝ, 0 < C ∧ ∀ u : EuclideanSpace ℝ (Fin 0) → ℝ,
    HarmonicOnNhd u univ → (∀ x, 0 ≤ u x) → ∀ x y, u x ≤ C * u y := by
  obtain ⟨C, hC, h⟩ := harnack_inequality (E := EuclideanSpace ℝ (Fin 0))
    isOpen_univ isOpen_univ isConnected_univ (by simp) (subset_univ _)
  exact ⟨C, hC, fun u hu hu₀ x y ↦ h u hu (fun z _ ↦ hu₀ z) x (mem_univ _) y (mem_univ _)⟩
