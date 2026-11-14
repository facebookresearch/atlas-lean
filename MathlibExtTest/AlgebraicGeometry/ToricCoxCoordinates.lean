/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.ToricCoxCoordinates
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

noncomputable section

open MathlibExt.AlgebraicGeometry.ToricCoxCoordinates

private def lineFan : FanData 1 2 where
  rays := ![fun _ => 1, fun _ => -1]
  faces := (Finset.univ : Finset (Fin 2)).powerset.filter (fun σ => σ.card ≤ 1)
  empty_mem := by simp
  singleton_mem := by intro i; simp
  downward := by
    intro σ hσ τ hτ
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
      (Finset.card_le_card hτ).trans (Finset.mem_filter.mp hσ).2⟩

/-- The projective-line Cox open excludes the unstable zero coordinate tuple. -/
example : (fun _ : Fin 2 => (0 : ℂ)) ∉ coxLocus lineFan := by
  rintro ⟨σ, hσ, hz⟩
  have hcard : σ.card ≤ 1 := (Finset.mem_filter.mp hσ).2
  have hsub : (Finset.univ : Finset (Fin 2)) ⊆ σ := by
    intro i hi
    by_contra h
    exact hz i h rfl
  have hlow : 2 ≤ σ.card := by simpa using Finset.card_le_card hsub
  exact Nat.not_succ_le_self 1 (hlow.trans hcard)

/-- A boundary point with one vanishing coordinate is retained. -/
example : (![1, 0] : Fin 2 → ℂ) ∈ coxLocus lineFan := by
  refine ⟨{1}, lineFan.singleton_mem 1, ?_⟩
  intro i hi
  fin_cases i <;> simp_all

/-- The opposite integral rays give the expected diagonal scalar Cox group. -/
example (u : ℂˣ) : characterHom lineFan (fun _ : Fin 2 => u) = 1 := by
  funext j
  fin_cases j
  simp [characterHom, lineFan, Fin.prod_univ_two]
