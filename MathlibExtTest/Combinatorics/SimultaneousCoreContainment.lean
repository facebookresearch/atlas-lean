/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimultaneousCoreContainment
import Mathlib.Tactic.Tauto

/-!
# Tests for simultaneous core containment

The partition `(3, 1, 1)` has hook lengths `5, 2, 1, 2, 1`. It is a simultaneous
`(3, 4)`-core and so lies in every maximum-size such core. For modulus one the only core
is the empty diagram.
-/

open MathlibExt.Combinatorics.SimultaneousCoreContainmentOWR1265Problem006Wanted

namespace MathlibExtTest.Combinatorics.SimultaneousCoreContainment

private def shape := YoungDiagram.ofRowLens [3, 1, 1] (by decide)

private lemma shape_core_iff (s : ℕ) : IsCore s shape ↔ ¬ s ∣ 1 ∧ ¬ s ∣ 2 ∧ ¬ s ∣ 5 := by
  have h : shape.cells = {(0, 0), (0, 1), (0, 2), (1, 0), (2, 0)} := by
    decide
  have lens : shape.rowLen 0 = 3 ∧ shape.rowLen 1 = 1 ∧ shape.rowLen 2 = 1 ∧
      shape.colLen 0 = 3 ∧ shape.colLen 1 = 1 ∧ shape.colLen 2 = 1 := by
    simp only [YoungDiagram.rowLen_eq_card, YoungDiagram.colLen_eq_card]
    decide
  simp only [IsCore, ← YoungDiagram.mem_cells, h, Finset.mem_insert, Finset.mem_singleton,
    or_imp, forall_and, forall_eq]
  obtain ⟨hr₀, hr₁, hr₂, hc₀, hc₁, hc₂⟩ := lens
  simp [hr₀, hr₁, hr₂, hc₀, hc₁, hc₂]
  tauto

private lemma shape_cores : IsCore 3 shape ∧ IsCore 4 shape := by
  simp only [shape_core_iff]
  decide

example : ¬ IsCore 5 shape := by simp [shape_core_iff]

example (μ : YoungDiagram) : IsCore 1 μ ↔ μ = ⊥ := by
  constructor
  · intro h
    exact le_bot_iff.mp (fun c hc => False.elim (h c hc (one_dvd _)))
  · rintro rfl c hc
    exact (YoungDiagram.notMem_bot c hc).elim

example (κ : YoungDiagram) (h₃ : IsCore 3 κ) (h₄ : IsCore 4 κ)
    (hmax : ∀ ν : YoungDiagram, IsCore 3 ν → IsCore 4 ν → ν.card ≤ κ.card) : shape ≤ κ :=
  simultaneousCoreContainment_holds 3 4 (by decide) (by decide) (by decide)
    κ h₃ h₄ hmax shape shape_cores.1 shape_cores.2

end MathlibExtTest.Combinatorics.SimultaneousCoreContainment
