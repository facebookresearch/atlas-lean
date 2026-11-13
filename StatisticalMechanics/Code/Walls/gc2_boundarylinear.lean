/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































































import Mathlib
import Code.Sharpness.FluxEdgeCopyBridge
import Code.Sharpness.SwitchingCovariance
import Code.Walls.gc_subgraphcount

open Finset BigOperators
open scoped symmDiff Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech.Walls

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
















theorem gc2_odd_degK_symmDiff (m : ↥G.edgeFinset → ℕ) (N₁ N₂ : Finset (Copy G m)) (x : V) :
    Odd (RandomCurrent.degK (endsM G m) (N₁ ∆ N₂) x)
      ↔ (Odd (RandomCurrent.degK (endsM G m) N₁ x)
          ≠ Odd (RandomCurrent.degK (endsM G m) N₂ x)) :=
  RandomCurrent.odd_degK_symmDiff (endsM G m) N₁ N₂ x





















theorem gc2_boundary_symmDiff (m : ↥G.edgeFinset → ℕ) (N₁ N₂ : Finset (Copy G m)) :
    StatMech.Sharpness.RandomCurrent.sources (endsM G m) (N₁ ∆ N₂)
      = StatMech.Sharpness.RandomCurrent.sources (endsM G m) N₁
          ∆ StatMech.Sharpness.RandomCurrent.sources (endsM G m) N₂ :=
  RandomCurrent.sources_symmDiff (endsM G m) N₁ N₂







theorem gc2_mem_boundary_symmDiff (m : ↥G.edgeFinset → ℕ) (N₁ N₂ : Finset (Copy G m)) (x : V) :
    x ∈ StatMech.Sharpness.RandomCurrent.sources (endsM G m) (N₁ ∆ N₂)
      ↔ ((x ∈ StatMech.Sharpness.RandomCurrent.sources (endsM G m) N₁)
          ≠ (x ∈ StatMech.Sharpness.RandomCurrent.sources (endsM G m) N₂)) := by
  rw [gc2_boundary_symmDiff, Finset.mem_symmDiff]
  by_cases h1 : x ∈ StatMech.Sharpness.RandomCurrent.sources (endsM G m) N₁ <;>
    by_cases h2 : x ∈ StatMech.Sharpness.RandomCurrent.sources (endsM G m) N₂ <;>
    simp [h1, h2]




theorem gc2_boundary_symmDiff_self (m : ↥G.edgeFinset → ℕ) (N : Finset (Copy G m)) :
    StatMech.Sharpness.RandomCurrent.sources (endsM G m) (N ∆ N) = (∅ : Finset V) := by
  rw [gc2_boundary_symmDiff, symmDiff_self, bot_eq_empty]


















theorem gc2_boundary_symmDiff_profile (m : ↥G.edgeFinset → ℕ) (N₁ N₂ : Finset (Copy G m)) :
    StatMech.Sharpness.sources G (ofEdgeFun G (profileFlux G m (N₁ ∆ N₂)))
      = StatMech.Sharpness.sources G (ofEdgeFun G (profileFlux G m N₁))
          ∆ StatMech.Sharpness.sources G (ofEdgeFun G (profileFlux G m N₂)) := by
  rw [← sources_eq, ← sources_eq, ← sources_eq]
  exact gc2_boundary_symmDiff G m N₁ N₂














theorem gc2_boundary_symmDiff_cancel_right (m : ↥G.edgeFinset → ℕ) (N P : Finset (Copy G m)) :
    StatMech.Sharpness.RandomCurrent.sources (endsM G m) (N ∆ P)
      = StatMech.Sharpness.RandomCurrent.sources (endsM G m) N
          ∆ StatMech.Sharpness.RandomCurrent.sources (endsM G m) P :=
  gc2_boundary_symmDiff G m N P








theorem gc2_boundary_surgery (m : ↥G.edgeFinset → ℕ) (N P : Finset (Copy G m))
    {B : Finset V} (hN : StatMech.Sharpness.RandomCurrent.sources (endsM G m) N = B) :
    StatMech.Sharpness.RandomCurrent.sources (endsM G m) (N ∆ P)
      = B ∆ StatMech.Sharpness.RandomCurrent.sources (endsM G m) P := by
  rw [gc2_boundary_symmDiff, hN]

end StatMech.Walls
