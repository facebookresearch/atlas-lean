/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































































import Mathlib
import Code.Sharpness.RandomCurrent
import Code.Sharpness.ClaimIsing
import Code.Sharpness.FluxEdgeCopyBridge
import Code.Walls.gc2_boundarylinear

open Finset BigOperators
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech.Walls

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

















theorem gc3_sources_add₃ (n₁ n₂ n₃ : Current V) :
    sources G (fun e => n₁ e + n₂ e + n₃ e)
      = sources G n₁ ∆ sources G n₂ ∆ sources G n₃ := by
  
  have h1 : sources G (fun e => n₁ e + n₂ e + n₃ e)
      = sources G (fun e => (fun e => n₁ e + n₂ e) e + n₃ e) := rfl
  rw [h1, sources_add G (fun e => n₁ e + n₂ e) n₃, sources_add G n₁ n₂]









theorem gc3_triple_source_pinned (n₁ n₂ n₃ : Current V) {A B C : Finset V}
    (hA : sources G n₁ = A) (hB : sources G n₂ = B) (hC : sources G n₃ = C) :
    sources G (fun e => n₁ e + n₂ e + n₃ e) = A ∆ B ∆ C := by
  rw [gc3_sources_add₃ G n₁ n₂ n₃, hA, hB, hC]









theorem gc3_mem_triple_source (n₁ n₂ n₃ : Current V) (x : V) :
    x ∈ sources G (fun e => n₁ e + n₂ e + n₃ e)
      ↔ ((x ∈ sources G n₁) ≠ (x ∈ sources G n₂)) ≠ (x ∈ sources G n₃) := by
  rw [gc3_sources_add₃, Finset.mem_symmDiff, Finset.mem_symmDiff]
  by_cases h1 : x ∈ sources G n₁ <;> by_cases h2 : x ∈ sources G n₂ <;>
    by_cases h3 : x ∈ sources G n₃ <;> simp [h1, h2, h3]








theorem gc3_triple_source_self_left (n p : Current V) :
    sources G (fun e => n e + n e + p e) = sources G p := by
  rw [gc3_sources_add₃ G n n p, symmDiff_self, bot_symmDiff]



















theorem gc3_boundary_symmDiff₃ (m : ↥G.edgeFinset → ℕ) (N₁ N₂ N₃ : Finset (Copy G m)) :
    StatMech.Sharpness.RandomCurrent.sources (endsM G m) (N₁ ∆ N₂ ∆ N₃)
      = StatMech.Sharpness.RandomCurrent.sources (endsM G m) N₁
          ∆ StatMech.Sharpness.RandomCurrent.sources (endsM G m) N₂
          ∆ StatMech.Sharpness.RandomCurrent.sources (endsM G m) N₃ := by
  rw [gc2_boundary_symmDiff G m (N₁ ∆ N₂) N₃, gc2_boundary_symmDiff G m N₁ N₂]






theorem gc3_triple_source_edgecopy_pinned (m : ↥G.edgeFinset → ℕ)
    (N₁ N₂ N₃ : Finset (Copy G m)) {A B C : Finset V}
    (hA : StatMech.Sharpness.RandomCurrent.sources (endsM G m) N₁ = A)
    (hB : StatMech.Sharpness.RandomCurrent.sources (endsM G m) N₂ = B)
    (hC : StatMech.Sharpness.RandomCurrent.sources (endsM G m) N₃ = C) :
    StatMech.Sharpness.RandomCurrent.sources (endsM G m) (N₁ ∆ N₂ ∆ N₃) = A ∆ B ∆ C := by
  rw [gc3_boundary_symmDiff₃ G m N₁ N₂ N₃, hA, hB, hC]






theorem gc3_boundary_symmDiff₃_profile (m : ↥G.edgeFinset → ℕ)
    (N₁ N₂ N₃ : Finset (Copy G m)) :
    StatMech.Sharpness.sources G (ofEdgeFun G (profileFlux G m (N₁ ∆ N₂ ∆ N₃)))
      = StatMech.Sharpness.sources G (ofEdgeFun G (profileFlux G m N₁))
          ∆ StatMech.Sharpness.sources G (ofEdgeFun G (profileFlux G m N₂))
          ∆ StatMech.Sharpness.sources G (ofEdgeFun G (profileFlux G m N₃)) := by
  rw [← sources_eq, ← sources_eq, ← sources_eq, ← sources_eq]
  exact gc3_boundary_symmDiff₃ G m N₁ N₂ N₃

end StatMech.Walls
