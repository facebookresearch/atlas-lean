/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































































import Mathlib
import Code.Sharpness.Switching
import Code.Sharpness.FluxEdgeCopyBridge
import Code.Walls.gc2_componenthandshake

open Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false

namespace StatMech.Walls

open StatMech.Sharpness
open StatMech.Sharpness.RandomCurrent
open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]









omit [Fintype V] [DecidableEq V] in



theorem gc6_adjStep_mono {ι : Type*} (ends : ι → Sym2 V)
    {N m : Finset ι} (hNm : N ⊆ m) {a b : V} (h : adjStep ends N a b) :
    adjStep ends m a b := by
  obtain ⟨i, hi, ha, hb, hne⟩ := h
  exact ⟨i, hNm hi, ha, hb, hne⟩

omit [Fintype V] [DecidableEq V] in




theorem gc6_connK_mono {ι : Type*} (ends : ι → Sym2 V)
    {N m : Finset ι} (hNm : N ⊆ m) {i j : V} (h : connK ends N i j) :
    connK ends m i j :=
  Relation.ReflTransGen.mono (fun _ _ hstep => gc6_adjStep_mono ends hNm hstep) h








set_option linter.unusedFintypeInType false in











theorem gc6_pairingPath_abstract {ι : Type*} [DecidableEq ι] [Fintype ι]
    (ends : ι → Sym2 V) (N m : Finset ι)
    (hnd : ∀ i ∈ N, ¬ (ends i).IsDiag)
    (hNm : N ⊆ m) {i j : V}
    (hbdry : sources ends N = {i, j}) (hij : i ≠ j) :
    connK ends m i j := by
  
  have hconnN : connK ends N i j := by
    have hi_odd : Odd (degK ends N i) := by
      have hi : i ∈ sources ends N := by rw [hbdry]; simp
      rwa [RandomCurrent.mem_sources] at hi
    have hbdry' : ∀ x, Odd (degK ends N x) → x = i ∨ x = j := by
      intro x hx
      rw [← RandomCurrent.mem_sources, hbdry] at hx
      simpa using hx
    exact path_exists ends N hnd i j hi_odd hbdry' hij
  
  exact gc6_connK_mono ends hNm hconnN
















theorem gc6_pairingPath (m : ↥G.edgeFinset → ℕ) (N : Finset (Copy G m)) {i j : V}
    (hbdry : sources (endsM G m) N = {i, j}) (hij : i ≠ j) :
    connK (endsM G m) (univ : Finset (Copy G m)) i j :=
  gc6_pairingPath_abstract (endsM G m) N univ
    (fun k _ => endsM_not_isDiag G m k) (Finset.subset_univ N) hbdry hij
















theorem gc6_pairingPath_currentConnected (m : ↥G.edgeFinset → ℕ) (N : Finset (Copy G m)) {i j : V}
    (hbdry : sources (endsM G m) N = {i, j}) (hij : i ≠ j) :
    CurrentConnected G (ofEdgeFun G (profileFlux G m (univ : Finset (Copy G m)))) i j := by
  rw [← connK_iff]
  exact gc6_pairingPath G m N hbdry hij

















theorem gc6_pairingPath_oddDegree (m : ↥G.edgeFinset → ℕ) (N : Finset (Copy G m)) {i j : V}
    (hi_odd : Odd (degK (endsM G m) N i)) (hj_odd : Odd (degK (endsM G m) N j))
    (hother : ∀ x, Odd (degK (endsM G m) N x) → x = i ∨ x = j) (hij : i ≠ j) :
    connK (endsM G m) (univ : Finset (Copy G m)) i j := by
  have hbdry : sources (endsM G m) N = {i, j} := by
    ext x
    simp only [RandomCurrent.mem_sources, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact hother x
    · rintro (rfl | rfl)
      · exact hi_odd
      · exact hj_odd
  exact gc6_pairingPath G m N hbdry hij

end StatMech.Walls
