/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































































import Mathlib
import Code.Sharpness.Switching
import Code.Sharpness.FluxEdgeCopyBridge

open Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false

namespace StatMech.Walls

open StatMech.Sharpness
open StatMech.Sharpness.RandomCurrent
open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
























theorem gc2_componentHandshake_abstract {ι : Type*} [DecidableEq ι] [Fintype ι]
    (ends : ι → Sym2 V) (M : Finset ι)
    (hnd : ∀ i ∈ M, ¬ (ends i).IsDiag) {u v : V}
    (hu_odd : Odd (degK ends M u))
    (hbdry : ∀ x, Odd (degK ends M x) → x = u ∨ x = v)
    (huv : u ≠ v) :
    connK ends M u v :=
  path_exists ends M hnd u v hu_odd hbdry huv





















theorem gc2_componentHandshake (m : ↥G.edgeFinset → ℕ) (M : Finset (Copy G m)) {u v : V}
    (hu_odd : Odd (degK (endsM G m) M u))
    (hbdry : ∀ x, Odd (degK (endsM G m) M x) → x = u ∨ x = v)
    (huv : u ≠ v) :
    connK (endsM G m) M u v :=
  gc2_componentHandshake_abstract (endsM G m) M
    (fun i _ => endsM_not_isDiag G m i) hu_odd hbdry huv




















theorem gc2_componentHandshake_sources (m : ↥G.edgeFinset → ℕ) (M : Finset (Copy G m)) {u v : V}
    (hbdry : RandomCurrent.sources (endsM G m) M = {u, v}) (huv : u ≠ v) :
    connK (endsM G m) M u v := by
  
  have hu_odd : Odd (degK (endsM G m) M u) := by
    have hu : u ∈ RandomCurrent.sources (endsM G m) M := by rw [hbdry]; simp
    rwa [RandomCurrent.mem_sources] at hu
  
  have hbdry' : ∀ x, Odd (degK (endsM G m) M x) → x = u ∨ x = v := by
    intro x hx
    rw [← RandomCurrent.mem_sources, hbdry] at hx
    simpa using hx
  exact gc2_componentHandshake G m M hu_odd hbdry' huv


















theorem gc2_componentHandshake_mem_compOf (m : ↥G.edgeFinset → ℕ) (M : Finset (Copy G m)) {u v : V}
    (hbdry : RandomCurrent.sources (endsM G m) M = {u, v}) (huv : u ≠ v) :
    v ∈ compOf (endsM G m) M u := by
  rw [mem_compOf]
  exact gc2_componentHandshake_sources G m M hbdry huv










theorem gc2_componentHandshake_oddComp (m : ↥G.edgeFinset → ℕ) (M : Finset (Copy G m)) {u v : V}
    (hbdry : RandomCurrent.sources (endsM G m) M = {u, v}) (huv : u ≠ v) :
    (compOf (endsM G m) M u).filter (fun x => Odd (degK (endsM G m) M x)) = {u, v} := by
  
  have hv_comp : v ∈ compOf (endsM G m) M u := gc2_componentHandshake_mem_compOf G m M hbdry huv
  have hu_comp : u ∈ compOf (endsM G m) M u := by rw [mem_compOf]; exact Relation.ReflTransGen.refl
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨_, hxodd⟩
    rw [← RandomCurrent.mem_sources, hbdry] at hxodd
    simpa using hxodd
  · intro hx
    
    have hx_src : x ∈ RandomCurrent.sources (endsM G m) M := by rw [hbdry]; exact hx
    rw [RandomCurrent.mem_sources] at hx_src
    refine ⟨?_, hx_src⟩
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hu_comp
    · exact hv_comp

end StatMech.Walls
