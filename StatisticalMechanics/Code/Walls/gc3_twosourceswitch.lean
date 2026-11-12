/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/































































import Mathlib
import Code.Sharpness.Switching
import Code.Sharpness.FluxEdgeCopyBridge
import Code.Walls.gc2_shiftbij
import Code.Walls.gc2_pairsubconfig

open Finset BigOperators
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 800000

namespace StatMech.Walls

open StatMech.Sharpness StatMech.Sharpness.RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]

















theorem gc3_sources_shift₂_bijOn (ends : ι → Sym2 V) (m P Q : Finset ι)
    (hP : P ⊆ m) (hQ : Q ⊆ m) (A : Finset V) :
    Set.BijOn (fun K => (K ∆ P) ∆ Q)
      {K | K ⊆ m ∧ sources ends K = A}
      {K | K ⊆ m ∧ sources ends K = A ∆ sources ends P ∆ sources ends Q} :=
  (gc2_sources_shift_bijOn ends m Q hQ (A ∆ sources ends P)).comp
    (gc2_sources_shift_bijOn ends m P hP A)

























theorem gc3_twoSourceSwitch (ends : ι → Sym2 V) (m : Finset ι)
    (A : Finset V) {u v s t : V} (huv : u ≠ v) (hst : s ≠ t)
    (hconnuv : connK ends m u v) (hconnst : connK ends m s t) :
    #(m.powerset.filter (fun K => sources ends K = A ∆ {u, v} ∆ {s, t}))
      = #(m.powerset.filter (fun K => sources ends K = A)) := by
  
  obtain ⟨P, hPm, hPsrc⟩ := gc2_pair_subconfig ends m hconnuv huv
  obtain ⟨Q, hQm, hQsrc⟩ := gc2_pair_subconfig ends m hconnst hst
  
  have hbij := gc3_sources_shift₂_bijOn ends m P Q hPm hQm A
  rw [hPsrc, hQsrc] at hbij
  
  have himg : (m.powerset.filter (fun K => sources ends K = A ∆ {u, v} ∆ {s, t}))
      = (m.powerset.filter (fun K => sources ends K = A)).image (fun K => (K ∆ P) ∆ Q) := by
    ext K
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · intro ⟨hKm, hKsrc⟩
      obtain ⟨L, hL, hLK⟩ := hbij.2.2 ⟨hKm, hKsrc⟩
      exact ⟨L, ⟨hL.1, hL.2⟩, hLK⟩
    · rintro ⟨L, ⟨hLm, hLsrc⟩, rfl⟩
      have := hbij.1 ⟨hLm, hLsrc⟩
      exact ⟨this.1, this.2⟩
  rw [himg, Finset.card_image_of_injOn]
  
  intro K₁ hK₁ K₂ hK₂ h
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hK₁ hK₂
  exact hbij.2.1 ⟨hK₁.1, hK₁.2⟩ ⟨hK₂.1, hK₂.2⟩ h


















theorem gc3_twoSourceSwitch_lemma (ends : ι → Sym2 V) (m : Finset ι)
    (A : Finset V) {u v s t : V} (huv : u ≠ v) (hst : s ≠ t)
    (hconnuv : connK ends m u v) (hconnst : connK ends m s t) (F : Finset ι → ℝ) :
    ∑ _K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {u, v} ∆ {s, t}), F m
      = ∑ _K ∈ m.powerset.filter (fun K => sources ends K = A), F m := by
  rw [Finset.sum_const, Finset.sum_const,
    gc3_twoSourceSwitch ends m A huv hst hconnuv hconnst]








open StatMech.Sharpness.FluxEdgeCopy in









theorem gc3_twoSourceSwitch_current {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (m : ↥G.edgeFinset → ℕ)
    (M : Finset (Copy G m)) (A : Finset W) {u v s t : W} (huv : u ≠ v) (hst : s ≠ t)
    (hconnuv : connK (endsM G m) M u v) (hconnst : connK (endsM G m) M s t) :
    #(M.powerset.filter (fun K => RandomCurrent.sources (endsM G m) K = A ∆ {u, v} ∆ {s, t}))
      = #(M.powerset.filter (fun K => RandomCurrent.sources (endsM G m) K = A)) :=
  gc3_twoSourceSwitch (endsM G m) M A huv hst hconnuv hconnst














theorem gc3_twoSourceSwitch_coincident (ends : ι → Sym2 V) (m : Finset ι)
    (A : Finset V) (u v : V) :
    #(m.powerset.filter (fun K => sources ends K = A ∆ {u, v} ∆ {u, v}))
      = #(m.powerset.filter (fun K => sources ends K = A)) := by
  have hcancel : A ∆ ({u, v} : Finset V) ∆ {u, v} = A := by
    rw [symmDiff_assoc, symmDiff_self, symmDiff_bot]
  rw [hcancel]

end StatMech.Walls
