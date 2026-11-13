/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



























































import Mathlib
import Code.Sharpness.Switching

open Finset BigOperators
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false

namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]















theorem gc2_sources_shift_bijOn (ends : ι → Sym2 V) (m K : Finset ι) (hK : K ⊆ m) (A : Finset V) :
    Set.BijOn (fun N => N ∆ K)
      {N | N ⊆ m ∧ sources ends N = A}
      {N | N ⊆ m ∧ sources ends N = A ∆ sources ends K} :=
  sources_shift_bijOn ends m K hK A









theorem gc2_shift_involutive (K : Finset ι) :
    Function.Involutive (fun N : Finset ι => N ∆ K) := by
  intro N
  simp only
  rw [symmDiff_symmDiff_cancel_right]



theorem gc2_shift_leftInvOn (ends : ι → Sym2 V) (m K : Finset ι) (B : Finset V) :
    Set.LeftInvOn (fun N => N ∆ K) (fun N => N ∆ K)
      {N | N ⊆ m ∧ sources ends N = B} := by
  intro N _
  exact gc2_shift_involutive K N












theorem gc2_shift_bijOn_empty_to_B (ends : ι → Sym2 V) (m K : Finset ι) (hK : K ⊆ m)
    (B : Finset V) (hKsrc : sources ends K = B) :
    Set.BijOn (fun N => N ∆ K)
      {N | N ⊆ m ∧ sources ends N = ∅}
      {N | N ⊆ m ∧ sources ends N = B} := by
  have h := sources_shift_bijOn ends m K hK (∅ : Finset V)
  rw [hKsrc, (by exact symmDiff_eq_right.mpr rfl : (∅ : Finset V) ∆ B = B)] at h
  exact h






theorem gc2_shift_bijOn_B_to_empty (ends : ι → Sym2 V) (m K : Finset ι) (hK : K ⊆ m)
    (B : Finset V) (hKsrc : sources ends K = B) :
    Set.BijOn (fun N => N ∆ K)
      {N | N ⊆ m ∧ sources ends N = B}
      {N | N ⊆ m ∧ sources ends N = ∅} := by
  have h := sources_shift_bijOn ends m K hK B
  rw [hKsrc, symmDiff_self B] at h
  exact h











theorem gc2_shift_involution_empty_B (ends : ι → Sym2 V) (m K : Finset ι) (hK : K ⊆ m)
    (B : Finset V) (hKsrc : sources ends K = B) :
    Set.BijOn (fun N => N ∆ K)
        {N | N ⊆ m ∧ sources ends N = B}
        {N | N ⊆ m ∧ sources ends N = ∅}
      ∧ Set.LeftInvOn (fun N => N ∆ K) (fun N => N ∆ K)
        {N | N ⊆ m ∧ sources ends N = B}
      ∧ Set.RightInvOn (fun N => N ∆ K) (fun N => N ∆ K)
        {N | N ⊆ m ∧ sources ends N = ∅} :=
  ⟨gc2_shift_bijOn_B_to_empty ends m K hK B hKsrc,
   gc2_shift_leftInvOn ends m K B,
   fun N _ => gc2_shift_involutive K N⟩

end StatMech.Walls
