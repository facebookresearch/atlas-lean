/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKRectMedialClosedCycles
import Code.FrontierD.FKRectEulerDefectTransitions

open Finset

namespace StatMech.FrontierD

noncomputable section



theorem fkRectEulerHomologyDefect_mono_configurationOfEdges
    (R : FKRectTorus) {F A : Finset R.EdgeIndex} (hFA : F ⊆ A) :
    fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) ≤
      fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R A) := by
  induction n : A.card - F.card using Nat.strong_induction_on generalizing F with
  | _ n ih =>
      subst n
      by_cases hEq : F = A
      · subst F
        exact le_rfl
      · have hss : F ⊂ A := (Finset.ssubset_iff_subset_ne).2 ⟨hFA, hEq⟩
        obtain ⟨e, heF, hins⟩ := Finset.ssubset_iff.mp hss
        have hstep := fkRectEulerHomologyDefect_insert_mono R F e heF
        have hcardlt : F.card < A.card := Finset.card_lt_card hss
        have hlt : A.card - (insert e F).card < A.card - F.card := by
          rw [Finset.card_insert_of_notMem heF]
          omega
        exact hstep.trans (ih _ hlt hins rfl)



theorem fkRectEulerHomologyDefect_even
    (R : FKRectTorus) (F : Finset R.EdgeIndex) :
    Even (fkRectEulerHomologyDefect R
      (fkRectConfigurationOfEdges R F)) := by
  induction F using Finset.induction_on with
  | empty =>
      rw [fkRectEulerHomologyDefect_empty]
      exact ⟨0, by norm_num⟩
  | @insert e F heF ih =>
      rcases fkRectEulerHomologyDefect_insert_dichotomy R F e heF with h | h
      · rw [h]
        exact ih
      · rw [h]
        exact ih.add ⟨1, by norm_num⟩



theorem fkRectEulerHomologyDefect_classified
    (R : FKRectTorus) (F : Finset R.EdgeIndex) :
    fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) = 0 ∨
      fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) = 2 := by
  have hlower : 0 ≤ fkRectEulerHomologyDefect R
      (fkRectConfigurationOfEdges R F) := by
    simpa only [fkRectEulerHomologyDefect_empty] using
      (fkRectEulerHomologyDefect_mono_configurationOfEdges R
        (Finset.empty_subset F))
  have hupper : fkRectEulerHomologyDefect R
      (fkRectConfigurationOfEdges R F) ≤ 2 := by
    simpa only [fkRectEulerHomologyDefect_univ] using
      (fkRectEulerHomologyDefect_mono_configurationOfEdges R
        (Finset.subset_univ F))
  obtain ⟨k, hk⟩ := fkRectEulerHomologyDefect_even R F
  omega

end

end StatMech.FrontierD
