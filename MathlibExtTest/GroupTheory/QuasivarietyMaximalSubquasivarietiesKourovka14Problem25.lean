/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.QuasivarietyMaximalSubquasivarietiesKourovka14Problem25

open MathlibExt.GroupTheory.QuasivarietyMaximalSubquasivarietiesKourovka14Problem25Wanted

-- A quasi-identity with no premises and conclusion x = 1 detects the trivial group.
example (H : Type) [Group H] :
    (QuasiIdentity.mk 1 [] (FreeGroup.of 0)).HoldsIn H ↔ ∀ h : H, h = 1 := by
  constructor
  · intro h x
    simpa using h (fun _ => x) (by simp)
  · intro h x _
    exact h _

-- Two distinct maximal proper subquasivarieties of the witness are incomparable.
example : ∃ (G : Type) (_ : Group G), Group.FG G ∧
    ∃ R S, IsMaximalProperSubquasivariety G R ∧ IsMaximalProperSubquasivariety G S ∧
      ¬ QVLe R S ∧ ¬ QVLe S R := by
  obtain ⟨G, grp, fg, many⟩ := finitelyGeneratedGroupInfinitelyManyMaximalSubquasivarieties_holds
  obtain ⟨Q, hQ, hdistinct⟩ := many 2
  refine ⟨G, grp, fg, Q 0, Q 1, hQ 0, hQ 1, ?_, ?_⟩
  · intro h
    obtain h' | h' := (hQ 0).2.2 (Q 1) h (hQ 1).1
    · exact hdistinct 0 1 (by decide) ⟨h, h'⟩
    · exact (hQ 1).2.1 h'
  · intro h
    obtain h' | h' := (hQ 1).2.2 (Q 0) h (hQ 0).1
    · exact hdistinct 0 1 (by decide) ⟨h', h⟩
    · exact (hQ 0).2.1 h'
