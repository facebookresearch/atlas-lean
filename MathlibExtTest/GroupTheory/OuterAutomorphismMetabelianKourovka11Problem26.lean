/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.OuterAutomorphismMetabelianKourovka11Problem26
import Mathlib.GroupTheory.QuotientGroup.Basic

open MathlibExt.GroupTheory.OuterAutomorphismMetabelianKourovka11Problem26Wanted

-- Recover the quotient formulation of the theorem for an arbitrary group.
example (G : Type) [Group G] :
    ∃ (M : Type) (_ : Group M), Subgroup.derivedSeries M 2 = ⊥ ∧ Subgroup.center M = ⊥ ∧
      ∃ _ : (MulAut.conj (G := M)).range.Normal,
        Nonempty ((MulAut M ⧸ (MulAut.conj (G := M)).range) ≃* G) := by
  by_contra h
  apply groupNotOuterAutOfMetabelian_refuted
  refine ⟨G, inferInstance, fun M inst hmet hcen ⟨φ, hsurj, hker⟩ ↦ ?_⟩
  apply h
  refine ⟨M, inst, hmet, hcen, ?_⟩
  rw [← hker]
  exact ⟨inferInstance, ⟨QuotientGroup.quotientKerEquivOfSurjective φ hsurj⟩⟩

-- The trivial group realizes precisely the trivial target groups.
example (M G : Type) [Group M] [Subsingleton M] [Group G] : OutIsoTo M G ↔ Subsingleton G := by
  have : Subsingleton (MulAut M) := ⟨fun f g ↦ MulEquiv.ext fun x ↦ Subsingleton.elim _ _⟩
  constructor
  · rintro ⟨φ, hφ, _⟩
    exact hφ.subsingleton
  · intro h
    exact ⟨1, fun x ↦ ⟨1, Subsingleton.elim _ _⟩, Subsingleton.elim _ _⟩
