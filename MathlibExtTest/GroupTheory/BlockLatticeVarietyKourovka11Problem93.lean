/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.BlockLatticeVarietyKourovka11Problem93
import Mathlib.Data.Set.Lattice.Bounded

open MathlibExt.GroupTheory.BlockLatticeVarietyKourovka11Problem93Wanted

-- The refutation supplies an identity with a counterexample among ordinary lattices.
example : ∃ p q : LatticeTerm,
    (∀ (G : Type) [Group G] [Finite G] (v : ℕ → Set G), (∀ n, IsBlock (v n)) →
      p.evalBlock v = q.evalBlock v) ∧
    ∃ (L : Type) (_ : Lattice L) (v : ℕ → L), p.eval v ≠ q.eval v := by
  classical
  simpa only [blockLatticesGenerateAllLattices, not_forall, exists_prop]
    using blockLatticesGenerateAllLattices_refuted

-- The empty block acts as the bottom element when evaluating a join.
example {G : Type} [Group G] (X : Set G) (hX : IsBlock X) :
    (LatticeTerm.sup (.var 0) (.var 1)).evalBlock (fun n ↦ if n = 0 then ∅ else X) = X := by
  change blockSup ∅ X = X
  apply Set.Subset.antisymm
  · exact Set.sInter_subset_of_mem ⟨hX, by simp⟩
  · apply Set.subset_sInter
    rintro Z ⟨_, hZ⟩ x hx
    exact hZ (Or.inr hx)
