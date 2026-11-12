/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Patrick Tam
-/
module

public import MathlibExt.GroupTheory.Representation

@[expose] public section

open CategoryTheory

namespace MathlibExtTest.GroupTheory.Representation

open MetaMathlibExt

-- Algebra 511: Character Degrees

lemma mem_cd_iff {G : Type} [Group G] [Fintype G] (d : ℕ) :
    d ∈ cd G ↔ ∃ V : FDRep ℂ G, Simple V ∧ d = Module.finrank ℂ V :=
  Iff.rfl

-- Algebra 530: Irreducible Character

lemma IsIrrChar.of_simple
    {G : Type*} [Group G] [Fintype G]
    (V : FDRep ℂ G) [CategoryTheory.Simple V] :
    IsIrrChar (FDRep.character V) := by
  exact ⟨V, inferInstance, fun _ => rfl⟩

end MathlibExtTest.GroupTheory.Representation

end
