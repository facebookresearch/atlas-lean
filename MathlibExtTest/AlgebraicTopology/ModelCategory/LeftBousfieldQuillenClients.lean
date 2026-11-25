/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.Quillen

/-!
# Clients of the recognized left Bousfield Quillen interface

The first example constructs the unchanged weak-equivalence presentation on
any base model category. The second uses two independent recognition packets
and an arbitrary original adjunction.
-/

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open HomotopicalAlgebra.LeftBousfieldLocalization

variable {C D : Type*} [Category* C] [ModelCategory C] [Category* D] [ModelCategory D]

private theorem unchanged : Recognition (weakEquivalences C) (IsFibrant (C := C)) := by
  have hRlp : (cofibrations C ⊓ weakEquivalences C).rlp = fibrations C :=
    trivialCofibrations_rlp C
  refine ⟨le_rfl, inferInstance, ?_, ?_, ?_, fun _ _ _ ↦ Iff.rfl⟩
  · rw [hRlp]
    exact inferInstanceAs (IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C))
  · rw [hRlp]
    rfl
  · intro X
    rw [hRlp]
    exact (fibration_iff (terminal.from X)).symm

example (X : C) :
    IsFibrant ((equivalence (unchanged (C := C))).functor.obj X) ↔ IsFibrant X :=
  isFibrant_iff unchanged _

example {W : MorphismProperty C} {V : MorphismProperty D}
    {P : ObjectProperty C} {Q : ObjectProperty D}
    (source : Recognition W P) (target : Recognition V Q)
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [adj.IsQuillenAdjunction]
    (hLocal : ∀ Z : D, Q Z → P (G.obj Z))
    {X Y : Localized target} (p : X ⟶ Y) (hp : fibrations (Localized target) p) :
    fibrations (Localized source)
      ((((equivalence target).inverse ⋙ G) ⋙ (equivalence source).functor).map p) := by
  have hQ : (localizedAdjunction source target adj).IsQuillenAdjunction :=
    (isQuillenAdjunction_iff_preservesLocalFibrant source target adj).mpr hLocal
  exact Adjunction.IsQuillenAdjunction.preservesFibrations
    (adj := localizedAdjunction source target adj) p hp
