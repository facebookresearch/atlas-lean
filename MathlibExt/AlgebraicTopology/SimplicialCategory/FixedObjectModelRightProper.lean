/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectModel
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RightProper

/-!
# Genuine right properness of the original fixed-object model

Every original fixed-label Hom evaluation preserves the entire original
enriched pullback. The original full Hom weak and Kan-fibration classes
therefore reduce each actual pullback to genuine scalar right properness.
No properness or model-comparison outcome is supplied as an input.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FixedObjectModel
variable {O : Type u}
attribute [local instance] modelCategory

/-- The actual original pullback of a weak map along a full Hom fibration is weak on every SAME Hom. -/
theorem weak_of_isPullback {A B X Y : FixedObjects O}
    {p' : A ⟶ B} {f' : A ⟶ X} {f : B ⟶ Y} {p : X ⟶ Y}
    (sq : IsPullback p' f' f p) (hp : fibrations O p) (hf : weakEquivalences O f) :
    weakEquivalences O f' := by
  rw [weakEquivalences_iff] at hf ⊢
  rw [fibrations_iff] at hp
  intro x y
  let _ : Fibration (homMap p x y) := hp x y
  let _ : WeakEquivalence (homMap f x y) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr (hf x y)
  have hs : IsPullback (homMap p' x y) (homMap f' x y) (homMap f x y) (homMap p x y) :=
    sq.map (evaluation x y)
  exact (HomotopicalAlgebra.weakEquivalence_iff _).mp
    (IsRightProper.weakEquivalence_of_isPullback hs)

/-- The SAME original fixed-object model is genuinely right proper. -/
instance rightProper : IsRightProper (FixedObjects O) where
  weakEquivalences_isStableUnderBaseChangeAgainst_fibrations := by
    constructor
    intro X Y p hp
    constructor
    intro A B p' f' f sq hf
    exact weak_of_isPullback sq hp hf

end CategoryTheory.SimplicialEnrichment.FixedObjects.FixedObjectModel
