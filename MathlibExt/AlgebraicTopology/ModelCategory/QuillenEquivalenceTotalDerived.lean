/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalenceDerivedComponents

/-!
# The SAME canonical total derived adjunction is an equivalence

The proved native component isomorphisms and the genuine cofibrant and
fibrant derivability structures cover every localized object. Thus the
actual canonical total derived adjunction of a Quillen equivalence has
invertible unit and counit. Its complete functors and Hom equivalence
are preserved. This is an ordinary localization theorem; an infinity
localization universal property is not asserted.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u₁ u₂ v₁ v₂
open CategoryTheory MorphismProperty

namespace HomotopicalAlgebra
variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [adj.IsQuillenEquivalence]

local notation "WC" => weakEquivalences C
local notation "WD" => weakEquivalences D
local notation "data" => quillenDerivedAdjunctionData adj

/-- Cofibrant resolutions and the proved actual unit components cover the entire original source
localization. -/
theorem quillenEquivalenceDerived_unit_isIso : IsIso (data).adjunction.unit := by
  let Φ := CofibrantObject.localizerMorphism C
  let _ : (Φ.functor ⋙ (WC).Q).EssSurj := Φ.essSurj_of_hasLeftResolutions (WC).Q
  let _ : ∀ Z, IsIso ((data).adjunction.unit.app Z) := fun Z => by
    rw [NatTrans.isIso_app_iff_of_iso (data).adjunction.unit
      ((Φ.functor ⋙ (WC).Q).objObjPreimageIso Z).symm]
    exact quillenEquivalenceDerived_unit_isIso_of_isCofibrant adj
      ((Φ.functor ⋙ (WC).Q).objPreimage Z).obj
  exact NatIso.isIso_of_isIso_app (data).adjunction.unit

/-- Fibrant resolutions and the proved actual counit components cover the entire original target
localization. -/
theorem quillenEquivalenceDerived_counit_isIso : IsIso (data).adjunction.counit := by
  let Φ := FibrantObject.localizerMorphism D
  let _ : (Φ.functor ⋙ (WD).Q).EssSurj := Φ.essSurj_of_hasRightResolutions (WD).Q
  let _ : ∀ Z, IsIso ((data).adjunction.counit.app Z) := fun Z => by
    rw [NatTrans.isIso_app_iff_of_iso (data).adjunction.counit
      ((Φ.functor ⋙ (WD).Q).objObjPreimageIso Z).symm]
    exact quillenEquivalenceDerived_counit_isIso_of_isFibrant adj
      ((Φ.functor ⋙ (WD).Q).objPreimage Z).obj
  exact NatIso.isIso_of_isIso_app (data).adjunction.counit

/-- The actual canonical total derived adjunction of the genuine Quillen equivalence, with its SAME
functors. -/
def quillenEquivalenceDerivedEquivalence : (WC).Localization ≌ (WD).Localization := by
  let _ : IsIso (data).adjunction.unit := quillenEquivalenceDerived_unit_isIso adj
  let _ : IsIso (data).adjunction.counit := quillenEquivalenceDerived_counit_isIso adj
  exact (data).adjunction.toEquivalence

/-- The whole forward functor is the SAME canonical total left derived functor. -/
theorem quillenEquivalenceDerivedEquivalence_functor :
    (quillenEquivalenceDerivedEquivalence adj).functor = (data).leftDerived := rfl

/-- The whole inverse functor is the SAME canonical total right derived functor. -/
theorem quillenEquivalenceDerivedEquivalence_inverse :
    (quillenEquivalenceDerivedEquivalence adj).inverse = (data).rightDerived := rfl

/-- The complete equivalence unit retains the actual canonical derived-adjunction unit map. -/
theorem quillenEquivalenceDerivedEquivalence_unit_hom :
    (quillenEquivalenceDerivedEquivalence adj).unitIso.hom = (data).adjunction.unit := rfl

/-- The complete equivalence counit retains the actual canonical derived-adjunction counit map. -/
theorem quillenEquivalenceDerivedEquivalence_counit_hom :
    (quillenEquivalenceDerivedEquivalence adj).counitIso.hom = (data).adjunction.counit := rfl

/-- Every actual localized adjunct uses the SAME complete canonical derived Hom equivalence. -/
theorem quillenEquivalenceDerivedEquivalence_homEquiv (X : (WC).Localization) (Y :
  (WD).Localization)
    (f : (data).leftDerived.obj X ⟶ Y) :
    (quillenEquivalenceDerivedEquivalence adj).toAdjunction.homEquiv X Y f =
      (data).adjunction.homEquiv X Y f := rfl

end HomotopicalAlgebra
