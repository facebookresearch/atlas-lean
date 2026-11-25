/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.MorphismProperty.CoproductCellDecomposition

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MorphismProperty.CoproductCells

#check @coordinateObj
#check @coordinateMap
#check @coordinateMap_id
#check @coordinateMap_comp
#check @coordinateDiagram
#check @coordinateDiagram_obj
#check @coordinateDiagram_map
#check @coordinateDiagram_continuous
#check @coproductDiagram
#check @coproductDiagram_continuous
#check @sigmaMap_isPushout_of_isIso
#check @cellOrder
#check @cellIndex
#check @cellDiagram
#check @cellSourceIso
#check @cellTargetIso
#check @cellSourceInjection
#check @cellTargetInjection
#check @cell_isPushout
#check @coproductMapOriginalCells
#check @coproductMapOriginalCells_diagram
#check @coproductMapOriginalCells_fac
#check @coproductMapOriginalCellsIsColimit
#check @coproductMap_originalCells

namespace CoproductCellContract

variable {C : Type u} [Category.{v} C] {ι : Type w}
  [HasColimitsOfShape (Discrete ι) C] {X Y : ι → C}
  (p : ∀ i, X i ⟶ Y i) (i : ι) (hp : ∀ j, j ≠ i → IsIso (p j))

/-- The constructed original pushout descends an arbitrary compatible original cocone. -/
def originalDesc {T : C} (a : Y i ⟶ T) (b : (∐ X) ⟶ T)
    (h : p i ≫ a = Sigma.ι X i ≫ b) : (∐ Y) ⟶ T :=
  (sigmaMap_isPushout_of_isIso p i hp).desc a b h

/-- The descent retains the original changed-coordinate leg. -/
theorem originalDesc_injection {T : C} (a : Y i ⟶ T) (b : (∐ X) ⟶ T)
    (h : p i ≫ a = Sigma.ι X i ≫ b) :
    Sigma.ι Y i ≫ originalDesc p i hp a b h = a :=
  (sigmaMap_isPushout_of_isIso p i hp).inl_desc a b h

/-- The descent retains the original whole coproduct-arrow leg. -/
theorem originalDesc_sigma {T : C} (a : Y i ⟶ T) (b : (∐ X) ⟶ T)
    (h : p i ≫ a = Sigma.ι X i ≫ b) :
    Limits.Sigma.map p ≫ originalDesc p i hp a b h = b :=
  (sigmaMap_isPushout_of_isIso p i hp).inr_desc a b h

/-- Both original leg equations determine the same unique descended map. -/
theorem originalDesc_unique {T : C} (a : Y i ⟶ T) (b : (∐ X) ⟶ T)
    (h : p i ≫ a = Sigma.ι X i ≫ b) (d : (∐ Y) ⟶ T)
    (hd₁ : Sigma.ι Y i ≫ d = a) (hd₂ : Limits.Sigma.map p ≫ d = b) :
    d = originalDesc p i hp a b h := by
  apply (sigmaMap_isPushout_of_isIso p i hp).hom_ext
  · exact hd₁.trans (originalDesc_injection p i hp a b h).symm
  · exact hd₂.trans (originalDesc_sigma p i hp a b h).symm

/-- The literal original cell, not the bottom composite, satisfies both prescribed legs. -/
theorem actualCell_square [LinearOrder ι] [SuccOrder (cellOrder ι)] :
    p i ≫ cellTargetInjection p i =
      cellSourceInjection p i ≫
        (cellDiagram p).map (homOfLE (Order.le_succ (cellIndex i))) :=
  (cell_isPushout p i).w

/-- The complete final factor retains the original coproduct arrow for any original family. -/
theorem wholeOriginalFactor [LinearOrder ι] [WellFoundedLT ι]
    [SuccOrder (cellOrder ι)] :
    (coproductMapOriginalCells p).isoBot.inv ≫
      (coproductMapOriginalCells p).incl.app ⊥ = Limits.Sigma.map p :=
  coproductMapOriginalCells_fac p

end CoproductCellContract
