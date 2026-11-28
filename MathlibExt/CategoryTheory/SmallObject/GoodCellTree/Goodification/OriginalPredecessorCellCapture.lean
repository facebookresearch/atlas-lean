/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalLowerSubtreeChoices
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.BoundedLowerPresentation

/-!
# Actual compact-source capture inside original predecessor lower subsets

The original lower subtree uses the same whole-tree selected points and
maps. Compactness internally captures an actual bounded lower support
inside that original predecessor subset. Both its actual lower-to-lower
map and the original attaching map are retained.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t u v

namespace CategoryTheory.SmallObject.OriginalPredecessorCellCapture

open Limits LowerSetColimits OriginalLowerSubtreeChoices
  CellTreeLowerRestriction BoundedLowerSupport BoundedLowerPresentation

variable {C : Type u} [Category.{v} C]
  {P : Type w} [PartialOrder P] {A : Type t} {s : A → Arrow C} {X : C}
  (T : CellTree s X (P := P)) (L : LowerSetColimitData T.diagram)
  (B : LowerSet P)

/-- The actual endpoint comparison of a lifted lower support is its original whole-tree map. -/
theorem originalEndpointMap (D : LowerSet B) :
    (choices B L).map (le_top : D ≤ ⊤) ≫
        ((CellTreeLowerRestriction.tree T L B).endpointIso (choices B L)).hom =
      L.map (lift_le B D) := by
  let K := CellTreeLowerRestriction.tree T L B
  let M : LowerSetColimitData K.diagram := choices B L
  change M.map (le_top : D ≤ ⊤) ≫ (K.endpointIso M).hom = L.map (lift_le B D)
  apply (M.isColimit D).hom_ext
  intro p
  have hLeft : M.ι D p ≫ (M.map (le_top : D ≤ ⊤) ≫ (K.endpointIso M).hom) =
      K.inclusion p.1 := by
    rw [← Category.assoc, M.ι_map]
    exact K.ι_endpointIso_hom M p.1
  have hRight : M.ι D p ≫ L.map (lift_le B D) = K.inclusion p.1 :=
    L.ι_map (lift_le B D) (carrierIso B D p)
  exact hLeft.trans hRight.symm

variable (i : A) (g : (s i).left ⟶ (L.obj B).right)
  (chi : Cardinal.{w}) [Fact chi.IsRegular]

/-- Actual local capture data inside the original predecessor lower subset. -/
structure LocalCaptureData where
  /-- The actual original whole-carrier lower support. -/
  support : LowerSet P
  /-- Every captured original label remains in the original predecessor subset. -/
  below : support ≤ B
  /-- The original support has its actual derived cardinal bound. -/
  bound : HasCardinalLT support chi
  /-- The actual original compact-source factor into that same selected lower point. -/
  attaching : (s i).left ⟶ (L.obj support).right
  /-- The original attaching map is retained through the original lower comparison. -/
  factor : attaching ≫ (L.map below).right = g

variable [IsCardinalLocallyPresentable C chi] [IsCardinalPresentable (s i).left chi]
  (good : T.IsGood chi)

include good in
/-- Original compactness derives the actual bounded support inside its original predecessor set. -/
theorem localCapture_nonempty : Nonempty (LocalCaptureData T L B i g chi) := by
  let : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0} C
  let : HasBinaryCoproducts C := inferInstance
  let K := CellTreeLowerRestriction.tree T L B
  let M := choices B L
  have hK : K.IsGood chi := CellTreeLowerRestriction.tree_good T L B chi good
  obtain ⟨D, _, a, ha⟩ :=
    existsRawFactorContaining chi K hK M g (BoundedLowerSupport.empty chi)
  have hMap := originalEndpointMap T L B D.1
  change a ≫ ((choices B L).map (le_top : D.1 ≤ ⊤) ≫
    (K.endpointIso (choices B L)).hom).right = g at ha
  rw [hMap] at ha
  exact ⟨{
    support := lift B D.1
    below := lift_le B D.1
    bound := lift_bound B chi D.1 D.2
    attaching := a
    factor := ha }⟩

/-- Select only the local original factor whose existence was proved from real compactness. -/
def localCapture : LocalCaptureData T L B i g chi :=
  Classical.choice (localCapture_nonempty T L B i g chi good)

/-- The full original local factor keeps the same original attaching-map function. -/
theorem localCapture_factor :
    (localCapture T L B i g chi good).attaching ≫
      (L.map (localCapture T L B i g chi good).below).right = g :=
  (localCapture T L B i g chi good).factor

/-- Every actual internally captured lower label stays in the same original predecessor subset. -/
theorem localCapture_below :
    (localCapture T L B i g chi good).support ≤ B :=
  (localCapture T L B i g chi good).below

/-- The actual original support bound is internally derived, never supplied as a desired result. -/
theorem localCapture_bound :
    HasCardinalLT (localCapture T L B i g chi good).support chi :=
  (localCapture T L B i g chi good).bound

end CategoryTheory.SmallObject.OriginalPredecessorCellCapture
