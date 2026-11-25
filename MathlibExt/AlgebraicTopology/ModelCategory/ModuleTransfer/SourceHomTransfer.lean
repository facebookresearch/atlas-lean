/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Transporting original generating sources through the actual free adjunction

The whole relative-cell diagram is mapped by the original forgetful functor.
Its coproduct attachments, pushouts, continuous history and endpoint remain
the same. Source Hom is transported by the actual free/forget Hom bijection,
at one specified original cardinal. No uniform-smallness conclusion is taken
from a fixed-cardinal input.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe w uC uD v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty CategoryTheory.SmallObject
open Opposite

namespace HomotopicalAlgebra.ModuleTransfer.SourceHomTransfer

variable {C : Type uC} [Category.{v} C] {D : Type uD} [Category.{v} D]
  (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R)

/-- The source Hom of the actual free object is the original source Hom after forgetting. -/
def sourceHomIso (X : C) : coyoneda.obj (op (L.obj X)) ≅ R ⋙ coyoneda.obj (op X) :=
  NatIso.ofComponents (fun Y => (adj.homEquiv X Y).toIso) (by
    intro Y Y' f
    ext g
    exact adj.homEquiv_naturality_right g f)

variable [HasColimitsOfSize.{w, w} C] [HasColimitsOfSize.{w, w} D] [LocallySmall.{w} D]
  [PreservesColimitsOfSize.{w, w} R]
  (P Q : MorphismProperty C) [P.IsSmall.{w}]
  [Q.IsStableUnderCoproducts.{w}] [Q.IsStableUnderCobaseChange]
  [Q.IsStableUnderTransfiniteComposition.{w}]
  (κ : Cardinal.{w}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (hImage : P.strictMap L ≤ Q.inverseImage R)

include hImage in
omit [HasColimitsOfSize.{w, w} C] [HasColimitsOfSize.{w, w} D] [LocallySmall.{w} D]
  [P.IsSmall.{w}] [Fact κ.IsRegular] in
/-- Every original mapped relative-cell transition belongs to the same target closed-cell class. -/
theorem originalCellTransitions {X Y : D} (f : X ⟶ Y)
    (c : RelativeCellComplex.{w} (fun _ : κ.ord.ToType => (P.strictMap L).homFamily) f)
    {i j : κ.ord.ToType} (φ : i ⟶ j) : Q (R.map (c.F.map φ)) := by
  let : PreservesColimitsOfSize.{0, 0} R := preservesColimitsOfSize_shrink R
  let : (Q.inverseImage R).IsStableUnderCoproducts.{w} :=
    { isStableUnderCoproductsOfShape J :=
        { condition := by
            intro F G cF cG hF hG a ha b hb
            change Q (R.map b)
            apply (inferInstance : Q.IsStableUnderColimitsOfShape (Discrete J)).condition
              (F ⋙ R) (G ⋙ R) (R.mapCocone cF) (R.mapCocone cG)
              (isColimitOfPreserves R hF) (isColimitOfPreserves R hG) (Functor.whiskerRight a R)
              (fun j => ha j) (R.map b)
            intro j
            change R.map (cF.ι.app j) ≫ R.map b = R.map (a.app j) ≫ R.map (cG.ι.app j)
            rw [← R.map_comp, ← R.map_comp]
            exact R.congr_map (hb j) } }
  let : (Q.inverseImage R).IsStableUnderCobaseChange :=
    { of_isPushout := fun sq hf => Q.of_isPushout (R.map_isPushout sq) hf }
  let : PreservesWellOrderContinuousOfShape κ.ord.ToType R :=
    { preservesColimitsOfShape := fun _ _ => by infer_instance }
  have hCop : (P.strictMap L).coproducts.{w} ≤ Q.inverseImage R :=
    (coproducts_le_iff (P := P.strictMap L)).mpr hImage
  have hPush : (P.strictMap L).coproducts.{w}.pushouts ≤ Q.inverseImage R :=
    (pushouts_le_iff (P := (P.strictMap L).coproducts.{w})).mpr hCop
  let t : ((P.strictMap L).coproducts.{w}).pushouts.TransfiniteCompositionOfShape κ.ord.ToType f :=
    { __ := c.toTransfiniteCompositionOfShape
      map_mem j hj := by
        simpa only [ofHoms_homFamily] using (c.attachCells j hj).pushouts_coproducts }
  let mapped : Q.TransfiniteCompositionOfShape κ.ord.ToType (R.map f) := (t.ofLE hPush).map
  change Q ((c.F ⋙ R).map φ)
  exact mapped.mem_map φ

include R adj hImage in
omit [HasColimitsOfSize.{w, w} C] in
/-- The complete original source-Hom certificate gives all six free-image eligibility fields at the same rank. -/
theorem originalImageSmallObject
    (hSource : ∀ {X Y : C} (i : X ⟶ Y), P i →
      ∀ (F : κ.ord.ToType ⥤ C) [F.IsWellOrderContinuous],
        (∀ {a b : κ.ord.ToType} (φ : a ⟶ b), Q (F.map φ)) →
          PreservesColimit F (coyoneda.obj (op X))) :
    (P.strictMap L).IsCardinalForSmallObjectArgument κ := by
  refine { isSmall := IsSmall.strictMap (inferInstance : P.IsSmall.{w}) L, preservesColimit := ?_ }
  intro X Y Z T i hi f c
  cases hi with
  | @map A B g hg =>
    let : PreservesWellOrderContinuousOfShape κ.ord.ToType R :=
      { preservesColimitsOfShape := fun _ _ => by infer_instance }
    let : c.F.IsWellOrderContinuous := c.toTransfiniteCompositionOfShape.isWellOrderContinuous
    let : (c.F ⋙ R).IsWellOrderContinuous := inferInstance
    let : PreservesColimit (c.F ⋙ R) (coyoneda.obj (op A)) :=
      hSource g hg (c.F ⋙ R) (fun φ => originalCellTransitions L R P Q κ hImage f c φ)
    let : PreservesColimit c.F (R ⋙ coyoneda.obj (op A)) := inferInstance
    exact preservesColimit_of_natIso c.F (sourceHomIso L R adj A).symm

end HomotopicalAlgebra.ModuleTransfer.SourceHomTransfer
