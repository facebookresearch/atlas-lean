/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.Loop.OriginalBasedPathLoopComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.Loop.OriginalBasedPathConnectingLift
import MathlibExt.CategoryTheory.Comma.Arrow.OriginalComparisonSquares

/-!
# The original looped based-path Arrow and whole original connecting lift

The SAME original basedPath(loop) comparison intertwines the actual
original endpoint projection with the actual loop of basedPathProj.
Both Arrow maps, both naturality directions and the SAME original points
are retained. Applying the actual original loop map to the previously
constructed whole original based-path lift gives a genuine whole lift
over the SAME original looped projection, with its full projection and
selected point equations. No new fibration, connecting or sign law is
assumed or inferred from this point-set construction.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial MonoidalClosed SSet.modelCategoryQuillen


namespace SSet.OriginalLoopedBasedPathLiftGeometry

open CategoryTheory.OriginalLoopedEndpointCoherenceGeometry
open SSet.OriginalPathFiberComparisonGeometry
open SSet.OriginalBasedPathLoopUniversalGeometry
open SSet.OriginalBasedPathLoopComparisonGeometry
open SSet.OriginalLoopPathInterchangeGeometry
open SSet.OriginalLoopPathEndpointGeometry
open SSet.OriginalBasedPathConnectingGeometry
open SSet.LoopShiftOriginalGeometry (originalLoopPoint)

/-- The SAME actual original endpoint map is looped with its SAME original selected-point proof. -/
def originalLoopBasedProjection (X : SSet.{u}) (x : X _⦋0⦌) :
    loopSpace (basedPath X x) (basedPathPoint X x) ⟶ loopSpace X x :=
  SSet.loopSpaceMap (SSet.basedPathProj X x) (SSet.basedPathProj_basedPathPoint X x)

/-- The complete original looped endpoint map retains both SAME original loop points. -/
theorem originalLoopBasedProjection_point (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) :
    (originalLoopBasedProjection X x).app _
        (originalLoopPoint (basedPath X x) (basedPathPoint X x)) = originalLoopPoint X x :=
  originalLoopSpaceMap_point (SSet.basedPathProj X x) (SSet.basedPathProj_basedPathPoint X x)

/-- The original looped endpoint square retains both actual total inclusions and original
inner final endpoint. -/
theorem originalLoopBasedProjection_double_inclusion (X : SSet.{u}) (x : X _⦋0⦌) :
    originalLoopBasedProjection X x ≫ originalLoopDoubleInclusion X x =
      originalLoopBasedDoublePathInclusion X x ≫
        (ihom (Δ[1] : SSet.{u})).map (SSet.eval₁ : pathSpace X ⟶ X) := by
  have h := originalLoopDoubleInclusion_naturality
    (SSet.basedPathProj X x) (SSet.basedPathProj_basedPathPoint X x)
  have hv : (ihom (Δ[1] : SSet.{u})).map (SSet.basedPathProj X x) =
      (ihom (Δ[1] : SSet.{u})).map (SSet.basedPathIncl X x) ≫
        (ihom (Δ[1] : SSet.{u})).map (SSet.eval₁ : pathSpace X ⟶ X) :=
    (ihom (Δ[1] : SSet.{u})).map_comp _ _
  exact h.trans ((congrArg (fun a => originalLoopDoubleInclusion
    (basedPath X x) (basedPathPoint X x) ≫ a) hv).trans (Category.assoc _ _ _).symm)

/-- The SAME original based-loop endpoint square retains the complete outer final endpoint. -/
theorem originalBasedLoopProjection_double_inclusion (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) :
    SSet.basedPathProj (loopSpace X x) (originalLoopPoint X x) ≫ originalLoopDoubleInclusion X x =
      originalBasedLoopDoublePathInclusion X x ≫
        (SSet.eval₁ : pathSpace (pathSpace X) ⟶ pathSpace X) := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => SSet.basedPathIncl (loopSpace X x) (originalLoopPoint X x) ≫ a)
      (SSet.pathSpace_map_eval₁ (originalLoopDoubleInclusion X x)).symm).trans
        (Category.assoc _ _ _).symm)

/-- The full original forward comparison commutes with the SAME original looped endpoint map. -/
theorem originalBasedPathLoopComparisonHom_endpoint (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) :
    originalBasedPathLoopComparisonHom X x ≫ originalLoopBasedProjection X x =
      SSet.basedPathProj (loopSpace X x) (originalLoopPoint X x) :=
  originalWholeEndpointSquare
    (hMono := originalLoopDoubleInclusion_mono X x)
    (originalBasedPathLoopComparisonHom X x) (originalLoopBasedProjection X x)
    (SSet.basedPathProj (loopSpace X x) (originalLoopPoint X x)) (originalLoopDoubleInclusion X x)
    (originalLoopBasedDoublePathInclusion X x) (originalBasedLoopDoublePathInclusion X x)
    (originalDoublePathSwapIso X).hom
    ((ihom (Δ[1] : SSet.{u})).map (SSet.eval₁ : pathSpace X ⟶ X))
    (SSet.eval₁ : pathSpace (pathSpace X) ⟶ pathSpace X)
    (originalLoopBasedProjection_double_inclusion X x)
    (originalBasedPathLoopComparisonHom_projection X x)
    (originalDoublePathSwap_hom_map_evalOne X)
    (originalBasedLoopProjection_double_inclusion X x)

/-- The full original inverse comparison commutes with the SAME original based-loop endpoint. -/
theorem originalBasedPathLoopComparisonInv_endpoint (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) :
    originalBasedPathLoopComparisonInv X x ≫
        SSet.basedPathProj (loopSpace X x) (originalLoopPoint X x) =
      originalLoopBasedProjection X x :=
  originalWholeInverseEndpointSquare (originalBasedPathLoopComparisonIso X x)
    (SSet.basedPathProj (loopSpace X x) (originalLoopPoint X x)) (originalLoopBasedProjection X x)
    (originalBasedPathLoopComparisonHom_endpoint X x)

/-- Both complete original based-loop and looped based-path Arrows form the SAME full Arrow Iso. -/
def originalLoopBasedPathArrowIso (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) :
    Arrow.mk (SSet.basedPathProj (loopSpace X x) (originalLoopPoint X x)) ≅
      Arrow.mk (originalLoopBasedProjection X x) :=
  originalWholeEndpointArrowIso (originalBasedPathLoopComparisonIso X x)
    (SSet.basedPathProj (loopSpace X x) (originalLoopPoint X x)) (originalLoopBasedProjection X x)
    (originalBasedPathLoopComparisonHom_endpoint X x)

/-- The entire original forward Arrow total map is the SAME complete original comparison. -/
theorem originalLoopBasedPathArrowIso_hom_left (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) :
    (originalLoopBasedPathArrowIso X x).hom.left = originalBasedPathLoopComparisonHom X x :=
  originalWholeEndpointArrowIso_hom_left (originalBasedPathLoopComparisonIso X x)
    (SSet.basedPathProj (loopSpace X x) (originalLoopPoint X x)) (originalLoopBasedProjection X x)
    (originalBasedPathLoopComparisonHom_endpoint X x)

/-- The entire original forward Arrow base map is the SAME complete original identity. -/
theorem originalLoopBasedPathArrowIso_hom_right (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) :
    (originalLoopBasedPathArrowIso X x).hom.right = 𝟙 (loopSpace X x) :=
  originalWholeEndpointArrowIso_hom_right (originalBasedPathLoopComparisonIso X x)
    (SSet.basedPathProj (loopSpace X x) (originalLoopPoint X x)) (originalLoopBasedProjection X x)
    (originalBasedPathLoopComparisonHom_endpoint X x)

/-- The entire original inverse Arrow total map is the SAME complete original comparison. -/
theorem originalLoopBasedPathArrowIso_inv_left (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) :
    (originalLoopBasedPathArrowIso X x).inv.left = originalBasedPathLoopComparisonInv X x :=
  originalWholeEndpointArrowIso_inv_left (originalBasedPathLoopComparisonIso X x)
    (SSet.basedPathProj (loopSpace X x) (originalLoopPoint X x)) (originalLoopBasedProjection X x)
    (originalBasedPathLoopComparisonHom_endpoint X x)

/-- The entire original inverse Arrow base map is the SAME complete original identity. -/
theorem originalLoopBasedPathArrowIso_inv_right (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) :
    (originalLoopBasedPathArrowIso X x).inv.right = 𝟙 (loopSpace X x) :=
  originalWholeEndpointArrowIso_inv_right (originalBasedPathLoopComparisonIso X x)
    (SSet.basedPathProj (loopSpace X x) (originalLoopPoint X x)) (originalLoopBasedProjection X x)
    (originalBasedPathLoopComparisonHom_endpoint X x)

private theorem originalLoopMap_whole_congr {X Y : SSet.{u}} {f g : X ⟶ Y}
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f = g) (hf : f.app _ x = y) (hg : g.app _ x = y) :
    SSet.loopSpaceMap f hf = SSet.loopSpaceMap g hg := by
  cases h
  rfl

/-- The entire original looped endpoint maps retain every full original pointed-map square. -/
theorem originalLoopBasedProjection_naturality {X Y : SSet.{u}} (f : X ⟶ Y)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y) :
    SSet.loopSpaceMap (SSet.basedPathMap f h) (SSet.basedPathMap_app_point f h) ≫
        originalLoopBasedProjection Y y =
      originalLoopBasedProjection X x ≫ SSet.loopSpaceMap f h := by
  let pL := SSet.basedPathMap f h ≫ SSet.basedPathProj Y y
  let pR := SSet.basedPathProj X x ≫ f
  have hL : pL.app _ (basedPathPoint X x) = y := by
    exact (congrArg ((SSet.basedPathProj Y y).app (op ⦋0⦌))
      (SSet.basedPathMap_app_point f h)).trans
      (SSet.basedPathProj_basedPathPoint Y y)
  have hR : pR.app _ (basedPathPoint X x) = y := by
    exact (congrArg (f.app (op ⦋0⦌)) (SSet.basedPathProj_basedPathPoint X x)).trans h
  exact (SSet.loopSpaceMap_comp (SSet.basedPathMap f h) (SSet.basedPathProj Y y)
    (SSet.basedPathMap_app_point f h) (SSet.basedPathProj_basedPathPoint Y y)).symm.trans
      ((originalLoopMap_whole_congr (SSet.basedPathMap_proj f h) hL hR).trans
        (SSet.loopSpaceMap_comp (SSet.basedPathProj X x) f
          (SSet.basedPathProj_basedPathPoint X x) h))

/-- Every entire original pointed map gives the SAME complete based-loop Arrow square. -/
def originalBasedLoopArrowMap {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (f : X ⟶ Y) {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y) :
    Arrow.mk (SSet.basedPathProj (loopSpace X x) (originalLoopPoint X x)) ⟶
      Arrow.mk (SSet.basedPathProj (loopSpace Y y) (originalLoopPoint Y y)) :=
  Arrow.homMk
    (SSet.basedPathMap (SSet.loopSpaceMap f h) (originalLoopSpaceMap_point f h))
    (SSet.loopSpaceMap f h)
    (SSet.basedPathMap_proj (SSet.loopSpaceMap f h) (originalLoopSpaceMap_point f h))

/-- Every entire original pointed map gives the SAME complete looped based-path Arrow square. -/
def originalLoopBasedArrowMap {X Y : SSet.{u}} (f : X ⟶ Y)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y) :
    Arrow.mk (originalLoopBasedProjection X x) ⟶ Arrow.mk (originalLoopBasedProjection Y y) :=
  Arrow.homMk
    (SSet.loopSpaceMap (SSet.basedPathMap f h) (SSet.basedPathMap_app_point f h))
    (SSet.loopSpaceMap f h) (originalLoopBasedProjection_naturality f h)

/-- Both whole original forward Arrow comparisons retain every entire original pointed map. -/
theorem originalLoopBasedPathArrowIso_hom_naturality {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (f : X ⟶ Y)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y) :
    originalBasedLoopArrowMap f h ≫ (originalLoopBasedPathArrowIso Y y).hom =
      (originalLoopBasedPathArrowIso X x).hom ≫ originalLoopBasedArrowMap f h := by
  apply Arrow.hom_ext
  · exact originalBasedPathLoopComparisonHom_naturality f h
  · exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- Both whole original inverse Arrow comparisons retain every entire original pointed map. -/
theorem originalLoopBasedPathArrowIso_inv_naturality {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (f : X ⟶ Y)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y) :
    originalLoopBasedArrowMap f h ≫ (originalLoopBasedPathArrowIso Y y).inv =
      (originalLoopBasedPathArrowIso X x).inv ≫ originalBasedLoopArrowMap f h := by
  apply Arrow.hom_ext
  · exact originalBasedPathLoopComparisonInv_naturality f h
  · exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The full original looped based-path lift uses the SAME original comparison and SAME actual
original chosen lift, with their complete original loop maps. -/
def originalLoopedBasedPathLift (S : SSet.FibrationSequence.{u}) :
    basedPath (loopSpace S.B S.b) (originalLoopPoint S.B S.b) ⟶ loopSpace S.E S.e :=
  originalBasedPathLoopComparisonHom S.B S.b ≫
    SSet.loopSpaceMap (basedPathLift S) (basedPathLift_point S)

/-- The whole original looped lift retains the SAME entire original looped projection. -/
theorem originalLoopedBasedPathLift_projection (S : SSet.FibrationSequence.{u}) :
    originalLoopedBasedPathLift S ≫ SSet.loopSpaceMap S.p S.hb =
      SSet.basedPathProj (loopSpace S.B S.b) (originalLoopPoint S.B S.b) := by
  have hp : (basedPathLift S ≫ S.p).app _ (basedPathPoint S.B S.b) = S.b :=
    (congrArg (S.p.app (op ⦋0⦌)) (basedPathLift_point S)).trans S.hb
  have hL : SSet.loopSpaceMap (basedPathLift S) (basedPathLift_point S) ≫
      SSet.loopSpaceMap S.p S.hb = originalLoopBasedProjection S.B S.b :=
    (SSet.loopSpaceMap_comp (basedPathLift S) S.p (basedPathLift_point S) S.hb).symm.trans
      (originalLoopMap_whole_congr (basedPathLift_projection S) hp
        (SSet.basedPathProj_basedPathPoint S.B S.b))
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => originalBasedPathLoopComparisonHom S.B S.b ≫ a) hL).trans
      (originalBasedPathLoopComparisonHom_endpoint S.B S.b))

/-- The whole original looped lift retains the SAME original constant based-loop vertex. -/
theorem originalLoopedBasedPathLift_point (S : SSet.FibrationSequence.{u}) :
    (originalLoopedBasedPathLift S).app _
        (basedPathPoint (loopSpace S.B S.b) (originalLoopPoint S.B S.b)) =
      originalLoopPoint S.E S.e :=
  (congrArg ((SSet.loopSpaceMap (basedPathLift S) (basedPathLift_point S)).app (op ⦋0⦌))
    (originalBasedPathLoopComparisonHom_point S.B S.b)).trans
      (originalLoopSpaceMap_point (basedPathLift S) (basedPathLift_point S))

/-- The whole original looped lift retains the SAME entire selected total-point map. -/
theorem originalLoopedBasedPathLift_point_map (S : SSet.FibrationSequence.{u}) :
    SSet.const (X := Δ[0])
        (basedPathPoint (loopSpace S.B S.b) (originalLoopPoint S.B S.b)) ≫
          originalLoopedBasedPathLift S = SSet.const (X := Δ[0]) (originalLoopPoint S.E S.e) :=
  (SSet.const_comp _ _).trans (congrArg (fun p => SSet.const (X := Δ[0]) p)
    (originalLoopedBasedPathLift_point S))

end SSet.OriginalLoopedBasedPathLiftGeometry
