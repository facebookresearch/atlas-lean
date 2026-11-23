/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.Loop.OriginalLoopedBasedPathLift

/-!
# Loops of every SAME original selected simplicial fiber

Both whole maps compare the original loopSpace of S.fiber at S.fiberPoint
with the SAME strict fiber of the original loopSpaceMap S.p S.hb.  The
inverse is the original path-of-fiber universal lift followed by the
original two-endpoint loop lift.  Both original inclusions, both selected
points, both complete inverse identities and every entire pointed
fibration-sequence square are retained.  This construction does not
assert that the original loop map is a Kan fibration.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial MonoidalClosed SSet.modelCategoryQuillen

namespace SSet.OriginalLoopFiberComparisonGeometry

open SSet.OriginalPathFiberComparisonGeometry
open SSet.OriginalBasedPathLoopUniversalGeometry
open SSet.OriginalBasedPathLoopComparisonGeometry
open CategoryTheory.OriginalLoopPathComparisonCoherenceGeometry
open SSet.LoopShiftOriginalGeometry (originalLoopPoint)

/-- The target is the SAME original strict fiber of the actual original loop map. -/
abbrev originalLoopFiberTarget (S : SSet.FibrationSequence.{u}) : SSet.{u} :=
  Subcomplex.fiber (SSet.loopSpaceMap S.p S.hb) (originalLoopPoint S.B S.b)

/-- The complete target inclusion is the original strict-fiber inclusion. -/
abbrev originalLoopFiberTargetIncl (S : SSet.FibrationSequence.{u}) :
    originalLoopFiberTarget S ⟶ loopSpace S.E S.e :=
  (Subcomplex.fiber (SSet.loopSpaceMap S.p S.hb) (originalLoopPoint S.B S.b)).ι

/-- The actual selected target point retains both original selected loop vertices. -/
def originalLoopFiberTargetPoint (S : SSet.FibrationSequence.{u}) :
    originalLoopFiberTarget S _⦋0⦌ :=
  Subcomplex.fiber.basePoint (originalLoopPoint S.E S.e)
    (originalLoopSpaceMap_point S.p S.hb)

/-- The selected original fiber inclusion retains its SAME original total vertex. -/
theorem originalFiberIncl_point (S : SSet.FibrationSequence.{u}) :
    S.fiberIncl.app _ S.fiberPoint = S.e := rfl

/-- The source-to-total function is the actual original loop of the selected fiber inclusion. -/
def originalLoopFiberImage (S : SSet.FibrationSequence.{u}) :
    loopSpace S.fiber S.fiberPoint ⟶ loopSpace S.E S.e :=
  SSet.loopSpaceMap S.fiberIncl (originalFiberIncl_point S)

/-- The complete original image retains the SAME full path inclusion square. -/
@[reassoc]
theorem originalLoopFiberImage_double_projection (S : SSet.FibrationSequence.{u}) :
    originalLoopFiberImage S ≫ originalLoopDoubleInclusion S.E S.e =
      originalLoopDoubleInclusion S.fiber S.fiberPoint ≫
        (ihom (Δ[1] : SSet.{u})).map S.fiberIncl :=
  originalLoopDoubleInclusion_naturality S.fiberIncl (originalFiberIncl_point S)

/-- The entire original image retains the SAME original constant-loop point. -/
theorem originalLoopFiberImage_point (S : SSet.FibrationSequence.{u}) :
    (originalLoopFiberImage S).app _ (originalLoopPoint S.fiber S.fiberPoint) =
      originalLoopPoint S.E S.e :=
  originalLoopSpaceMap_point S.fiberIncl (originalFiberIncl_point S)

/-- The whole original image lies over the SAME entire original constant base loop. -/
theorem originalLoopFiberImage_over_base (S : SSet.FibrationSequence.{u}) :
    originalLoopFiberImage S ≫ SSet.loopSpaceMap S.p S.hb =
      SSet.const (originalLoopPoint S.B S.b) := by
  let : Mono (originalLoopDoubleInclusion S.B S.b) :=
    originalLoopDoubleInclusion_mono S.B S.b
  apply (cancel_mono (originalLoopDoubleInclusion S.B S.b)).mp
  rw [Category.assoc, originalLoopDoubleInclusion_naturality S.p S.hb,
    ← Category.assoc, originalLoopFiberImage_double_projection, Category.assoc,
    ← Functor.map_comp, S.fiberIncl_comp, originalPathMapConstant,
    SSet.comp_const, originalLoopDoubleInclusion_point_map]

/-- The full forward comparison is the original strict-fiber universal map. -/
def originalLoopFiberComparisonHom (S : SSet.FibrationSequence.{u}) :
    loopSpace S.fiber S.fiberPoint ⟶ originalLoopFiberTarget S :=
  Subcomplex.lift (originalLoopFiberImage S)
    ((Subcomplex.range_le_fiber_iff _ _ _).mpr (originalLoopFiberImage_over_base S))

/-- The complete forward function retains its SAME actual original total inclusion. -/
@[reassoc]
theorem originalLoopFiberComparisonHom_projection (S : SSet.FibrationSequence.{u}) :
    originalLoopFiberComparisonHom S ≫ originalLoopFiberTargetIncl S =
      originalLoopFiberImage S :=
  Subcomplex.lift_ι _ _

/-- The target's entire original interval map lies in the SAME original path fiber. -/
theorem originalLoopFiberTarget_path_over_base (S : SSet.FibrationSequence.{u}) :
    (originalLoopFiberTargetIncl S ≫ originalLoopDoubleInclusion S.E S.e) ≫
        (ihom (Δ[1] : SSet.{u})).map S.p =
      SSet.const (originalPathPoint S.B S.b) := by
  rw [Category.assoc, ← originalLoopDoubleInclusion_naturality S.p S.hb,
    ← Category.assoc, Subcomplex.fiber_ι_comp, originalLoopDoubleInclusion_point_map]

/-- The complete original path-of-fiber lift retains the SAME selected original fiber. -/
def originalLoopFiberTargetPath (S : SSet.FibrationSequence.{u}) :
    originalLoopFiberTarget S ⟶ pathSpace S.fiber :=
  originalPathFiberLift S.p S.b
    (originalLoopFiberTargetIncl S ≫ originalLoopDoubleInclusion S.E S.e)
    (originalLoopFiberTarget_path_over_base S)

/-- The complete original path lift retains its SAME entire original total projection. -/
@[reassoc]
theorem originalLoopFiberTargetPath_projection (S : SSet.FibrationSequence.{u}) :
    originalLoopFiberTargetPath S ≫ (ihom (Δ[1] : SSet.{u})).map S.fiberIncl =
      originalLoopFiberTargetIncl S ≫ originalLoopDoubleInclusion S.E S.e :=
  originalPathFiberLift_projection S.p S.b _ _

private theorem originalLoopFiberTargetPath_endpoint (S : SSet.FibrationSequence.{u})
    (v : ∀ X : SSet.{u}, pathSpace X ⟶ X)
    (hv : ∀ {X Y : SSet.{u}} (f : X ⟶ Y),
      (ihom (Δ[1] : SSet.{u})).map f ≫ v Y = v X ≫ f)
    (he : originalLoopDoubleInclusion S.E S.e ≫ v S.E = SSet.const S.e) :
    originalLoopFiberTargetPath S ≫ v S.fiber = SSet.const S.fiberPoint := by
  let : Mono S.fiberIncl := inferInstanceAs (Mono (Subcomplex.fiber S.p S.b).ι)
  apply (cancel_mono S.fiberIncl).mp
  rw [Category.assoc, ← hv S.fiberIncl, ← Category.assoc,
    originalLoopFiberTargetPath_projection, Category.assoc, he, SSet.comp_const,
    SSet.const_comp]
  rfl

/-- The whole original lifted path retains its SAME entire initial fiber-point constraint. -/
theorem originalLoopFiberTargetPath_initial (S : SSet.FibrationSequence.{u}) :
    originalLoopFiberTargetPath S ≫ (SSet.eval₀ : pathSpace S.fiber ⟶ S.fiber) =
      SSet.const S.fiberPoint :=
  originalLoopFiberTargetPath_endpoint S (fun _ => SSet.eval₀)
    (fun f => SSet.pathSpace_map_eval₀ f) (originalLoopDoubleInclusion_evalZero S.E S.e)

/-- The whole original lifted path retains its SAME entire final fiber-point constraint. -/
theorem originalLoopFiberTargetPath_final (S : SSet.FibrationSequence.{u}) :
    originalLoopFiberTargetPath S ≫ (SSet.eval₁ : pathSpace S.fiber ⟶ S.fiber) =
      SSet.const S.fiberPoint :=
  originalLoopFiberTargetPath_endpoint S (fun _ => SSet.eval₁)
    (fun f => SSet.pathSpace_map_eval₁ f) (originalLoopDoubleInclusion_evalOne S.E S.e)

/-- The full inverse comparison is the SAME original two-endpoint loop universal map. -/
def originalLoopFiberComparisonInv (S : SSet.FibrationSequence.{u}) :
    originalLoopFiberTarget S ⟶ loopSpace S.fiber S.fiberPoint :=
  originalLoopUniversalLift S.fiber S.fiberPoint (originalLoopFiberTargetPath S)
    (originalLoopFiberTargetPath_initial S) (originalLoopFiberTargetPath_final S)

/-- The entire inverse function retains both original strict loop inclusions. -/
@[reassoc]
theorem originalLoopFiberComparisonInv_path_projection (S : SSet.FibrationSequence.{u}) :
    originalLoopFiberComparisonInv S ≫ originalLoopDoubleInclusion S.fiber S.fiberPoint =
      originalLoopFiberTargetPath S :=
  originalLoopUniversalLift_projection S.fiber S.fiberPoint _ _ _

/-- The complete inverse function retains the SAME whole original total interval square. -/
theorem originalLoopFiberComparisonInv_double_projection (S : SSet.FibrationSequence.{u}) :
    originalLoopFiberComparisonInv S ≫ originalLoopDoubleInclusion S.fiber S.fiberPoint ≫
        (ihom (Δ[1] : SSet.{u})).map S.fiberIncl =
      originalLoopFiberTargetIncl S ≫ originalLoopDoubleInclusion S.E S.e := by
  rw [← Category.assoc, originalLoopFiberComparisonInv_path_projection,
    originalLoopFiberTargetPath_projection]

/-- The entire inverse function retains the SAME original looped total inclusion. -/
@[reassoc]
theorem originalLoopFiberComparisonInv_projection (S : SSet.FibrationSequence.{u}) :
    originalLoopFiberComparisonInv S ≫ originalLoopFiberImage S =
      originalLoopFiberTargetIncl S := by
  let : Mono (originalLoopDoubleInclusion S.E S.e) :=
    originalLoopDoubleInclusion_mono S.E S.e
  apply (cancel_mono (originalLoopDoubleInclusion S.E S.e)).mp
  rw [Category.assoc, originalLoopFiberImage_double_projection]
  exact originalLoopFiberComparisonInv_double_projection S

/-- Both complete original comparison functions compose to the SAME source identity. -/
theorem originalLoopFiberComparison_hom_inv_id (S : SSet.FibrationSequence.{u}) :
    originalLoopFiberComparisonHom S ≫ originalLoopFiberComparisonInv S =
      𝟙 (loopSpace S.fiber S.fiberPoint) := by
  let : Mono (originalLoopDoubleInclusion S.fiber S.fiberPoint) :=
    originalLoopDoubleInclusion_mono S.fiber S.fiberPoint
  let : Mono ((ihom (Δ[1] : SSet.{u})).map S.fiberIncl) :=
    originalPathFiberInclusion_mono S.p S.b
  apply (cancel_mono (originalLoopDoubleInclusion S.fiber S.fiberPoint ≫
    (ihom (Δ[1] : SSet.{u})).map S.fiberIncl)).mp
  rw [Category.assoc, originalLoopFiberComparisonInv_double_projection,
    ← Category.assoc, originalLoopFiberComparisonHom_projection,
    originalLoopFiberImage_double_projection, Category.id_comp]

/-- Both complete original comparison functions compose to the SAME target identity. -/
theorem originalLoopFiberComparison_inv_hom_id (S : SSet.FibrationSequence.{u}) :
    originalLoopFiberComparisonInv S ≫ originalLoopFiberComparisonHom S =
      𝟙 (originalLoopFiberTarget S) := by
  let : Mono (originalLoopFiberTargetIncl S) :=
    inferInstanceAs (Mono (Subcomplex.fiber (SSet.loopSpaceMap S.p S.hb)
      (originalLoopPoint S.B S.b)).ι)
  apply (cancel_mono (originalLoopFiberTargetIncl S)).mp
  rw [Category.assoc, originalLoopFiberComparisonHom_projection,
    originalLoopFiberComparisonInv_projection, Category.id_comp]

/-- The whole original Iso retains both actual original comparison functions. -/
def originalLoopFiberComparisonIso (S : SSet.FibrationSequence.{u}) :
    loopSpace S.fiber S.fiberPoint ≅ originalLoopFiberTarget S where
  hom := originalLoopFiberComparisonHom S
  inv := originalLoopFiberComparisonInv S
  hom_inv_id := originalLoopFiberComparison_hom_inv_id S
  inv_hom_id := originalLoopFiberComparison_inv_hom_id S

/-- The entire forward comparison retains the SAME original selected fiber-loop point. -/
theorem originalLoopFiberComparisonHom_point (S : SSet.FibrationSequence.{u}) :
    (originalLoopFiberComparisonHom S).app _ (originalLoopPoint S.fiber S.fiberPoint) =
      originalLoopFiberTargetPoint S := by
  apply Subtype.ext
  exact originalLoopFiberImage_point S

/-- The entire inverse comparison retains the SAME original selected fiber-loop point. -/
theorem originalLoopFiberComparisonInv_point (S : SSet.FibrationSequence.{u}) :
    (originalLoopFiberComparisonInv S).app _ (originalLoopFiberTargetPoint S) =
      originalLoopPoint S.fiber S.fiberPoint := by
  rw [← originalLoopFiberComparisonHom_point S]
  exact ConcreteCategory.congr_hom
    (congr_app (originalLoopFiberComparisonIso S).hom_inv_id (op ⦋0⦌)) _

/-- The complete forward comparison retains the SAME entire original selected-point map. -/
theorem originalLoopFiberComparisonHom_point_map {A : SSet.{u}}
    (S : SSet.FibrationSequence.{u}) :
    SSet.const (X := A) (originalLoopPoint S.fiber S.fiberPoint) ≫
        originalLoopFiberComparisonHom S = SSet.const (originalLoopFiberTargetPoint S) :=
  (SSet.const_comp _ _).trans (congrArg (fun x => SSet.const (X := A) x)
    (originalLoopFiberComparisonHom_point S))

/-- The complete inverse comparison retains the SAME entire original selected-point map. -/
theorem originalLoopFiberComparisonInv_point_map {A : SSet.{u}}
    (S : SSet.FibrationSequence.{u}) :
    SSet.const (X := A) (originalLoopFiberTargetPoint S) ≫
        originalLoopFiberComparisonInv S = SSet.const (originalLoopPoint S.fiber S.fiberPoint) :=
  (SSet.const_comp _ _).trans (congrArg (fun x => SSet.const (X := A) x)
    (originalLoopFiberComparisonInv_point S))

/-- The entire original forward comparison retains the complete original terminal point leg. -/
theorem originalLoopFiberComparisonHom_terminal (S : SSet.FibrationSequence.{u}) :
    originalLoopFiberComparisonHom S ≫ SSet.stdSimplex.isTerminalObj₀.from
        (originalLoopFiberTarget S) =
      SSet.stdSimplex.isTerminalObj₀.from (loopSpace S.fiber S.fiberPoint) :=
  SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The entire original inverse comparison retains the complete original terminal point leg. -/
theorem originalLoopFiberComparisonInv_terminal (S : SSet.FibrationSequence.{u}) :
    originalLoopFiberComparisonInv S ≫ SSet.stdSimplex.isTerminalObj₀.from
        (loopSpace S.fiber S.fiberPoint) =
      SSet.stdSimplex.isTerminalObj₀.from (originalLoopFiberTarget S) :=
  SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

private theorem originalLoopMap_whole_congr {X Y : SSet.{u}} {f g : X ⟶ Y}
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f = g) (hf : f.app _ x = y) (hg : g.app _ x = y) :
    SSet.loopSpaceMap f hf = SSet.loopSpaceMap g hg := by
  cases h
  rfl

/-- Every complete original sequence square retains the whole original looped projection square. -/
theorem originalLoopFiberSquare {S T : SSet.FibrationSequence.{u}}
    (f : SSet.FibrationSequenceHom S T) :
    SSet.loopSpaceMap f.totalMap f.total_pt ≫ SSet.loopSpaceMap T.p T.hb =
      SSet.loopSpaceMap S.p S.hb ≫ SSet.loopSpaceMap f.baseMap f.base_pt := by
  have hL : (f.totalMap ≫ T.p).app _ S.e = T.b :=
    (congrArg (T.p.app (op ⦋0⦌)) f.total_pt).trans T.hb
  have hR : (S.p ≫ f.baseMap).app _ S.e = T.b :=
    (congrArg (f.baseMap.app (op ⦋0⦌)) S.hb).trans f.base_pt
  exact (SSet.loopSpaceMap_comp f.totalMap T.p f.total_pt T.hb).symm.trans
    ((originalLoopMap_whole_congr f.comm hL hR).trans
      (SSet.loopSpaceMap_comp S.p f.baseMap S.hb f.base_pt))

/-- Every whole original sequence square gives the SAME full actual target fiber map. -/
def originalLoopFiberTargetMap {S T : SSet.FibrationSequence.{u}}
    (f : SSet.FibrationSequenceHom S T) : originalLoopFiberTarget S ⟶ originalLoopFiberTarget T :=
  Subcomplex.mapFiber (SSet.loopSpaceMap f.totalMap f.total_pt)
    (SSet.loopSpaceMap f.baseMap f.base_pt) (originalLoopFiberSquare f)
    (originalLoopSpaceMap_point f.baseMap f.base_pt)

/-- The full original target map retains the SAME entire original looped total square. -/
@[reassoc]
theorem originalLoopFiberTargetMap_projection {S T : SSet.FibrationSequence.{u}}
    (f : SSet.FibrationSequenceHom S T) :
    originalLoopFiberTargetMap f ≫ originalLoopFiberTargetIncl T =
      originalLoopFiberTargetIncl S ≫ SSet.loopSpaceMap f.totalMap f.total_pt :=
  Subcomplex.mapFiber_ι _ _ _ _

/-- The full original target map retains the SAME original selected target point. -/
theorem originalLoopFiberTargetMap_point {S T : SSet.FibrationSequence.{u}}
    (f : SSet.FibrationSequenceHom S T) :
    (originalLoopFiberTargetMap f).app _ (originalLoopFiberTargetPoint S) =
      originalLoopFiberTargetPoint T := by
  apply Subtype.ext
  exact originalLoopSpaceMap_point f.totalMap f.total_pt

/-- Every whole original sequence square retains the full original looped selected-fiber map. -/
theorem originalLoopFiberImage_naturality {S T : SSet.FibrationSequence.{u}}
    (f : SSet.FibrationSequenceHom S T) :
    SSet.loopSpaceMap f.fiberMap f.fiberMap_app_basePoint ≫ originalLoopFiberImage T =
      originalLoopFiberImage S ≫ SSet.loopSpaceMap f.totalMap f.total_pt := by
  have hL : (f.fiberMap ≫ T.fiberIncl).app _ S.fiberPoint = T.e :=
    (congrArg (T.fiberIncl.app (op ⦋0⦌)) f.fiberMap_app_basePoint).trans
      (originalFiberIncl_point T)
  have hR : (S.fiberIncl ≫ f.totalMap).app _ S.fiberPoint = T.e :=
    (congrArg (f.totalMap.app (op ⦋0⦌)) (originalFiberIncl_point S)).trans f.total_pt
  exact (SSet.loopSpaceMap_comp f.fiberMap T.fiberIncl
    f.fiberMap_app_basePoint (originalFiberIncl_point T)).symm.trans
      ((originalLoopMap_whole_congr f.fiberMap_ι hL hR).trans
        (SSet.loopSpaceMap_comp S.fiberIncl f.totalMap (originalFiberIncl_point S) f.total_pt))

/-- Both full forward original comparisons retain every entire original pointed sequence map. -/
theorem originalLoopFiberComparisonHom_naturality {S T : SSet.FibrationSequence.{u}}
    (f : SSet.FibrationSequenceHom S T) :
    SSet.loopSpaceMap f.fiberMap f.fiberMap_app_basePoint ≫ originalLoopFiberComparisonHom T =
      originalLoopFiberComparisonHom S ≫ originalLoopFiberTargetMap f := by
  let : Mono (originalLoopFiberTargetIncl T) :=
    inferInstanceAs (Mono (Subcomplex.fiber (SSet.loopSpaceMap T.p T.hb)
      (originalLoopPoint T.B T.b)).ι)
  apply (cancel_mono (originalLoopFiberTargetIncl T)).mp
  rw [Category.assoc, originalLoopFiberComparisonHom_projection, Category.assoc,
    originalLoopFiberTargetMap_projection, ← Category.assoc,
    originalLoopFiberComparisonHom_projection]
  exact originalLoopFiberImage_naturality f

/-- Both full inverse original comparisons retain every entire original pointed sequence map. -/
theorem originalLoopFiberComparisonInv_naturality {S T : SSet.FibrationSequence.{u}}
    (f : SSet.FibrationSequenceHom S T) :
    originalLoopFiberTargetMap f ≫ originalLoopFiberComparisonInv T =
      originalLoopFiberComparisonInv S ≫ SSet.loopSpaceMap f.fiberMap f.fiberMap_app_basePoint :=
  originalWholeInverseComparisonSquare (originalLoopFiberComparisonIso S)
    (originalLoopFiberComparisonIso T)
    (SSet.loopSpaceMap f.fiberMap f.fiberMap_app_basePoint) (originalLoopFiberTargetMap f)
    (originalLoopFiberComparisonHom_naturality f)

end SSet.OriginalLoopFiberComparisonGeometry
