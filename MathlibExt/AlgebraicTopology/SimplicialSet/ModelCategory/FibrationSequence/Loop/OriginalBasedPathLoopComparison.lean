/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.Loop.OriginalBasedPathLoopUniversalMaps
import MathlibExt.CategoryTheory.Comma.Arrow.OriginalComparisonSquares

/-!
# The SAME original basedPath(loop) and loop(basedPath) comparison

The original double-path coordinate swap exchanges the three actual
original endpoint constraints on the two original carriers. Their full
universal maps construct both original comparison maps. Both inverse
identities, both selected point maps and all original strictly pointed
map naturalities are proved with the original inclusions. The complete
original double-path permutation stays visible; no connecting sign or
cross-degree law is assumed.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial MonoidalClosed SSet.modelCategoryQuillen


namespace SSet.OriginalBasedPathLoopComparisonGeometry

open SSet.OriginalPathFiberComparisonGeometry
open SSet.OriginalBasedPathLoopUniversalGeometry
open SSet.OriginalLoopPathInterchangeGeometry
open SSet.OriginalLoopPathEndpointGeometry
open SSet.LoopShiftOriginalGeometry (originalLoopPoint)
open CategoryTheory.OriginalLoopPathComparisonCoherenceGeometry

/-- The entire original path map of every full original constant map is the SAME constant path. -/
theorem originalPathMapConstant {A X : SSet.{u}} (x : X _⦋0⦌) :
    (ihom (Δ[1] : SSet.{u})).map (SSet.const (X := A) x) =
      SSet.const (X := pathSpace A) (originalPathPoint X x) := by
  let q : A ⟶ (Δ[0] : SSet.{u}) := SSet.stdSimplex.isTerminalObj₀.from A
  exact (congrArg (fun f => (ihom (Δ[1] : SSet.{u})).map f)
    (SSet.comp_const q x).symm).trans
      (((ihom (Δ[1] : SSet.{u})).map_comp q (SSet.const (X := Δ[0]) x)).trans
        ((congrArg (fun f => (ihom (Δ[1] : SSet.{u})).map q ≫ f)
          (originalPathPointMap X x)).trans
            ((Category.assoc _ _ _).symm.trans (SSet.comp_const _ _))))

/-- The entire SAME original based-path inclusion retains its complete initial endpoint map. -/
theorem originalBasedPathIncl_initial (X : SSet.{u}) (x : X _⦋0⦌) :
    SSet.basedPathIncl X x ≫ (SSet.eval₀ : pathSpace X ⟶ X) = SSet.const x :=
  Subcomplex.fiber_ι_comp _ _

/-- The entire original double-path map retains the full original two path-map value clause. -/
theorem originalDoublePathFunctor_map {X Y : SSet.{u}} (f : X ⟶ Y) :
    originalDoublePathFunctor.map f =
      (ihom (Δ[1] : SSet.{u})).map ((ihom (Δ[1] : SSet.{u})).map f) := rfl

/-- Every entire original loop map retains both SAME original selected loop vertices. -/
theorem originalLoopSpaceMap_point {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (f : X ⟶ Y) {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y) :
    (SSet.loopSpaceMap f h).app _ (originalLoopPoint X x) = originalLoopPoint Y y :=
  SSet.loopSpaceMap_app_point f h

/-- Both SAME original loop inclusions retain the entire original initial endpoint constraint. -/
@[reassoc]
theorem originalLoopDoubleInclusion_evalZero (X : SSet.{u}) (x : X _⦋0⦌) :
    originalLoopDoubleInclusion X x ≫ (SSet.eval₀ : pathSpace X ⟶ X) = SSet.const x := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => SSet.loopSpaceIncl X x ≫ a)
      (Subcomplex.fiber_ι_comp (SSet.eval₀ : pathSpace X ⟶ X) x)).trans
        (SSet.comp_const _ _))

/-- Both SAME original loop inclusions retain the entire original final endpoint constraint. -/
@[reassoc]
theorem originalLoopDoubleInclusion_evalOne (X : SSet.{u}) (x : X _⦋0⦌) :
    originalLoopDoubleInclusion X x ≫ (SSet.eval₁ : pathSpace X ⟶ X) = SSet.const x :=
  (Category.assoc _ _ _).trans (Subcomplex.fiber_ι_comp (SSet.basedPathProj X x) x)

/-- The SAME original based-path-of-loop inclusion retains the full inner initial constraint. -/
theorem originalBasedLoopDoublePathInclusion_innerZero (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) :
    originalBasedLoopDoublePathInclusion X x ≫
        (ihom (Δ[1] : SSet.{u})).map (SSet.eval₀ : pathSpace X ⟶ X) =
      SSet.const (originalPathPoint X x) := by
  unfold originalBasedLoopDoublePathInclusion
  rw [Category.assoc, ← Functor.map_comp, originalLoopDoubleInclusion_evalZero,
    originalPathMapConstant]
  simp only [SSet.comp_const]

/-- The SAME original based-path-of-loop inclusion retains the full inner final constraint. -/
theorem originalBasedLoopDoublePathInclusion_innerOne (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) :
    originalBasedLoopDoublePathInclusion X x ≫
        (ihom (Δ[1] : SSet.{u})).map (SSet.eval₁ : pathSpace X ⟶ X) =
      SSet.const (originalPathPoint X x) := by
  unfold originalBasedLoopDoublePathInclusion
  rw [Category.assoc, ← Functor.map_comp, originalLoopDoubleInclusion_evalOne,
    originalPathMapConstant]
  simp only [SSet.comp_const]

/-- The SAME original based-path-of-loop inclusion retains the full outer initial constraint. -/
theorem originalBasedLoopDoublePathInclusion_outerZero (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) :
    originalBasedLoopDoublePathInclusion X x ≫
        (SSet.eval₀ : pathSpace (pathSpace X) ⟶ pathSpace X) =
      SSet.const (originalPathPoint X x) := by
  unfold originalBasedLoopDoublePathInclusion
  rw [Category.assoc, SSet.pathSpace_map_eval₀, ← Category.assoc,
    originalBasedPathIncl_initial, originalLoopDoubleInclusion_point_map]

/-- The SAME original loop-of-based-path inclusion retains the full inner initial constraint. -/
theorem originalLoopBasedDoublePathInclusion_innerZero (X : SSet.{u}) (x : X _⦋0⦌) :
    originalLoopBasedDoublePathInclusion X x ≫
        (ihom (Δ[1] : SSet.{u})).map (SSet.eval₀ : pathSpace X ⟶ X) =
      SSet.const (originalPathPoint X x) := by
  unfold originalLoopBasedDoublePathInclusion
  rw [Category.assoc, ← Functor.map_comp, originalBasedPathIncl_initial, originalPathMapConstant]
  simp only [SSet.comp_const]

private theorem originalBasedPathPoint_constant_inclusion {A : SSet.{u}}
    (X : SSet.{u}) (x : X _⦋0⦌) :
    SSet.const (X := A) (basedPathPoint X x) ≫ SSet.basedPathIncl X x =
      SSet.const (X := A) (originalPathPoint X x) := by
  rw [SSet.const_comp]
  rfl

/-- The SAME original loop-of-based-path inclusion retains the full outer initial constraint. -/
theorem originalLoopBasedDoublePathInclusion_outerZero (X : SSet.{u}) (x : X _⦋0⦌) :
    originalLoopBasedDoublePathInclusion X x ≫
        (SSet.eval₀ : pathSpace (pathSpace X) ⟶ pathSpace X) =
      SSet.const (originalPathPoint X x) := by
  unfold originalLoopBasedDoublePathInclusion
  rw [Category.assoc, SSet.pathSpace_map_eval₀, ← Category.assoc,
    originalLoopDoubleInclusion_evalZero, originalBasedPathPoint_constant_inclusion]

/-- The SAME original loop-of-based-path inclusion retains the full outer final constraint. -/
theorem originalLoopBasedDoublePathInclusion_outerOne (X : SSet.{u}) (x : X _⦋0⦌) :
    originalLoopBasedDoublePathInclusion X x ≫
        (SSet.eval₁ : pathSpace (pathSpace X) ⟶ pathSpace X) =
      SSet.const (originalPathPoint X x) := by
  unfold originalLoopBasedDoublePathInclusion
  rw [Category.assoc, SSet.pathSpace_map_eval₁, ← Category.assoc,
    originalLoopDoubleInclusion_evalOne, originalBasedPathPoint_constant_inclusion]

/-- The whole original forward based-path/loop comparison uses the SAME full original swap. -/
def originalBasedPathLoopComparisonHom (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) :
    basedPath (loopSpace X x) (originalLoopPoint X x) ⟶
      loopSpace (basedPath X x) (basedPathPoint X x) :=
  originalLoopBasedDoublePathLift X x
    (originalBasedLoopDoublePathInclusion X x ≫ (originalDoublePathSwapIso X).hom)
    (by rw [Category.assoc, originalDoublePathSwap_hom_map_evalZero,
      originalBasedLoopDoublePathInclusion_outerZero])
    (by rw [Category.assoc, originalDoublePathSwap_hom_evalZero,
      originalBasedLoopDoublePathInclusion_innerZero])
    (by rw [Category.assoc, originalDoublePathSwap_hom_evalOne,
      originalBasedLoopDoublePathInclusion_innerOne])

/-- The whole original inverse based-path/loop comparison uses the SAME full original swap. -/
def originalBasedPathLoopComparisonInv (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) :
    loopSpace (basedPath X x) (basedPathPoint X x) ⟶
      basedPath (loopSpace X x) (originalLoopPoint X x) :=
  originalBasedLoopDoublePathLift X x
    (originalLoopBasedDoublePathInclusion X x ≫ (originalDoublePathSwapIso X).hom)
    (by rw [Category.assoc, originalDoublePathSwap_hom_map_evalZero,
      originalLoopBasedDoublePathInclusion_outerZero])
    (by rw [Category.assoc, originalDoublePathSwap_hom_map_evalOne,
      originalLoopBasedDoublePathInclusion_outerOne])
    (by rw [Category.assoc, originalDoublePathSwap_hom_evalZero,
      originalLoopBasedDoublePathInclusion_innerZero])

/-- The entire original forward comparison retains every full original double-path leg. -/
@[reassoc]
theorem originalBasedPathLoopComparisonHom_projection (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) :
    originalBasedPathLoopComparisonHom X x ≫ originalLoopBasedDoublePathInclusion X x =
      originalBasedLoopDoublePathInclusion X x ≫ (originalDoublePathSwapIso X).hom :=
  originalLoopBasedDoublePathLift_projection _ _ _ _ _ _

/-- The entire original inverse comparison retains every full original double-path leg. -/
@[reassoc]
theorem originalBasedPathLoopComparisonInv_projection (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) :
    originalBasedPathLoopComparisonInv X x ≫ originalBasedLoopDoublePathInclusion X x =
      originalLoopBasedDoublePathInclusion X x ≫ (originalDoublePathSwapIso X).hom :=
  originalBasedLoopDoublePathLift_projection _ _ _ _ _ _

/-- Both complete original comparison maps form an Iso of the SAME original selected carriers. -/
def originalBasedPathLoopComparisonIso (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) :
    basedPath (loopSpace X x) (originalLoopPoint X x) ≅
      loopSpace (basedPath X x) (basedPathPoint X x) where
  hom := originalBasedPathLoopComparisonHom X x
  inv := originalBasedPathLoopComparisonInv X x
  hom_inv_id := by
    let : Mono (originalBasedLoopDoublePathInclusion X x) :=
      originalBasedLoopDoublePathInclusion_mono X x
    apply (cancel_mono (originalBasedLoopDoublePathInclusion X x)).mp
    rw [Category.assoc, originalBasedPathLoopComparisonInv_projection,
      ← Category.assoc, originalBasedPathLoopComparisonHom_projection,
      Category.assoc, originalDoublePathSwapIso_involution, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    let : Mono (originalLoopBasedDoublePathInclusion X x) :=
      originalLoopBasedDoublePathInclusion_mono X x
    apply (cancel_mono (originalLoopBasedDoublePathInclusion X x)).mp
    rw [Category.assoc, originalBasedPathLoopComparisonHom_projection,
      ← Category.assoc, originalBasedPathLoopComparisonInv_projection,
      Category.assoc, originalDoublePathSwapIso_involution, Category.comp_id, Category.id_comp]

private theorem originalBasedLoopInclusion_point (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) :
    (originalBasedLoopDoublePathInclusion X x).app _
        (basedPathPoint (loopSpace X x) (originalLoopPoint X x)) =
      originalPathPoint (pathSpace X) (originalPathPoint X x) :=
  originalPathMapPoint (originalLoopDoubleInclusion X x) (originalLoopDoubleInclusion_point X x)

private theorem originalLoopBasedInclusion_point (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) :
    (originalLoopBasedDoublePathInclusion X x).app _
        (originalLoopPoint (basedPath X x) (basedPathPoint X x)) =
      originalPathPoint (pathSpace X) (originalPathPoint X x) := by
  have h : (SSet.basedPathIncl X x).app _ (basedPathPoint X x) = originalPathPoint X x := rfl
  exact (congrArg (((ihom (Δ[1] : SSet.{u})).map (SSet.basedPathIncl X x)).app _)
    (originalLoopDoubleInclusion_point (basedPath X x) (basedPathPoint X x))).trans
      (originalPathMapPoint (SSet.basedPathIncl X x) h)

/-- The whole original based-path-of-loop point map retains its SAME original constant square. -/
theorem originalBasedLoopDoublePathInclusion_point_map (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) :
    SSet.const (X := Δ[0]) (basedPathPoint (loopSpace X x) (originalLoopPoint X x)) ≫
        originalBasedLoopDoublePathInclusion X x =
      SSet.const (X := Δ[0]) x ≫ originalDoubleConstPathNatTrans.app X := by
  change _ = SSet.const (X := Δ[0]) x ≫ (SSet.constPath X ≫ SSet.constPath (pathSpace X))
  rw [← Category.assoc, SSet.const_comp, SSet.const_comp]
  exact (SSet.const_comp _ _).trans (congrArg (fun p => SSet.const (X := Δ[0]) p)
    (originalBasedLoopInclusion_point X x))

/-- The whole original loop-of-based-path point map retains its SAME original constant square. -/
theorem originalLoopBasedDoublePathInclusion_point_map (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) :
    SSet.const (X := Δ[0]) (originalLoopPoint (basedPath X x) (basedPathPoint X x)) ≫
        originalLoopBasedDoublePathInclusion X x =
      SSet.const (X := Δ[0]) x ≫ originalDoubleConstPathNatTrans.app X := by
  change _ = SSet.const (X := Δ[0]) x ≫ (SSet.constPath X ≫ SSet.constPath (pathSpace X))
  rw [← Category.assoc, SSet.const_comp, SSet.const_comp]
  exact (SSet.const_comp _ _).trans (congrArg (fun p => SSet.const (X := Δ[0]) p)
    (originalLoopBasedInclusion_point X x))

/-- The full original forward comparison preserves the SAME entire original selected point map. -/
theorem originalBasedPathLoopComparisonHom_point_map (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) :
    SSet.const (X := Δ[0]) (basedPathPoint (loopSpace X x) (originalLoopPoint X x)) ≫
        originalBasedPathLoopComparisonHom X x =
      SSet.const (X := Δ[0]) (originalLoopPoint (basedPath X x) (basedPathPoint X x)) := by
  let : Mono (originalLoopBasedDoublePathInclusion X x) :=
    originalLoopBasedDoublePathInclusion_mono X x
  apply (cancel_mono (originalLoopBasedDoublePathInclusion X x)).mp
  rw [Category.assoc, originalBasedPathLoopComparisonHom_projection, ← Category.assoc,
    originalBasedLoopDoublePathInclusion_point_map]
  exact (originalDoublePathSwapIso_constant_point_map X x).trans
    (originalLoopBasedDoublePathInclusion_point_map X x).symm

private theorem originalConstAtZero {A B : SSet.{u}} (b : B _⦋0⦌) (a : A _⦋0⦌) :
    (SSet.const b).app _ a = b := by
  change B.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ (0 : Fin 1)).op b = b
  have h : SimplexCategory.const ⦋0⦌ ⦋0⦌ (0 : Fin 1) = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
  rw [h, op_id, B.map_id]
  rfl

/-- The entire original forward comparison preserves the SAME original based loop vertex. -/
theorem originalBasedPathLoopComparisonHom_point (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) :
    (originalBasedPathLoopComparisonHom X x).app _
        (basedPathPoint (loopSpace X x) (originalLoopPoint X x)) =
      originalLoopPoint (basedPath X x) (basedPathPoint X x) := by
  let z : (Δ[0] : SSet.{u}) _⦋0⦌ := SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)
  have h := ConcreteCategory.congr_hom
    (congr_app (originalBasedPathLoopComparisonHom_point_map X x) (op ⦋0⦌)) z
  exact (congrArg ((originalBasedPathLoopComparisonHom X x).app _)
    (originalConstAtZero _ z)).symm.trans (h.trans (originalConstAtZero _ z))

/-- The entire original inverse comparison preserves the SAME original chosen based-path point. -/
theorem originalBasedPathLoopComparisonInv_point (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) :
    (originalBasedPathLoopComparisonInv X x).app _
        (originalLoopPoint (basedPath X x) (basedPathPoint X x)) =
      basedPathPoint (loopSpace X x) (originalLoopPoint X x) := by
  rw [← originalBasedPathLoopComparisonHom_point X x]
  exact ConcreteCategory.congr_hom
    (congr_app (originalBasedPathLoopComparisonIso X x).hom_inv_id (op ⦋0⦌)) _

/-- Every entire original strictly pointed map preserves the full double loop inclusion. -/
@[reassoc]
theorem originalLoopDoubleInclusion_naturality {X Y : SSet.{u}} (f : X ⟶ Y)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y) :
    SSet.loopSpaceMap f h ≫ originalLoopDoubleInclusion Y y =
      originalLoopDoubleInclusion X x ≫ (ihom (Δ[1] : SSet.{u})).map f := by
  unfold originalLoopDoubleInclusion
  rw [← Category.assoc, SSet.loopSpaceMap_ι, Category.assoc, SSet.basedPathMap_ι,
    ← Category.assoc]

/-- Every entire original strictly pointed map preserves the SAME based-path-of-loop double
inclusion. -/
@[reassoc]
theorem originalBasedLoopDoublePathInclusion_naturality {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (f : X ⟶ Y)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y) :
    SSet.basedPathMap (SSet.loopSpaceMap f h) (originalLoopSpaceMap_point f h) ≫
        originalBasedLoopDoublePathInclusion Y y =
      originalBasedLoopDoublePathInclusion X x ≫ originalDoublePathFunctor.map f := by
  unfold originalBasedLoopDoublePathInclusion
  rw [← Category.assoc, SSet.basedPathMap_ι, Category.assoc, ← Functor.map_comp,
    originalLoopDoubleInclusion_naturality, Functor.map_comp, ← Category.assoc]
  exact congrArg (fun a => originalBasedLoopDoublePathInclusion X x ≫ a)
    (originalDoublePathFunctor_map f).symm

/-- Every entire original strictly pointed map preserves the SAME loop-of-based-path double
inclusion. -/
@[reassoc]
theorem originalLoopBasedDoublePathInclusion_naturality {X Y : SSet.{u}}
    (f : X ⟶ Y) {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y) :
    SSet.loopSpaceMap (SSet.basedPathMap f h) (SSet.basedPathMap_app_point f h) ≫
        originalLoopBasedDoublePathInclusion Y y =
      originalLoopBasedDoublePathInclusion X x ≫ originalDoublePathFunctor.map f := by
  unfold originalLoopBasedDoublePathInclusion
  rw [← Category.assoc, originalLoopDoubleInclusion_naturality, Category.assoc,
    ← Functor.map_comp, SSet.basedPathMap_ι, Functor.map_comp, ← Category.assoc]
  exact congrArg (fun a => originalLoopBasedDoublePathInclusion X x ≫ a)
    (originalDoublePathFunctor_map f).symm

/-- Every entire original strictly pointed map preserves BOTH full forward comparison functions. -/
theorem originalBasedPathLoopComparisonHom_naturality {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (f : X ⟶ Y)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y) :
    SSet.basedPathMap (SSet.loopSpaceMap f h) (originalLoopSpaceMap_point f h) ≫
        originalBasedPathLoopComparisonHom Y y =
      originalBasedPathLoopComparisonHom X x ≫
        SSet.loopSpaceMap (SSet.basedPathMap f h) (SSet.basedPathMap_app_point f h) := by
  exact originalWholeComparisonSquare
    (hMono := originalLoopBasedDoublePathInclusion_mono Y y)
    (SSet.basedPathMap (SSet.loopSpaceMap f h) (originalLoopSpaceMap_point f h))
    (SSet.loopSpaceMap (SSet.basedPathMap f h) (SSet.basedPathMap_app_point f h))
    (originalDoublePathFunctor.map f)
    (originalBasedLoopDoublePathInclusion X x) (originalBasedLoopDoublePathInclusion Y y)
    (originalLoopBasedDoublePathInclusion X x) (originalLoopBasedDoublePathInclusion Y y)
    (originalDoublePathSwapIso X).hom (originalDoublePathSwapIso Y).hom
    (originalBasedPathLoopComparisonHom X x) (originalBasedPathLoopComparisonHom Y y)
    (originalBasedPathLoopComparisonHom_projection X x)
    (originalBasedPathLoopComparisonHom_projection Y y)
    (originalBasedLoopDoublePathInclusion_naturality f h)
    (originalLoopBasedDoublePathInclusion_naturality f h)
    (originalDoublePathSwapIso_hom_naturality f)

/-- Every entire original strictly pointed map preserves BOTH full inverse comparison functions. -/
theorem originalBasedPathLoopComparisonInv_naturality {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] (f : X ⟶ Y)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y) :
    SSet.loopSpaceMap (SSet.basedPathMap f h) (SSet.basedPathMap_app_point f h) ≫
        originalBasedPathLoopComparisonInv Y y =
      originalBasedPathLoopComparisonInv X x ≫
        SSet.basedPathMap (SSet.loopSpaceMap f h) (originalLoopSpaceMap_point f h) := by
  exact originalWholeInverseComparisonSquare
    (originalBasedPathLoopComparisonIso X x) (originalBasedPathLoopComparisonIso Y y)
    (SSet.basedPathMap (SSet.loopSpaceMap f h) (originalLoopSpaceMap_point f h))
    (SSet.loopSpaceMap (SSet.basedPathMap f h) (SSet.basedPathMap_app_point f h))
    (originalBasedPathLoopComparisonHom_naturality f h)

end SSet.OriginalBasedPathLoopComparisonGeometry
