/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.Loop.OriginalPathFiberComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.BasedPathLoop
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.LoopConnectingHomotopy

/-!
# Full universal maps into the original based-path and loop carriers

All lifts here use the SAME original strict fiber objects and their
original inclusions. The original path-of-fiber Iso supplies whole lifts
through the mapped original fiber inclusion. The original based-path and
loop objects then give both full maps from actual interval squares whose
three original endpoint constraints are constant at the SAME original
chosen point. Every total projection and uniqueness property is proved.
These are the two full original carriers for the subsequent coordinate
comparison; no connecting or sign law is an input.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial MonoidalClosed SSet.modelCategoryQuillen

namespace SSet.OriginalBasedPathLoopUniversalGeometry

open SSet.OriginalPathFiberComparisonGeometry
open SSet.LoopShiftOriginalGeometry (originalLoopPoint)

/-- The actual original path image of every whole original fiber inclusion is monic. -/
theorem originalPathFiberInclusion_mono {E B : SSet.{u}} (f : E ⟶ B) (b : B _⦋0⦌) :
    Mono ((ihom (Δ[1] : SSet.{u})).map (Subcomplex.fiber f b).ι) := by
  rw [← originalPathFiberIso_hom_fst f b]
  infer_instance

/-- The full original path-to-fiber lift uses both complete original comparison maps. -/
def originalPathFiberLift {A E B : SSet.{u}} (f : E ⟶ B) (b : B _⦋0⦌)
    (g : A ⟶ pathSpace E)
    (hg : g ≫ (ihom (Δ[1] : SSet.{u})).map f = SSet.const (originalPathPoint B b)) :
    A ⟶ pathSpace (Subcomplex.fiber f b : SSet.{u}) :=
  Subcomplex.lift g ((Subcomplex.range_le_fiber_iff _ _ _).mpr hg) ≫
    (originalPathFiberIso f b).inv

/-- Every full original lifted map retains its SAME entire mapped total projection. -/
@[reassoc]
theorem originalPathFiberLift_projection {A E B : SSet.{u}} (f : E ⟶ B) (b : B _⦋0⦌)
    (g : A ⟶ pathSpace E)
    (hg : g ≫ (ihom (Δ[1] : SSet.{u})).map f = SSet.const (originalPathPoint B b)) :
    originalPathFiberLift f b g hg ≫ (ihom (Δ[1] : SSet.{u})).map (Subcomplex.fiber f b).ι = g := by
  unfold originalPathFiberLift
  rw [Category.assoc, originalPathFiberIso_inv_fst, Subcomplex.lift_ι]

/-- The SAME entire original mapped projection determines the full original lift uniquely. -/
theorem originalPathFiberLift_unique {A E B : SSet.{u}} (f : E ⟶ B) (b : B _⦋0⦌)
    (g : A ⟶ pathSpace E)
    (hg : g ≫ (ihom (Δ[1] : SSet.{u})).map f = SSet.const (originalPathPoint B b))
    (m : A ⟶ pathSpace (Subcomplex.fiber f b : SSet.{u}))
    (hm : m ≫ (ihom (Δ[1] : SSet.{u})).map (Subcomplex.fiber f b).ι = g) :
    m = originalPathFiberLift f b g hg := by
  let : Mono ((ihom (Δ[1] : SSet.{u})).map (Subcomplex.fiber f b).ι) :=
    originalPathFiberInclusion_mono f b
  exact (cancel_mono _).mp (hm.trans (originalPathFiberLift_projection f b g hg).symm)

/-- The whole based-path lift is the SAME original strict-fiber universal map. -/
def originalBasedPathUniversalLift {A : SSet.{u}} (X : SSet.{u}) (x : X _⦋0⦌)
    (g : A ⟶ pathSpace X) (h₀ : g ≫ (SSet.eval₀ : pathSpace X ⟶ X) = SSet.const x) :
    A ⟶ basedPath X x :=
  Subcomplex.lift g ((Subcomplex.range_le_fiber_iff _ _ _).mpr h₀)

/-- The full original based-path universal map retains its SAME original inclusion. -/
@[reassoc]
theorem originalBasedPathUniversalLift_projection {A : SSet.{u}} (X : SSet.{u})
    (x : X _⦋0⦌) (g : A ⟶ pathSpace X)
    (h₀ : g ≫ (SSet.eval₀ : pathSpace X ⟶ X) = SSet.const x) :
    originalBasedPathUniversalLift X x g h₀ ≫ SSet.basedPathIncl X x = g :=
  Subcomplex.lift_ι _ _

/-- The complete original based-path projection retains its SAME entire final-endpoint map. -/
@[reassoc]
theorem originalBasedPathUniversalLift_final {A : SSet.{u}} (X : SSet.{u})
    (x : X _⦋0⦌) (g : A ⟶ pathSpace X)
    (h₀ : g ≫ (SSet.eval₀ : pathSpace X ⟶ X) = SSet.const x) :
    originalBasedPathUniversalLift X x g h₀ ≫ SSet.basedPathProj X x =
      g ≫ (SSet.eval₁ : pathSpace X ⟶ X) := by
  change originalBasedPathUniversalLift X x g h₀ ≫
    (SSet.basedPathIncl X x ≫ SSet.eval₁) = _
  rw [← Category.assoc, originalBasedPathUniversalLift_projection]

/-- The full original loop inclusion retains both SAME original fiber inclusions. -/
def originalLoopDoubleInclusion (X : SSet.{u}) (x : X _⦋0⦌) : loopSpace X x ⟶ pathSpace X :=
  SSet.loopSpaceIncl X x ≫ SSet.basedPathIncl X x

/-- Both full original strict-fiber inclusions make the SAME complete loop inclusion monic. -/
theorem originalLoopDoubleInclusion_mono (X : SSet.{u}) (x : X _⦋0⦌) :
    Mono (originalLoopDoubleInclusion X x) := by
  let : Mono (SSet.loopSpaceIncl X x) := inferInstanceAs
    (Mono (Subcomplex.fiber (SSet.basedPathProj X x) x).ι)
  let : Mono (SSet.basedPathIncl X x) := inferInstanceAs
    (Mono (Subcomplex.fiber (SSet.eval₀ : pathSpace X ⟶ X) x).ι)
  exact inferInstanceAs (Mono (SSet.loopSpaceIncl X x ≫ SSet.basedPathIncl X x))

/-- The SAME full original loop inclusion remains monic after the actual original path functor. -/
theorem originalPathLoopDoubleInclusion_mono (X : SSet.{u}) (x : X _⦋0⦌) :
    Mono ((ihom (Δ[1] : SSet.{u})).map (originalLoopDoubleInclusion X x)) := by
  let : Mono ((ihom (Δ[1] : SSet.{u})).map (SSet.loopSpaceIncl X x)) :=
    originalPathFiberInclusion_mono (SSet.basedPathProj X x) x
  let : Mono ((ihom (Δ[1] : SSet.{u})).map (SSet.basedPathIncl X x)) :=
    originalPathFiberInclusion_mono (SSet.eval₀ : pathSpace X ⟶ X) x
  change Mono ((ihom (Δ[1] : SSet.{u})).map
    (SSet.loopSpaceIncl X x ≫ SSet.basedPathIncl X x))
  rw [Functor.map_comp]
  infer_instance

/-- The whole original chosen loop point retains its SAME constant-path projection. -/
theorem originalLoopDoubleInclusion_point (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) :
    (originalLoopDoubleInclusion X x).app _ (originalLoopPoint X x) =
      originalPathPoint X x := rfl

/-- The whole original chosen loop point map retains its SAME full constant-path projection. -/
@[reassoc]
theorem originalLoopDoubleInclusion_point_map {A : SSet.{u}} (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) :
    SSet.const (X := A) (originalLoopPoint X x) ≫ originalLoopDoubleInclusion X x =
      SSet.const (X := A) (originalPathPoint X x) :=
  (SSet.const_comp _ _).trans (congrArg (fun p => SSet.const (X := A) p)
    (originalLoopDoubleInclusion_point X x))

/-- The complete original loop universal map lifts through both SAME original strict fibers. -/
def originalLoopUniversalLift {A : SSet.{u}} (X : SSet.{u}) (x : X _⦋0⦌)
    (g : A ⟶ pathSpace X)
    (h₀ : g ≫ (SSet.eval₀ : pathSpace X ⟶ X) = SSet.const x)
    (h₁ : g ≫ (SSet.eval₁ : pathSpace X ⟶ X) = SSet.const x) : A ⟶ loopSpace X x :=
  Subcomplex.lift (originalBasedPathUniversalLift X x g h₀)
    ((Subcomplex.range_le_fiber_iff _ _ _).mpr
      ((originalBasedPathUniversalLift_final X x g h₀).trans h₁))

/-- The whole original loop universal map retains its SAME first strict-fiber inclusion. -/
@[reassoc]
theorem originalLoopUniversalLift_first_projection {A : SSet.{u}} (X : SSet.{u})
    (x : X _⦋0⦌) (g : A ⟶ pathSpace X)
    (h₀ : g ≫ (SSet.eval₀ : pathSpace X ⟶ X) = SSet.const x)
    (h₁ : g ≫ (SSet.eval₁ : pathSpace X ⟶ X) = SSet.const x) :
    originalLoopUniversalLift X x g h₀ h₁ ≫ SSet.loopSpaceIncl X x =
      originalBasedPathUniversalLift X x g h₀ := Subcomplex.lift_ι _ _

/-- The whole original loop universal map retains both SAME original strict-fiber inclusions. -/
@[reassoc]
theorem originalLoopUniversalLift_projection {A : SSet.{u}} (X : SSet.{u})
    (x : X _⦋0⦌) (g : A ⟶ pathSpace X)
    (h₀ : g ≫ (SSet.eval₀ : pathSpace X ⟶ X) = SSet.const x)
    (h₁ : g ≫ (SSet.eval₁ : pathSpace X ⟶ X) = SSet.const x) :
    originalLoopUniversalLift X x g h₀ h₁ ≫ originalLoopDoubleInclusion X x = g := by
  change originalLoopUniversalLift X x g h₀ h₁ ≫
    (SSet.loopSpaceIncl X x ≫ SSet.basedPathIncl X x) = _
  rw [← Category.assoc, originalLoopUniversalLift_first_projection,
    originalBasedPathUniversalLift_projection]

/-- The SAME whole original double inclusion determines every complete original loop lift. -/
theorem originalLoopUniversalLift_unique {A : SSet.{u}} (X : SSet.{u})
    (x : X _⦋0⦌) (g : A ⟶ pathSpace X)
    (h₀ : g ≫ (SSet.eval₀ : pathSpace X ⟶ X) = SSet.const x)
    (h₁ : g ≫ (SSet.eval₁ : pathSpace X ⟶ X) = SSet.const x)
    (m : A ⟶ loopSpace X x) (hm : m ≫ originalLoopDoubleInclusion X x = g) :
    m = originalLoopUniversalLift X x g h₀ h₁ := by
  let : Mono (originalLoopDoubleInclusion X x) := originalLoopDoubleInclusion_mono X x
  exact (cancel_mono _).mp (hm.trans (originalLoopUniversalLift_projection X x g h₀ h₁).symm)

/-- The SAME full original based-path-of-loop carrier retains its entire double-path inclusion. -/
def originalBasedLoopDoublePathInclusion (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) :
    basedPath (loopSpace X x) (originalLoopPoint X x) ⟶ pathSpace (pathSpace X) :=
  SSet.basedPathIncl (loopSpace X x) (originalLoopPoint X x) ≫
    (ihom (Δ[1] : SSet.{u})).map (originalLoopDoubleInclusion X x)

/-- The SAME full original loop-of-based-path carrier retains its entire double-path inclusion. -/
def originalLoopBasedDoublePathInclusion (X : SSet.{u}) (x : X _⦋0⦌) :
    loopSpace (basedPath X x) (basedPathPoint X x) ⟶ pathSpace (pathSpace X) :=
  originalLoopDoubleInclusion (basedPath X x) (basedPathPoint X x) ≫
    (ihom (Δ[1] : SSet.{u})).map (SSet.basedPathIncl X x)

/-- The entire original based-path-of-loop inclusion is genuinely monic on its SAME carrier. -/
theorem originalBasedLoopDoublePathInclusion_mono (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) : Mono (originalBasedLoopDoublePathInclusion X x) := by
  let : Mono (SSet.basedPathIncl (loopSpace X x) (originalLoopPoint X x)) := inferInstanceAs
    (Mono (Subcomplex.fiber (SSet.eval₀ : pathSpace (loopSpace X x) ⟶ loopSpace X x)
      (originalLoopPoint X x)).ι)
  let : Mono ((ihom (Δ[1] : SSet.{u})).map (originalLoopDoubleInclusion X x)) :=
    originalPathLoopDoubleInclusion_mono X x
  exact inferInstanceAs (Mono (SSet.basedPathIncl (loopSpace X x) (originalLoopPoint X x) ≫
    (ihom (Δ[1] : SSet.{u})).map (originalLoopDoubleInclusion X x)))

/-- The entire original loop-of-based-path inclusion is genuinely monic on its SAME carrier. -/
theorem originalLoopBasedDoublePathInclusion_mono (X : SSet.{u}) (x : X _⦋0⦌) :
    Mono (originalLoopBasedDoublePathInclusion X x) := by
  let : Mono (originalLoopDoubleInclusion (basedPath X x) (basedPathPoint X x)) :=
    originalLoopDoubleInclusion_mono _ _
  let : Mono ((ihom (Δ[1] : SSet.{u})).map (SSet.basedPathIncl X x)) :=
    originalPathFiberInclusion_mono (SSet.eval₀ : pathSpace X ⟶ X) x
  exact inferInstanceAs (Mono (originalLoopDoubleInclusion (basedPath X x) (basedPathPoint X x) ≫
    (ihom (Δ[1] : SSet.{u})).map (SSet.basedPathIncl X x)))

private theorem originalBasedPathPoint_inclusion (X : SSet.{u}) (x : X _⦋0⦌) :
    (SSet.basedPathIncl X x).app _ (basedPathPoint X x) = originalPathPoint X x := rfl

private theorem originalBasedPathPoint_constant_inclusion {A : SSet.{u}}
    (X : SSet.{u}) (x : X _⦋0⦌) :
    SSet.const (X := A) (basedPathPoint X x) ≫ SSet.basedPathIncl X x =
      SSet.const (X := A) (originalPathPoint X x) :=
  (SSet.const_comp _ _).trans (congrArg (fun p => SSet.const (X := A) p)
    (originalBasedPathPoint_inclusion X x))

/-- Every original interval square with the two original inner constraints lifts to the SAME
original loop path, preserving its entire double inclusion. -/
def originalBasedLoopSquarePath {A : SSet.{u}} (X : SSet.{u})
    (x : X _⦋0⦌) (g : A ⟶ pathSpace (pathSpace X))
    (h₀ : g ≫ (ihom (Δ[1] : SSet.{u})).map (SSet.eval₀ : pathSpace X ⟶ X) =
      SSet.const (originalPathPoint X x))
    (h₁ : g ≫ (ihom (Δ[1] : SSet.{u})).map (SSet.eval₁ : pathSpace X ⟶ X) =
      SSet.const (originalPathPoint X x)) : A ⟶ pathSpace (loopSpace X x) := by
  let m := originalPathFiberLift (SSet.eval₀ : pathSpace X ⟶ X) x g h₀
  have hm : m ≫ (ihom (Δ[1] : SSet.{u})).map (SSet.basedPathProj X x) =
      SSet.const (originalPathPoint X x) := by
    change m ≫ (ihom (Δ[1] : SSet.{u})).map
      (SSet.basedPathIncl X x ≫ SSet.eval₁) = _
    rw [Functor.map_comp, ← Category.assoc, originalPathFiberLift_projection]
    exact h₁
  exact originalPathFiberLift (SSet.basedPathProj X x) x m hm

/-- Every full original interval-square lift retains its SAME entire original loop path
projection. -/
@[reassoc]
theorem originalBasedLoopSquarePath_projection {A : SSet.{u}} (X : SSet.{u})
    (x : X _⦋0⦌) (g : A ⟶ pathSpace (pathSpace X))
    (h₀ : g ≫ (ihom (Δ[1] : SSet.{u})).map (SSet.eval₀ : pathSpace X ⟶ X) =
      SSet.const (originalPathPoint X x))
    (h₁ : g ≫ (ihom (Δ[1] : SSet.{u})).map (SSet.eval₁ : pathSpace X ⟶ X) =
      SSet.const (originalPathPoint X x)) :
    originalBasedLoopSquarePath X x g h₀ h₁ ≫
        (ihom (Δ[1] : SSet.{u})).map (originalLoopDoubleInclusion X x) = g := by
  let m : A ⟶ pathSpace (basedPath X x) :=
    originalPathFiberLift (SSet.eval₀ : pathSpace X ⟶ X) x g h₀
  have hmProjection : m ≫ (ihom (Δ[1] : SSet.{u})).map (SSet.basedPathIncl X x) = g :=
    originalPathFiberLift_projection (SSet.eval₀ : pathSpace X ⟶ X) x g h₀
  have hm : m ≫ (ihom (Δ[1] : SSet.{u})).map (SSet.basedPathProj X x) =
      SSet.const (originalPathPoint X x) := by
    exact (congrArg (fun a => m ≫ a) ((ihom (Δ[1] : SSet.{u})).map_comp
      (SSet.basedPathIncl X x) (SSet.eval₁ : pathSpace X ⟶ X))).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun a => a ≫ (ihom (Δ[1] : SSet.{u})).map
            (SSet.eval₁ : pathSpace X ⟶ X)) hmProjection).trans h₁))
  let q := originalPathFiberLift (SSet.basedPathProj X x) x m hm
  have hq : originalBasedLoopSquarePath X x g h₀ h₁ = q := rfl
  have hMap : (ihom (Δ[1] : SSet.{u})).map (originalLoopDoubleInclusion X x) =
      (ihom (Δ[1] : SSet.{u})).map (SSet.loopSpaceIncl X x) ≫
        (ihom (Δ[1] : SSet.{u})).map (SSet.basedPathIncl X x) :=
    Functor.map_comp _ _ _
  have hFirst : q ≫ (ihom (Δ[1] : SSet.{u})).map (SSet.loopSpaceIncl X x) = m :=
    originalPathFiberLift_projection (SSet.basedPathProj X x) x m hm
  have hSecond : m ≫ (ihom (Δ[1] : SSet.{u})).map (SSet.basedPathIncl X x) = g :=
    originalPathFiberLift_projection (SSet.eval₀ : pathSpace X ⟶ X) x g h₀
  exact (congrArg (fun a => a ≫ (ihom (Δ[1] : SSet.{u})).map
    (originalLoopDoubleInclusion X x)) hq).trans
      ((congrArg (fun a => q ≫ a) hMap).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun a => a ≫ (ihom (Δ[1] : SSet.{u})).map
            (SSet.basedPathIncl X x)) hFirst).trans hSecond)))

/-- The third SAME original constraint fixes the full original loop path at its SAME chosen loop. -/
theorem originalBasedLoopSquarePath_initial {A : SSet.{u}} (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) (g : A ⟶ pathSpace (pathSpace X))
    (h₀ : g ≫ (ihom (Δ[1] : SSet.{u})).map (SSet.eval₀ : pathSpace X ⟶ X) =
      SSet.const (originalPathPoint X x))
    (h₁ : g ≫ (ihom (Δ[1] : SSet.{u})).map (SSet.eval₁ : pathSpace X ⟶ X) =
      SSet.const (originalPathPoint X x))
    (hb₀ : g ≫ (SSet.eval₀ : pathSpace (pathSpace X) ⟶ pathSpace X) =
      SSet.const (originalPathPoint X x)) :
    originalBasedLoopSquarePath X x g h₀ h₁ ≫
        (SSet.eval₀ : pathSpace (loopSpace X x) ⟶ loopSpace X x) =
      SSet.const (originalLoopPoint X x) := by
  let : Mono (originalLoopDoubleInclusion X x) := originalLoopDoubleInclusion_mono X x
  apply (cancel_mono (originalLoopDoubleInclusion X x)).mp
  rw [Category.assoc, ← SSet.pathSpace_map_eval₀, ← Category.assoc,
    originalBasedLoopSquarePath_projection, originalLoopDoubleInclusion_point_map]
  exact hb₀

/-- All three original constraints give the whole original based-path-of-loop universal map. -/
def originalBasedLoopDoublePathLift {A : SSet.{u}} (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) (g : A ⟶ pathSpace (pathSpace X))
    (h₀ : g ≫ (ihom (Δ[1] : SSet.{u})).map (SSet.eval₀ : pathSpace X ⟶ X) =
      SSet.const (originalPathPoint X x))
    (h₁ : g ≫ (ihom (Δ[1] : SSet.{u})).map (SSet.eval₁ : pathSpace X ⟶ X) =
      SSet.const (originalPathPoint X x))
    (hb₀ : g ≫ (SSet.eval₀ : pathSpace (pathSpace X) ⟶ pathSpace X) =
      SSet.const (originalPathPoint X x)) :
    A ⟶ basedPath (loopSpace X x) (originalLoopPoint X x) :=
  originalBasedPathUniversalLift (loopSpace X x) (originalLoopPoint X x)
    (originalBasedLoopSquarePath X x g h₀ h₁)
      (originalBasedLoopSquarePath_initial X x g h₀ h₁ hb₀)

/-- The whole original based-path-of-loop universal map retains its complete original interval
square. -/
@[reassoc]
theorem originalBasedLoopDoublePathLift_projection {A : SSet.{u}} (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) (g : A ⟶ pathSpace (pathSpace X))
    (h₀ : g ≫ (ihom (Δ[1] : SSet.{u})).map (SSet.eval₀ : pathSpace X ⟶ X) =
      SSet.const (originalPathPoint X x))
    (h₁ : g ≫ (ihom (Δ[1] : SSet.{u})).map (SSet.eval₁ : pathSpace X ⟶ X) =
      SSet.const (originalPathPoint X x))
    (hb₀ : g ≫ (SSet.eval₀ : pathSpace (pathSpace X) ⟶ pathSpace X) =
      SSet.const (originalPathPoint X x)) :
    originalBasedLoopDoublePathLift X x g h₀ h₁ hb₀ ≫
        originalBasedLoopDoublePathInclusion X x = g := by
  unfold originalBasedLoopDoublePathLift originalBasedLoopDoublePathInclusion
  rw [← Category.assoc, originalBasedPathUniversalLift_projection,
    originalBasedLoopSquarePath_projection]

private theorem originalLoopBasedSquarePath_endpoint {A : SSet.{u}} (X : SSet.{u})
    (x : X _⦋0⦌) (g : A ⟶ pathSpace (pathSpace X))
    (h₀ : g ≫ (ihom (Δ[1] : SSet.{u})).map (SSet.eval₀ : pathSpace X ⟶ X) =
      SSet.const (originalPathPoint X x))
    (v : ∀ Z : SSet.{u}, pathSpace Z ⟶ Z)
    (hv : ∀ {Y Z : SSet.{u}} (f : Y ⟶ Z),
      (ihom (Δ[1] : SSet.{u})).map f ≫ v Z = v Y ≫ f)
    (hb : g ≫ v (pathSpace X) = SSet.const (originalPathPoint X x)) :
    originalPathFiberLift (SSet.eval₀ : pathSpace X ⟶ X) x g h₀ ≫ v (basedPath X x) =
      SSet.const (basedPathPoint X x) := by
  let : Mono (SSet.basedPathIncl X x) := inferInstanceAs
    (Mono (Subcomplex.fiber (SSet.eval₀ : pathSpace X ⟶ X) x).ι)
  apply (cancel_mono (SSet.basedPathIncl X x)).mp
  let m : A ⟶ pathSpace (basedPath X x) :=
    originalPathFiberLift (SSet.eval₀ : pathSpace X ⟶ X) x g h₀
  have hm : m ≫ (ihom (Δ[1] : SSet.{u})).map (SSet.basedPathIncl X x) = g :=
    originalPathFiberLift_projection (SSet.eval₀ : pathSpace X ⟶ X) x g h₀
  exact (Category.assoc m (v (basedPath X x)) (SSet.basedPathIncl X x)).trans
    ((congrArg (fun a => m ≫ a) (hv (SSet.basedPathIncl X x)).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun a => a ≫ v (pathSpace X)) hm).trans
          (hb.trans (originalBasedPathPoint_constant_inclusion X x).symm))))

/-- All three original constraints give the whole original loop-of-based-path universal map. -/
def originalLoopBasedDoublePathLift {A : SSet.{u}} (X : SSet.{u}) (x : X _⦋0⦌)
    (g : A ⟶ pathSpace (pathSpace X))
    (h₀ : g ≫ (ihom (Δ[1] : SSet.{u})).map (SSet.eval₀ : pathSpace X ⟶ X) =
      SSet.const (originalPathPoint X x))
    (hb₀ : g ≫ (SSet.eval₀ : pathSpace (pathSpace X) ⟶ pathSpace X) =
      SSet.const (originalPathPoint X x))
    (hb₁ : g ≫ (SSet.eval₁ : pathSpace (pathSpace X) ⟶ pathSpace X) =
      SSet.const (originalPathPoint X x)) :
    A ⟶ loopSpace (basedPath X x) (basedPathPoint X x) :=
  originalLoopUniversalLift (basedPath X x) (basedPathPoint X x)
    (originalPathFiberLift (SSet.eval₀ : pathSpace X ⟶ X) x g h₀)
    (originalLoopBasedSquarePath_endpoint X x g h₀ (fun _ => SSet.eval₀)
      (fun f => SSet.pathSpace_map_eval₀ f) hb₀)
    (originalLoopBasedSquarePath_endpoint X x g h₀ (fun _ => SSet.eval₁)
      (fun f => SSet.pathSpace_map_eval₁ f) hb₁)

/-- The whole original loop-of-based-path universal map retains its complete original interval
square. -/
@[reassoc]
theorem originalLoopBasedDoublePathLift_projection {A : SSet.{u}} (X : SSet.{u})
    (x : X _⦋0⦌) (g : A ⟶ pathSpace (pathSpace X))
    (h₀ : g ≫ (ihom (Δ[1] : SSet.{u})).map (SSet.eval₀ : pathSpace X ⟶ X) =
      SSet.const (originalPathPoint X x))
    (hb₀ : g ≫ (SSet.eval₀ : pathSpace (pathSpace X) ⟶ pathSpace X) =
      SSet.const (originalPathPoint X x))
    (hb₁ : g ≫ (SSet.eval₁ : pathSpace (pathSpace X) ⟶ pathSpace X) =
      SSet.const (originalPathPoint X x)) :
    originalLoopBasedDoublePathLift X x g h₀ hb₀ hb₁ ≫
        originalLoopBasedDoublePathInclusion X x = g := by
  let m : A ⟶ pathSpace (basedPath X x) :=
    originalPathFiberLift (SSet.eval₀ : pathSpace X ⟶ X) x g h₀
  have hm₀ : m ≫ (SSet.eval₀ : pathSpace (basedPath X x) ⟶ basedPath X x) =
      SSet.const (basedPathPoint X x) :=
    originalLoopBasedSquarePath_endpoint X x g h₀ (fun _ => SSet.eval₀)
      (fun f => SSet.pathSpace_map_eval₀ f) hb₀
  have hm₁ : m ≫ (SSet.eval₁ : pathSpace (basedPath X x) ⟶ basedPath X x) =
      SSet.const (basedPathPoint X x) :=
    originalLoopBasedSquarePath_endpoint X x g h₀ (fun _ => SSet.eval₁)
      (fun f => SSet.pathSpace_map_eval₁ f) hb₁
  let q := originalLoopUniversalLift (basedPath X x) (basedPathPoint X x) m hm₀ hm₁
  have hq : originalLoopBasedDoublePathLift X x g h₀ hb₀ hb₁ = q := rfl
  have hFirst : q ≫ originalLoopDoubleInclusion (basedPath X x) (basedPathPoint X x) = m :=
    originalLoopUniversalLift_projection (basedPath X x) (basedPathPoint X x) m hm₀ hm₁
  have hSecond : m ≫ (ihom (Δ[1] : SSet.{u})).map (SSet.basedPathIncl X x) = g :=
    originalPathFiberLift_projection (SSet.eval₀ : pathSpace X ⟶ X) x g h₀
  exact (congrArg (fun a => a ≫ originalLoopBasedDoublePathInclusion X x) hq).trans
    ((Category.assoc q (originalLoopDoubleInclusion (basedPath X x) (basedPathPoint X x))
      ((ihom (Δ[1] : SSet.{u})).map (SSet.basedPathIncl X x))).symm.trans
        ((congrArg (fun a => a ≫ (ihom (Δ[1] : SSet.{u})).map
          (SSet.basedPathIncl X x)) hFirst).trans hSecond))

end SSet.OriginalBasedPathLoopUniversalGeometry
