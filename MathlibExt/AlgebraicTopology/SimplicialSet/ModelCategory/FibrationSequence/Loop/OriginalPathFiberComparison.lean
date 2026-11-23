/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.Loop.OriginalDoublePathEndpoints
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Fiber
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Original path-space and every original chosen strict fiber

The SAME original path right adjoint preserves the whole original fiber
pullback. Its original point simplex is terminal and its inverse point
comparison is the literal original constant-path map. The resulting full
Iso compares pathSpace of the original strict fiber to the original
strict fiber of the actual path map at the SAME constant-path point.
Both whole maps, both pullback legs, all actual chosen points and all
original commutative squares are retained.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial MonoidalClosed SSet.modelCategoryQuillen

namespace SSet.OriginalPathFiberComparisonGeometry

/-- The original chosen path point is the actual original constant-path image. -/
def originalPathPoint (X : SSet.{u}) (x : X _⦋0⦌) : pathSpace X _⦋0⦌ :=
  (SSet.constPath X).app _ x

/-- The entire original chosen-point function is its SAME original constant-path component. -/
theorem originalPathPoint_value (X : SSet.{u}) :
    originalPathPoint X = (SSet.constPath X).app (op ⦋0⦌) := rfl

/-- Every entire original map preserves the actual selected constant-path vertex. -/
theorem originalPathMapPoint {X Y : SSet.{u}} (f : X ⟶ Y)
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y) :
    ((ihom (Δ[1] : SSet.{u})).map f).app _ (originalPathPoint X x) =
      originalPathPoint Y y := by
  have e := ConcreteCategory.congr_hom
    (congr_app (SSet.constPath_naturality f) (op ⦋0⦌)) x
  exact e.symm.trans (congrArg ((SSet.constPath Y).app _) h)

/-- The SAME original point simplex remains terminal under the actual original path functor. -/
def originalPathPointIsTerminal : IsTerminal (pathSpace (Δ[0] : SSet.{u})) := by
  let : PreservesLimits (ihom (Δ[1] : SSet.{u})) :=
    (ihom.adjunction (Δ[1] : SSet.{u})).rightAdjoint_preservesLimits
  exact IsTerminal.isTerminalObj (ihom (Δ[1] : SSet.{u}))
    (Δ[0] : SSet.{u}) SSet.stdSimplex.isTerminalObj₀

/-- Both actual original point comparison maps are retained in the full point Iso. -/
def originalPathPointIso : pathSpace (Δ[0] : SSet.{u}) ≅ (Δ[0] : SSet.{u}) where
  hom := SSet.eval₀
  inv := SSet.constPath (Δ[0] : SSet.{u})
  hom_inv_id := originalPathPointIsTerminal.hom_ext _ _
  inv_hom_id := SSet.eval₀_constPath _

/-- The entire original forward point comparison is its SAME actual initial evaluation. -/
theorem originalPathPointIso_hom : originalPathPointIso.{u}.hom = SSet.eval₀ := rfl

/-- The entire original inverse point comparison is its SAME actual constant-path inclusion. -/
theorem originalPathPointIso_inv :
    originalPathPointIso.{u}.inv = SSet.constPath (Δ[0] : SSet.{u}) := rfl

/-- The SAME original terminal comparison also agrees with the entire final evaluation map. -/
theorem originalPathPointIso_hom_evalOne :
    originalPathPointIso.{u}.hom = SSet.eval₁ :=
  SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The full actual original point map is retained after applying the path functor. -/
theorem originalPathPointMap (X : SSet.{u}) (x : X _⦋0⦌) :
    (ihom (Δ[1] : SSet.{u})).map (SSet.const (X := Δ[0]) x) =
      originalPathPointIso.hom ≫ SSet.const (X := Δ[0]) (originalPathPoint X x) := by
  let e := originalPathPointIso.{u}
  let f := (ihom (Δ[1] : SSet.{u})).map (SSet.const (X := Δ[0]) x)
  have h : e.inv ≫ f = SSet.const (X := Δ[0]) (originalPathPoint X x) :=
    (SSet.constPath_naturality (SSet.const (X := Δ[0]) x)).symm.trans
      (SSet.const_comp x (SSet.constPath X))
  exact (Iso.hom_inv_id_assoc e f).symm.trans (congrArg (fun q => e.hom ≫ q) h)

/-- The entire original strict-fiber pullback is preserved by the actual original right adjoint. -/
theorem originalPathMappedFiber_isPullback {E B : SSet.{u}} (f : E ⟶ B)
    (b : B _⦋0⦌) :
    IsPullback
      ((ihom (Δ[1] : SSet.{u})).map (Subcomplex.fiber f b).ι)
      ((ihom (Δ[1] : SSet.{u})).map
        (SSet.stdSimplex.isTerminalObj₀.from (Subcomplex.fiber f b : SSet.{u})))
      ((ihom (Δ[1] : SSet.{u})).map f)
      ((ihom (Δ[1] : SSet.{u})).map (SSet.const (X := Δ[0]) b)) := by
  let : PreservesLimits (ihom (Δ[1] : SSet.{u})) :=
    (ihom.adjunction (Δ[1] : SSet.{u})).rightAdjoint_preservesLimits
  exact (Subcomplex.fiber_isPullback f b).map (ihom (Δ[1] : SSet.{u}))

/-- The full original path-fiber pullback retains its original total and point legs. -/
theorem originalPathFiber_isPullback {E B : SSet.{u}} (f : E ⟶ B) (b : B _⦋0⦌) :
    IsPullback
      ((ihom (Δ[1] : SSet.{u})).map (Subcomplex.fiber f b).ι)
      ((ihom (Δ[1] : SSet.{u})).map
        (SSet.stdSimplex.isTerminalObj₀.from (Subcomplex.fiber f b : SSet.{u})) ≫
          originalPathPointIso.hom)
      ((ihom (Δ[1] : SSet.{u})).map f)
      (SSet.const (X := Δ[0]) (originalPathPoint B b)) := by
  exact (originalPathMappedFiber_isPullback f b).of_iso (Iso.refl _) (Iso.refl _)
    originalPathPointIso (Iso.refl _) (by simp) (by simp) (by simp)
      ((Category.comp_id _).trans (originalPathPointMap B b))

/-- Both complete original fiber comparisons are obtained from the SAME original limiting cones. -/
def originalPathFiberIso {E B : SSet.{u}} (f : E ⟶ B) (b : B _⦋0⦌) :
    pathSpace (Subcomplex.fiber f b : SSet.{u}) ≅
      (Subcomplex.fiber ((ihom (Δ[1] : SSet.{u})).map f) (originalPathPoint B b) : SSet.{u}) :=
  (originalPathFiber_isPullback f b).isoIsPullback _ _
    (Subcomplex.fiber_isPullback ((ihom (Δ[1] : SSet.{u})).map f) (originalPathPoint B b))

/-- The entire original forward fiber comparison retains the actual original total projection. -/
@[reassoc]
theorem originalPathFiberIso_hom_fst {E B : SSet.{u}} (f : E ⟶ B) (b : B _⦋0⦌) :
    (originalPathFiberIso f b).hom ≫
        (Subcomplex.fiber ((ihom (Δ[1] : SSet.{u})).map f) (originalPathPoint B b)).ι =
      (ihom (Δ[1] : SSet.{u})).map (Subcomplex.fiber f b).ι :=
  (originalPathFiber_isPullback f b).isoIsPullback_hom_fst _ _ _

/-- The entire original forward fiber comparison retains the actual original point projection. -/
theorem originalPathFiberIso_hom_snd {E B : SSet.{u}} (f : E ⟶ B) (b : B _⦋0⦌) :
    (originalPathFiberIso f b).hom ≫
        SSet.stdSimplex.isTerminalObj₀.from
          (Subcomplex.fiber ((ihom (Δ[1] : SSet.{u})).map f) (originalPathPoint B b) : SSet.{u}) =
      (ihom (Δ[1] : SSet.{u})).map
        (SSet.stdSimplex.isTerminalObj₀.from (Subcomplex.fiber f b : SSet.{u})) ≫
          originalPathPointIso.hom :=
  (originalPathFiber_isPullback f b).isoIsPullback_hom_snd _ _ _

/-- The entire original inverse fiber comparison retains the actual original total projection. -/
@[reassoc]
theorem originalPathFiberIso_inv_fst {E B : SSet.{u}} (f : E ⟶ B) (b : B _⦋0⦌) :
    (originalPathFiberIso f b).inv ≫
        (ihom (Δ[1] : SSet.{u})).map (Subcomplex.fiber f b).ι =
      (Subcomplex.fiber ((ihom (Δ[1] : SSet.{u})).map f) (originalPathPoint B b)).ι :=
  (originalPathFiber_isPullback f b).isoIsPullback_inv_fst _ _ _

/-- The entire original inverse fiber comparison retains the actual original point projection. -/
theorem originalPathFiberIso_inv_snd {E B : SSet.{u}} (f : E ⟶ B) (b : B _⦋0⦌) :
    (originalPathFiberIso f b).inv ≫
        (ihom (Δ[1] : SSet.{u})).map
          (SSet.stdSimplex.isTerminalObj₀.from (Subcomplex.fiber f b : SSet.{u})) ≫
            originalPathPointIso.hom =
      SSet.stdSimplex.isTerminalObj₀.from
        (Subcomplex.fiber ((ihom (Δ[1] : SSet.{u})).map f) (originalPathPoint B b) : SSet.{u}) := by
  rw [← Category.assoc]
  exact (originalPathFiber_isPullback f b).isoIsPullback_inv_snd _ _ _

/-- The whole original forward comparison retains the SAME original constant-path fiber map. -/
theorem originalPathFiberIso_hom_constPath {E B : SSet.{u}} (f : E ⟶ B) (b : B _⦋0⦌) :
    SSet.constPath (Subcomplex.fiber f b : SSet.{u}) ≫ (originalPathFiberIso f b).hom =
      Subcomplex.mapFiber (SSet.constPath E) (SSet.constPath B)
        (SSet.constPath_naturality f).symm (y := b) (y' := originalPathPoint B b)
          (congrFun (originalPathPoint_value B) b).symm := by
  apply (cancel_mono
    (Subcomplex.fiber ((ihom (Δ[1] : SSet.{u})).map f) (originalPathPoint B b)).ι).mp
  rw [Category.assoc, originalPathFiberIso_hom_fst, Subcomplex.mapFiber_ι]
  exact (SSet.constPath_naturality (Subcomplex.fiber f b).ι).symm

/-- The whole original inverse comparison retains the SAME original constant-path fiber map. -/
theorem originalPathFiberIso_inv_constPath {E B : SSet.{u}} (f : E ⟶ B) (b : B _⦋0⦌) :
    Subcomplex.mapFiber (SSet.constPath E) (SSet.constPath B)
        (SSet.constPath_naturality f).symm (y := b) (y' := originalPathPoint B b)
          (congrFun (originalPathPoint_value B) b).symm ≫
          (originalPathFiberIso f b).inv = SSet.constPath (Subcomplex.fiber f b : SSet.{u}) := by
  rw [← originalPathFiberIso_hom_constPath, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Every actual original chosen fiber vertex is retained by the entire original forward map. -/
theorem originalPathFiberIso_hom_point {E B : SSet.{u}} (f : E ⟶ B) (b : B _⦋0⦌)
    (e : E _⦋0⦌) (he : f.app _ e = b) :
    (originalPathFiberIso f b).hom.app _
        (originalPathPoint (Subcomplex.fiber f b : SSet.{u}) (Subcomplex.fiber.basePoint e he)) =
      Subcomplex.fiber.basePoint (originalPathPoint E e) (originalPathMapPoint f he) := by
  have h := ConcreteCategory.congr_hom
    (congr_app (originalPathFiberIso_hom_constPath f b) (op ⦋0⦌))
      (Subcomplex.fiber.basePoint e he)
  exact h.trans (Subcomplex.mapFiber_app_basePoint (SSet.constPath E) (SSet.constPath B)
    (SSet.constPath_naturality f).symm (y := b) (y' := originalPathPoint B b)
      (congrFun (originalPathPoint_value B) b).symm e he)

/-- Every actual original chosen fiber vertex is retained by the entire original inverse map. -/
theorem originalPathFiberIso_inv_point {E B : SSet.{u}} (f : E ⟶ B) (b : B _⦋0⦌)
    (e : E _⦋0⦌) (he : f.app _ e = b) :
    (originalPathFiberIso f b).inv.app _
        (Subcomplex.fiber.basePoint (originalPathPoint E e) (originalPathMapPoint f he)) =
      originalPathPoint (Subcomplex.fiber f b : SSet.{u}) (Subcomplex.fiber.basePoint e he) := by
  rw [← originalPathFiberIso_hom_point f b e he]
  exact ConcreteCategory.congr_hom
    (congr_app (originalPathFiberIso f b).hom_inv_id (op ⦋0⦌)) _

/-- Every original full square retains its complete original mapped path square. -/
theorem originalPathFiberSquare {E B E' B' : SSet.{u}} {f : E ⟶ B} {f' : E' ⟶ B'}
    (g : E ⟶ E') (h : B ⟶ B') (hc : g ≫ f' = f ≫ h) :
    (ihom (Δ[1] : SSet.{u})).map g ≫ (ihom (Δ[1] : SSet.{u})).map f' =
      (ihom (Δ[1] : SSet.{u})).map f ≫ (ihom (Δ[1] : SSet.{u})).map h := by
  rw [← Functor.map_comp, hc, Functor.map_comp]

/-- Every original entire chosen square preserves both full forward original fiber comparisons. -/
theorem originalPathFiberIso_hom_naturality {E B E' B' : SSet.{u}} {f : E ⟶ B} {f' : E' ⟶ B'}
    (g : E ⟶ E') (h : B ⟶ B') (hc : g ≫ f' = f ≫ h)
    {b : B _⦋0⦌} {b' : B' _⦋0⦌} (hb : h.app _ b = b') :
    (ihom (Δ[1] : SSet.{u})).map (Subcomplex.mapFiber g h hc hb) ≫
        (originalPathFiberIso f' b').hom =
      (originalPathFiberIso f b).hom ≫ Subcomplex.mapFiber
        ((ihom (Δ[1] : SSet.{u})).map g) ((ihom (Δ[1] : SSet.{u})).map h)
        (originalPathFiberSquare g h hc) (originalPathMapPoint h hb) := by
  apply (cancel_mono
    (Subcomplex.fiber ((ihom (Δ[1] : SSet.{u})).map f') (originalPathPoint B' b')).ι).mp
  rw [Category.assoc, originalPathFiberIso_hom_fst, ← Functor.map_comp,
    Subcomplex.mapFiber_ι, Functor.map_comp, Category.assoc, Subcomplex.mapFiber_ι,
    ← Category.assoc, originalPathFiberIso_hom_fst]

/-- Every original entire chosen square preserves both full inverse original fiber comparisons. -/
theorem originalPathFiberIso_inv_naturality {E B E' B' : SSet.{u}} {f : E ⟶ B} {f' : E' ⟶ B'}
    (g : E ⟶ E') (h : B ⟶ B') (hc : g ≫ f' = f ≫ h)
    {b : B _⦋0⦌} {b' : B' _⦋0⦌} (hb : h.app _ b = b') :
    (originalPathFiberIso f b).inv ≫
        (ihom (Δ[1] : SSet.{u})).map (Subcomplex.mapFiber g h hc hb) =
      Subcomplex.mapFiber
        ((ihom (Δ[1] : SSet.{u})).map g) ((ihom (Δ[1] : SSet.{u})).map h)
        (originalPathFiberSquare g h hc) (originalPathMapPoint h hb) ≫
          (originalPathFiberIso f' b').inv := by
  apply (cancel_epi (originalPathFiberIso f b).hom).mp
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp,
    ← Category.assoc, ← originalPathFiberIso_hom_naturality g h hc hb,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SSet.OriginalPathFiberComparisonGeometry
