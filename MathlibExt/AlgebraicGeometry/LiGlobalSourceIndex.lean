/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LiFamilySourceDescent
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward

/-!
# All actual affine tests and lifted Li source charts

The parent tests are every actual affine point of the family stack.
Additional objects remember every source chart, every Cech tuple, every
possible local etale lift, every etale source cover of a parent test, and
 every common refinement of an actual family arrow. None is selected as a
 global standard lift of the parent.

The native projection forgets only the source presentation. Morphisms and
coefficient rings are the actual affine-stack morphisms and section rings.
The local curve-chart ring is retained separately from that base ring:
Li's log cochains are modules over the base, with their genuine local
 tensor coefficients on the curve charts.

Source: Jun Li, arXiv:math/0110113v1, equations 1.15–1.25 and
Theorems 2.2–2.3. Native affine stack points and their cartesian module
 dictionary are imported from the existing public source interface.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LiGlobalSourceIndex

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open CoherentCurveLinearSeries RelativeProjectiveLineModels ExpandedTargetChainGeometry
open StandardRelativeExpansionModels RubberMapFamilies RubberModuliStackModels
open StackAffineModules LiFamilyDeformationMaps
open scoped Simplicial

variable {k : Type} [Field k]
  (O : ProjectiveLine (Spec (.of k)) (structureModule (Spec (.of k))))
  (P : RelativePair (k := k)) (D : OriginalRubberPair O P)
  (R : ProjectiveLine P.divisor.left (normalLineModule P)) (S : StandardSystem P R)
  {g n : ℕ} (a : Fin n → ℤ) (B : RubberModuliModel O P D R S (g := g) a)

abbrev SourcePoint := LiFamilyDeformationMaps.Point O P D R S a B

abbrev LiftType (C : SourcePoint O P D R S a B) (i : Fin C.chart.cover.count) :=
  LiLiftedSourceCechModels.Lift O P D R S C.chart.length a
    C.family.rubber.curve
    (FramedRubberFamilies.totalMap O P D R S C.chart.length a
      (RubberPOTSourceCharts.familyAt O P D R S a C.chart.framed C.spec C.chart.point))
    C.chart.cover C.chart.source C.chart.universal i

/-- Every source choice occurs as an object; a cover/lift is not demanded
at a parent at which no such global standard choice exists. -/
inductive LocalChoice where
  | chart (C : SourcePoint O P D R S a B)
  | member (C : SourcePoint O P D R S a B) (z : SimplexCategory)
      (t : Fin (z.len + 1) → Fin C.chart.cover.count)
  | lift (C : SourcePoint O P D R S a B) (i : Fin C.chart.cover.count)
      (L : LiftType O P D R S a B C i)
  | cover (p : AffinePoint B.stack)
      (V : LiFamilySourceDescent.SourceCover (O := O) (P := P) (D := D)
        (R := R) (S := S) (a := a) (B := B) p)
  | baseChange (C : SourcePoint O P D R S a B) (p : AffinePoint B.stack)
      (map : p ⟶ C.native)
  | baseChangeCover (C : SourcePoint O P D R S a B) (p q : AffinePoint B.stack)
      (toChart : q ⟶ C.native) (toParent : q ⟶ p)
      (etale : Etale toParent.hom.base.left)
      (covering : Function.Surjective toParent.hom.base.left)
  | refinement (C E : SourcePoint O P D R S a B) (f : Arrow C E)
      (V : LiFamilySourceDescent.RefinementSpan (O := O) (P := P) (D := D)
        (R := R) (S := S) (a := a) (B := B) f)

def localPoint : LocalChoice O P D R S a B → SourcePoint O P D R S a B
  | .chart C => C
  | .member C _ _ => C
  | .lift C _ _ => C
  | .cover _ V => V.point
  | .baseChange C _ _ => C
  | .baseChangeCover C _ _ _ _ _ _ => C
  | .refinement _ _ _ V => V.point

def localNative (i : LocalChoice O P D R S a B) : AffinePoint B.stack :=
  match i with
  | .baseChange _ p _ => p
  | .baseChangeCover _ _ q _ _ _ _ => q
  | i => (localPoint O P D R S a B i).native

inductive FullChoice where
  | parent (p : AffinePoint B.stack)
  | local (i : LocalChoice O P D R S a B)

def native : FullChoice O P D R S a B → AffinePoint B.stack
  | .parent p => p
  | .local i => localNative O P D R S a B i

/-- The full source test category carries the actual base morphisms,
including stabilizer arrows of the native family stack. -/
abbrev Index := InducedCategory (AffinePoint B.stack) (native O P D R S a B)

abbrev LiftIndex := InducedCategory (AffinePoint B.stack) (localNative O P D R S a B)

def projection : Index O P D R S a B ⥤ AffinePoint B.stack :=
  inducedFunctor (native O P D R S a B)

def parent : AffinePoint B.stack ⥤ Index O P D R S a B where
  obj p := .parent p
  map f := InducedCategory.homMk f

def includeLift : LiftIndex O P D R S a B ⥤ Index O P D R S a B where
  obj i := .local i
  map f := InducedCategory.homMk f.hom

def coefficientRings : (Index O P D R S a B)ᵒᵖ ⥤ RingCat.{0} :=
  (projection O P D R S a B).op ⋙ rings B.stack ⋙ forget₂ CommRingCat RingCat

abbrev LargeModules := PresheafOfModules.{2} (coefficientRings O P D R S a B)

abbrev LargeLiftModules := PresheafOfModules.{2}
  ((includeLift O P D R S a B).op ⋙ coefficientRings O P D R S a B)

/-- Restriction uses the native module-presheaf functor, so all base-ring
 actions and every actual source arrow remain part of the diagram. -/
def restrictToLifts : LargeModules O P D R S a B ⥤ LargeLiftModules O P D R S a B :=
  PresheafOfModules.pushforward₀ (includeLift O P D R S a B)
    (coefficientRings O P D R S a B)

def parentRestriction : LargeModules O P D R S a B ⥤
    PresheafOfModules.{2} (rings B.stack ⋙ forget₂ CommRingCat RingCat) :=
  PresheafOfModules.pushforward₀ (parent O P D R S a B)
    (coefficientRings O P D R S a B)

@[simp] theorem parent_projection :
    parent O P D R S a B ⋙ projection O P D R S a B = 𝟭 (AffinePoint B.stack) := rfl

/-- The actual curve-chart algebra; it is not silently identified with
 the affine base ring used in the global coefficient diagram. -/
abbrev memberSourceRing (C : SourcePoint O P D R S a B) (z : SimplexCategory)
    (t : Fin (z.len + 1) → Fin C.chart.cover.count) :=
  (LiFamilySourceDescent.localChart C z t).source

end MathlibExt.AlgebraicGeometry.LiGlobalSourceIndex
