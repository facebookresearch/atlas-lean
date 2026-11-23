/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.CWComplex
public import MathlibExt.AlgebraicTopology.SimplicialSet.PiZeroConnectedRealization
public import MathlibExt.AlgebraicTopology.PlusConstruction.LoopCellHomologyTwoSplit
public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeCoverCertificates
public import Mathlib.CategoryTheory.Comma.Arrow
import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.PathGroupoidCover
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidPiOne
import MathlibExt.AlgebraicTopology.SimplicialSet.PiZeroToZerothHomotopySurjective
import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationFundamentalGroupoidEquivalence
public import MathlibExt.Topology.Homotopy.TopCat.HurewiczOne
public import MathlibExt.Topology.Homotopy.TopCat.HurewiczTwo
public import MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.Subcomplex
public import MathlibExt.Topology.Category.TopPair.ClosedBall
public import MathlibExt.AlgebraicTopology.PlusConstruction.CellFundamentalGroupQuotient
public import MathlibExt.AlgebraicTopology.PlusConstruction.LoopCellRelativeHomology
public import MathlibExt.AlgebraicTopology.PlusConstruction.LoopCellPerfectHomology
public import MathlibExt.AlgebraicTopology.SingularHomology.IntegerExactness
import MathlibExt.AlgebraicTopology.EilenbergSteenrod.PairSequenceExact
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Category.TopCat.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.Clopen
public import Mathlib.GroupTheory.IsPerfect
import Mathlib.Algebra.Category.Grp.Zero

/-!
# Sphere maps for the original perfect-subgroup cell family

Weibel, *The K-book*, Exercise IV.1.4 (printed p. 273 / PDF p. 281),
asks for actual maps from the two-sphere representing the added cell
classes. This module constructs spherical absolute preimages of every
ORIGINAL relative two-cell generator, with the fixed original relative
three-disk boundary coordinate and all integral coefficients.

The project-derived proof pulls the existing native cover of the singular
two-cell target back along the original inclusion. Its actual fundamental
group is the original perfect subgroup, and its old-cover first homology
is zero. The SAME characteristic disk pair lifts strictly; the actual
upstairs pair sequence supplies absolute preimages. The existing generic
one-connected classical sphere map then pushes down to the original
indexed generator. No cover, basis, model, inverse, sphere, calibration or
acyclicity witness is supplied as input.

The matched disk arrow, native lifts and realized pair maps are public
computed data for later cell constructions. This proof does not assert
that an arbitrary earlier noncanonical homology section is spherical or
that the realized singular-cover composite is a topological covering map.
Three-cell/local-coefficient correction, independent plus and Q=+ remain
separate conclusions.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Topology Topology.CWComplex
open SSet.KanComplex
open scoped Simplicial SSet.modelCategoryQuillen

universe u

namespace OriginalSphericalNativePullback

private abbrev targetPoint {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) : Y _⦋0⦌ :=
  f.app (Opposite.op ⦋0⦌) x

private abbrev cover {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) : SSet.{u} :=
  nativeCover Y (targetPoint f x)

private abbrev underNerve {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) : SSet.{u} :=
  CategoryTheory.nerve (CategoryTheory.Under (SSet.FundamentalGroupoid.mk (targetPoint f x)))

private def space {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) : SSet.{u} :=
  pullback f (nativeCoverProjection Y (targetPoint f x))

private def sourceProjection {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) :
    space f x ⟶ X :=
  pullback.fst f (nativeCoverProjection Y (targetPoint f x))

private def coverProjection {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) :
    space f x ⟶ cover f x :=
  pullback.snd f (nativeCoverProjection Y (targetPoint f x))

private def underProjection {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) :
    space f x ⟶ underNerve f x :=
  coverProjection f x ≫ nativeCoverUnderProjection Y (targetPoint f x)

private theorem square {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) :
    sourceProjection f x ≫ f =
      coverProjection f x ≫ nativeCoverProjection Y (targetPoint f x) :=
  pullback.condition

private def pointMap {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) :
    (Δ[0] : SSet.{u}) ⟶ space f x :=
  pullback.lift (SSet.const x)
    (SSet.const (nativeCoverIdentityPoint Y (targetPoint f x))) (by
      simp only [SSet.const_comp, nativeCoverProjection_identityPoint])

private def point {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) : (space f x) _⦋0⦌ :=
  SSet.yonedaEquiv (pointMap f x)

private theorem point_source {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) :
    (sourceProjection f x).app _ (point f x) = x := by
  have h : pointMap f x ≫ sourceProjection f x = SSet.const x := by
    dsimp only [pointMap, sourceProjection, space]
    exact pullback.lift_fst _ _ _
  rw [point, ← SSet.yonedaEquiv_comp, h, SSet.yonedaEquiv_const]

private theorem point_cover {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) :
    (coverProjection f x).app _ (point f x) =
      nativeCoverIdentityPoint Y (targetPoint f x) := by
  have h : pointMap f x ≫ coverProjection f x =
      SSet.const (nativeCoverIdentityPoint Y (targetPoint f x)) := by
    dsimp only [pointMap, coverProjection, space]
    exact pullback.lift_snd _ _ _
  rw [point, ← SSet.yonedaEquiv_comp, h, SSet.yonedaEquiv_const]

private theorem hom_ext {X Y T : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌)
    {a b : T ⟶ space f x}
    (hq : a ≫ sourceProjection f x = b ≫ sourceProjection f x)
    (hu : a ≫ underProjection f x = b ≫ underProjection f x) : a = b := by
  have hCover : a ≫ coverProjection f x = b ≫ coverProjection f x := by
    apply nativeCover_hom_ext (X := Y) (x := targetPoint f x)
    · calc
        (a ≫ coverProjection f x) ≫ nativeCoverProjection Y (targetPoint f x) =
          a ≫ (sourceProjection f x ≫ f) := by rw [Category.assoc, ← square]
        _ = (a ≫ sourceProjection f x) ≫ f := (Category.assoc _ _ _).symm
        _ = (b ≫ sourceProjection f x) ≫ f := congrArg (fun t => t ≫ f) hq
        _ = b ≫ (sourceProjection f x ≫ f) := Category.assoc _ _ _
        _ = (b ≫ coverProjection f x) ≫ nativeCoverProjection Y (targetPoint f x) := by
          rw [square, Category.assoc]
    · have hUnder : a ≫ (coverProjection f x ≫
          nativeCoverUnderProjection Y (targetPoint f x)) =
        b ≫ (coverProjection f x ≫ nativeCoverUnderProjection Y (targetPoint f x)) := hu
      exact (Category.assoc a (coverProjection f x)
        (nativeCoverUnderProjection Y (targetPoint f x))).trans
          (hUnder.trans (Category.assoc b (coverProjection f x)
            (nativeCoverUnderProjection Y (targetPoint f x))).symm)
  exact pullback.hom_ext hq hCover

private def flatLift {X Y T : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌)
    (a : T ⟶ X) (b : T ⟶ underNerve f x)
    (h : (a ≫ f) ≫ nativeCoverUnit Y =
      b ≫ nativeCoverNerveProjection Y (targetPoint f x)) : T ⟶ space f x :=
  let L : T ⟶ cover f x := pullback.lift (a ≫ f) b h
  pullback.lift a L (by
    dsimp only [L, cover, nativeCoverProjection]
    exact (pullback.lift_fst _ _ _).symm)

private theorem flatLift_source {X Y T : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌)
    (a : T ⟶ X) (b : T ⟶ underNerve f x)
    (h : (a ≫ f) ≫ nativeCoverUnit Y =
      b ≫ nativeCoverNerveProjection Y (targetPoint f x)) :
    flatLift f x a b h ≫ sourceProjection f x = a := by
  dsimp only [flatLift, sourceProjection, space]
  exact pullback.lift_fst _ _ _

private theorem flatLift_under {X Y T : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌)
    (a : T ⟶ X) (b : T ⟶ underNerve f x)
    (h : (a ≫ f) ≫ nativeCoverUnit Y =
      b ≫ nativeCoverNerveProjection Y (targetPoint f x)) :
    flatLift f x a b h ≫ underProjection f x = b := by
  let L : T ⟶ cover f x := pullback.lift (a ≫ f) b h
  have hOuter : flatLift f x a b h ≫ coverProjection f x = L := by
    exact pullback.lift_snd a L _
  have hInner : L ≫ nativeCoverUnderProjection Y (targetPoint f x) = b := by
    exact pullback.lift_snd (a ≫ f) b h
  calc
    flatLift f x a b h ≫ underProjection f x =
      (flatLift f x a b h ≫ coverProjection f x) ≫
        nativeCoverUnderProjection Y (targetPoint f x) :=
      (Category.assoc _ _ _).symm
    _ = L ≫ nativeCoverUnderProjection Y (targetPoint f x) :=
      congrArg (fun t : T ⟶ cover f x =>
        t ≫ nativeCoverUnderProjection Y (targetPoint f x)) hOuter
    _ = b := hInner

private theorem kan {X Y : SSet.{u}} [SSet.KanComplex X]
    (f : X ⟶ Y) (x : X _⦋0⦌) : SSet.KanComplex (space f x) := by
  have : HomotopicalAlgebra.Fibration (nativeCoverProjection Y (targetPoint f x)) :=
    nativeCoverProjection_fibration Y (targetPoint f x)
  dsimp only [space]
  infer_instance

end OriginalSphericalNativePullback

namespace OriginalSphericalNativePullback

attribute [local instance] kan nativeCover_kanComplex

private def underPoint {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) :
    (underNerve f x) _⦋0⦌ :=
  CategoryTheory.nerveEquiv.symm
    (CategoryTheory.Under.mk (𝟙 (SSet.FundamentalGroupoid.mk (targetPoint f x))))

private theorem constPoint_source {X Y T : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) :
    (SSet.const (point f x) : T ⟶ space f x) ≫ sourceProjection f x = SSet.const x := by
  rw [SSet.const_comp, point_source]

private theorem constPoint_cover {X Y T : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) :
    (SSet.const (point f x) : T ⟶ space f x) ≫ coverProjection f x =
      SSet.const (nativeCoverIdentityPoint Y (targetPoint f x)) := by
  rw [SSet.const_comp, point_cover]

private theorem constPoint_under {X Y T : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) :
    (SSet.const (point f x) : T ⟶ space f x) ≫ underProjection f x =
      SSet.const (underPoint f x) := by
  rw [underProjection, ← Category.assoc, constPoint_cover, SSet.const_comp,
    nativeCoverUnderProjection_identityPoint]
  rfl

private theorem constUnder_projection {X Y T : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) :
    (SSet.const (underPoint f x) : T ⟶ underNerve f x) ≫
      nativeCoverNerveProjection Y (targetPoint f x) =
      SSet.const (CategoryTheory.nerveEquiv.symm
        (SSet.FundamentalGroupoid.mk (targetPoint f x))) := by
  have hVertex : (nativeCoverNerveProjection Y (targetPoint f x)).app
      (Opposite.op ⦋0⦌) (underPoint f x) =
        CategoryTheory.nerveEquiv.symm
          (SSet.FundamentalGroupoid.mk (targetPoint f x)) := by
    exact CategoryTheory.nerveMap_app_mk₀
      (CategoryTheory.Under.forget (SSet.FundamentalGroupoid.mk (targetPoint f x)))
      (CategoryTheory.Under.mk (𝟙 (SSet.FundamentalGroupoid.mk (targetPoint f x))))
  exact (SSet.const_comp (underPoint f x)
    (nativeCoverNerveProjection Y (targetPoint f x))).trans
      (congrArg (SSet.const (X := T)) hVertex)

private theorem pointedLoop_under_const
    {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌)
    (τ : (space f x).PtSimplex 1 (point f x)) :
    (SSet.RelativeMorphism.map τ) ≫ underProjection f x = SSet.const (underPoint f x) := by
  let τCover := SSet.PtSimplex.map (coverProjection f x) (point_cover f x) τ
  have hMap : SSet.RelativeMorphism.map τCover =
      SSet.RelativeMorphism.map τ ≫ coverProjection f x := rfl
  have hConst : SSet.RelativeMorphism.map τCover ≫
      nativeCoverUnderProjection Y (targetPoint f x) =
        SSet.const (underPoint f x) :=
    nativeCoverUnderProjection_pointedOne_eq_const τCover
  exact (Category.assoc (SSet.RelativeMorphism.map τ) (coverProjection f x)
    (nativeCoverUnderProjection Y (targetPoint f x))).symm.trans
      ((congrArg (fun a : (Δ[1] : SSet.{u}) ⟶ cover f x =>
        a ≫ nativeCoverUnderProjection Y (targetPoint f x)) hMap.symm).trans hConst)

private def relationMap
    {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌)
    {σ : X.PtSimplex 1 x}
    (R : σ.RelStruct₀ (SSet.RelativeMorphism.const : X.PtSimplex 1 x)) :
    (SSet.PtSimplex.map f rfl σ).RelStruct₀
      (SSet.RelativeMorphism.const : Y.PtSimplex 1 (targetPoint f x)) where
  map := R.map ≫ f
  δ_castSucc_map := by
    change SSet.stdSimplex.δ (0 : Fin 3) ≫ (R.map ≫ f) = (SSet.RelativeMorphism.map σ) ≫ f
    have hFace : SSet.stdSimplex.δ (0 : Fin 3) ≫ R.map =
        SSet.RelativeMorphism.map σ := R.δ_castSucc_map
    exact (Category.assoc (SSet.stdSimplex.δ (0 : Fin 3)) R.map f).symm.trans
      (congrArg (fun t : (Δ[1] : SSet.{u}) ⟶ X => t ≫ f) hFace)
  δ_succ_map := by
    change SSet.stdSimplex.δ (1 : Fin 3) ≫ (R.map ≫ f) = SSet.const (targetPoint f x)
    have hFace : SSet.stdSimplex.δ (1 : Fin 3) ≫ R.map =
        SSet.const x := by
      exact R.δ_succ_map
    exact (Category.assoc (SSet.stdSimplex.δ (1 : Fin 3)) R.map f).symm.trans
      ((congrArg (fun t : (Δ[1] : SSet.{u}) ⟶ X => t ≫ f) hFace).trans
        (SSet.const_comp x f))
  δ_map_of_lt j hj := by
    have h : j.val < 0 := by
      have hIndex : ((Fin.castSucc (0 : Fin 2) : Fin 3).val) = 0 := rfl
      exact hIndex ▸ hj
    exact (Nat.not_lt_zero _ h).elim
  δ_map_of_gt j hj := by
    rw [← Category.assoc, R.δ_map_of_gt j hj, SSet.const_comp]

private def loopLiftOfTargetNull
    {X Y : SSet.{u}} [SSet.KanComplex Y] (f : X ⟶ Y) (x : X _⦋0⦌)
    (σ : X.PtSimplex 1 x)
    (h : π.mk (SSet.PtSimplex.map f rfl σ) = 1) :
    (space f x).PtSimplex 1 (point f x) := by
  let R := Classical.choice ((π.mk_eq_one_iff (SSet.PtSimplex.map f rfl σ)).mp h)
  let B : SSet.{u} := CategoryTheory.nerve (SSet.FundamentalGroupoid Y)
  let v : B _⦋0⦌ := CategoryTheory.nerveEquiv.symm
    (SSet.FundamentalGroupoid.mk (targetPoint f x))
  have hR : R.map ≫ nativeCoverUnit Y =
      (SSet.const v : (Δ[2] : SSet.{u}) ⟶ B) :=
    nativeCoverUnit_relStructOneMap_eq_const R
  have hFace : SSet.stdSimplex.δ (0 : Fin 3) ≫ R.map =
      SSet.RelativeMorphism.map σ ≫ f := by
    have hRaw : SSet.stdSimplex.δ (0 : Fin 3) ≫ R.map =
        SSet.RelativeMorphism.map (SSet.PtSimplex.map f rfl σ) :=
      R.δ_castSucc_map
    exact hRaw.trans (show SSet.RelativeMorphism.map (SSet.PtSimplex.map f rfl σ) =
      SSet.RelativeMorphism.map σ ≫ f from rfl)
  have h0 : ((SSet.RelativeMorphism.map σ) ≫ f) ≫ nativeCoverUnit Y =
      SSet.const (CategoryTheory.nerveEquiv.symm
        (SSet.FundamentalGroupoid.mk (targetPoint f x))) := by
    calc
      ((SSet.RelativeMorphism.map σ) ≫ f) ≫ nativeCoverUnit Y =
        (SSet.stdSimplex.δ (0 : Fin 3) ≫ R.map) ≫ nativeCoverUnit Y :=
          congrArg (fun t : (Δ[1] : SSet.{u}) ⟶ Y => t ≫ nativeCoverUnit Y) hFace.symm
      _ = SSet.stdSimplex.δ (0 : Fin 3) ≫ (R.map ≫ nativeCoverUnit Y) :=
        Category.assoc _ _ _
      _ = SSet.stdSimplex.δ (0 : Fin 3) ≫ (SSet.const v : (Δ[2] : SSet.{u}) ⟶ B) :=
        congrArg (fun t : (Δ[2] : SSet.{u}) ⟶ B => SSet.stdSimplex.δ (0 : Fin 3) ≫ t) hR
      _ = (SSet.const v : (Δ[1] : SSet.{u}) ⟶ B) :=
        SSet.comp_const (SSet.stdSimplex.δ (0 : Fin 3)) v
  have hL : ((SSet.RelativeMorphism.map σ) ≫ f) ≫ nativeCoverUnit Y =
      (SSet.const (underPoint f x) : (Δ[1] : SSet.{u}) ⟶ underNerve f x) ≫
        nativeCoverNerveProjection Y (targetPoint f x) :=
    h0.trans (constUnder_projection f x).symm
  let L := flatLift f x (SSet.RelativeMorphism.map σ) (SSet.const (underPoint f x)) hL
  refine { map := L, comm := ?_ }
  change (SSet.boundary.{u} 1).ι ≫ L = SSet.const (point f x)
  apply hom_ext f x
  · rw [Category.assoc, flatLift_source]
    exact σ.comm.trans (constPoint_source f x).symm
  · rw [Category.assoc, flatLift_under, SSet.comp_const, constPoint_under]

private theorem loopLiftOfTargetNull_projection
    {X Y : SSet.{u}} [SSet.KanComplex Y] (f : X ⟶ Y) (x : X _⦋0⦌)
    (σ : X.PtSimplex 1 x) (h : π.mk (SSet.PtSimplex.map f rfl σ) = 1) :
    SSet.PtSimplex.map (sourceProjection f x) (point_source f x)
      (loopLiftOfTargetNull f x σ h) = σ := by
  apply SSet.RelativeMorphism.ext
  dsimp only [loopLiftOfTargetNull, SSet.PtSimplex.map]
  exact flatLift_source _ _ _ _ _

private def liftedNullRelation
    {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌)
    (τ : (space f x).PtSimplex 1 (point f x))
    (R : (SSet.PtSimplex.map (sourceProjection f x) (point_source f x) τ).RelStruct₀
      (SSet.RelativeMorphism.const : X.PtSimplex 1 x)) :
    τ.RelStruct₀ (SSet.RelativeMorphism.const : (space f x).PtSimplex 1 (point f x)) := by
  let RY := relationMap f x R
  have hY := nativeCoverUnit_relStructOneMap_eq_const RY
  have hL : (R.map ≫ f) ≫ nativeCoverUnit Y =
      (SSet.const (underPoint f x) : (Δ[2] : SSet.{u}) ⟶ underNerve f x) ≫
        nativeCoverNerveProjection Y (targetPoint f x) :=
    hY.trans (constUnder_projection f x).symm
  let L := flatLift f x R.map (SSet.const (underPoint f x)) hL
  refine
    { map := L
      δ_castSucc_map := ?_
      δ_succ_map := ?_
      δ_map_of_lt := ?_
      δ_map_of_gt := ?_ }
  · apply hom_ext f x
    · rw [Category.assoc, flatLift_source, R.δ_castSucc_map]
      rfl
    · rw [Category.assoc, flatLift_under, SSet.comp_const]
      exact (pointedLoop_under_const f x τ).symm
  · apply hom_ext f x
    · rw [Category.assoc, flatLift_source, R.δ_succ_map]
      exact (constPoint_source f x).symm
    · rw [Category.assoc, flatLift_under, SSet.comp_const]
      exact (constPoint_under f x).symm
  · intro j hj
    have h : j.val < 0 := by
      have hIndex : ((Fin.castSucc (0 : Fin 2) : Fin 3).val) = 0 := rfl
      exact hIndex ▸ hj
    exact (Nat.not_lt_zero _ h).elim
  · intro j hj
    apply hom_ext f x
    · rw [Category.assoc, flatLift_source, R.δ_map_of_gt j hj]
      exact (constPoint_source f x).symm
    · rw [Category.assoc, flatLift_under, SSet.comp_const]
      exact (constPoint_under f x).symm

/-- The native constant class is the unit of the existing canonical group,
proved using its constant-simplex multiplication law. -/
private theorem piOne_nativeUnit_eq_groupUnit
    (K : SSet.{u}) [SSet.KanComplex K] (z : K _⦋0⦌) :
    (1 : π 1 K z) = (inferInstance : Group (π 1 K z)).one := by
  let G : Group (π 1 K z) := inferInstance
  let c : K.PtSimplex 1 z := SSet.RelativeMorphism.const
  have hMul : (π.mk c : π 1 K z) * π.mk c = π.mk c :=
    (SSet.PtSimplex.MulStruct.oneMul c (Fin.last 0)).mul_eq
  have hRight : (π.mk c : π 1 K z) * G.one = π.mk c :=
    @mul_one (π 1 K z) G.toMulOneClass (π.mk c)
  have hUnit : (π.mk c : π 1 K z) = G.one :=
    mul_left_cancel (hMul.trans hRight.symm)
  exact (show (1 : π 1 K z) = π.mk c from rfl).trans hUnit

private def piOneProjection
    {X Y : SSet.{u}} [SSet.KanComplex X] (f : X ⟶ Y) (x : X _⦋0⦌) :
    π 1 (space f x) (point f x) →* π 1 X x :=
  MonoidHom.mk' (π.map (sourceProjection f x) (point_source f x) 1)
    (π.map_mul (sourceProjection f x) (point_source f x) 0)

private theorem piOneProjection_eq_one_implies
    {X Y : SSet.{u}} [SSet.KanComplex X] (f : X ⟶ Y) (x : X _⦋0⦌)
    (a : π 1 (space f x) (point f x)) (h : piOneProjection f x a = 1) : a = 1 := by
  obtain ⟨τ, rfl⟩ := π.mk_surjective a
  change π.map (sourceProjection f x) (point_source f x) 1 (π.mk τ) = 1 at h
  rw [π.map_mk] at h
  obtain ⟨R⟩ := (π.mk_eq_one_iff _).mp h
  exact (π.mk_eq_one_iff τ).mpr ⟨liftedNullRelation f x τ R⟩

private theorem piOneProjection_injective
    {X Y : SSet.{u}} [SSet.KanComplex X] (f : X ⟶ Y) (x : X _⦋0⦌) :
    Function.Injective (piOneProjection f x) := by
  intro a b h
  let q : π 1 (space f x) (point f x) →* π 1 X x := piOneProjection f x
  have hMap : q (a * b⁻¹) = (inferInstance : Group (π 1 X x)).one := by
    rw [q.map_mul, q.map_inv, h, mul_inv_cancel]
    rfl
  have hNative : q (a * b⁻¹) = (1 : π 1 X x) :=
    hMap.trans (piOne_nativeUnit_eq_groupUnit X x).symm
  have hDifference : a * b⁻¹ = (1 : π 1 (space f x) (point f x)) :=
    piOneProjection_eq_one_implies f x (a * b⁻¹) hNative
  exact mul_inv_eq_one.mp
    (hDifference.trans (piOne_nativeUnit_eq_groupUnit (space f x) (point f x)))

end OriginalSphericalNativePullback

namespace OriginalSphericalNativePullback

attribute [local instance] kan nativeCover_kanComplex

private def piOneBaseMap {X Y : SSet.{u}} [SSet.KanComplex X] [SSet.KanComplex Y]
    (f : X ⟶ Y) (x : X _⦋0⦌) : π 1 X x →* π 1 Y (targetPoint f x) :=
  MonoidHom.mk' (π.map f rfl 1) (π.map_mul f rfl 0)

private theorem piOneProjection_mk
    {X Y : SSet.{u}} [SSet.KanComplex X] (f : X ⟶ Y) (x : X _⦋0⦌)
    (τ : (space f x).PtSimplex 1 (point f x)) :
    piOneProjection f x (π.mk τ) =
      π.mk (SSet.PtSimplex.map (sourceProjection f x) (point_source f x) τ) := by
  change π.map (sourceProjection f x) (point_source f x) 1 (π.mk τ) = _
  rw [π.map_mk]

private theorem piOneProjection_mk_in_kernel
    {X Y : SSet.{u}} [SSet.KanComplex X] [SSet.KanComplex Y]
    (f : X ⟶ Y) (x : X _⦋0⦌)
    (τ : (space f x).PtSimplex 1 (point f x)) :
    piOneBaseMap f x (piOneProjection f x (π.mk τ)) = 1 := by
  let p := nativeCoverProjection Y (targetPoint f x)
  let τY := SSet.PtSimplex.map (coverProjection f x) (point_cover f x) τ
  have hPt :
      SSet.PtSimplex.map f rfl
          (SSet.PtSimplex.map (sourceProjection f x) (point_source f x) τ) =
        SSet.PtSimplex.map p (nativeCoverProjection_identityPoint Y (targetPoint f x)) τY := by
    apply SSet.RelativeMorphism.ext
    change ((SSet.RelativeMorphism.map τ) ≫ sourceProjection f x) ≫ f =
      ((SSet.RelativeMorphism.map τ) ≫ coverProjection f x) ≫ p
    rw [Category.assoc, square, Category.assoc]
  rw [piOneProjection_mk]
  change π.map f rfl 1
    (π.mk (SSet.PtSimplex.map (sourceProjection f x) (point_source f x) τ)) = 1
  rw [π.map_mk, hPt]
  exact (nativeCoverProjection_pointedOne_class_eq_const τY).trans (by rfl)

private theorem piOneProjection_in_kernel
    {X Y : SSet.{u}} [SSet.KanComplex X] [SSet.KanComplex Y]
    (f : X ⟶ Y) (x : X _⦋0⦌) (a : π 1 (space f x) (point f x)) :
    piOneProjection f x a ∈ (piOneBaseMap f x).ker := by
  obtain ⟨τ, rfl⟩ := π.mk_surjective a
  exact MonoidHom.mem_ker.mpr
    ((piOneProjection_mk_in_kernel f x τ).trans
      (piOne_nativeUnit_eq_groupUnit Y (targetPoint f x)))

private theorem piOneProjection_range_eq_kernel
    {X Y : SSet.{u}} [SSet.KanComplex X] [SSet.KanComplex Y]
    (f : X ⟶ Y) (x : X _⦋0⦌) :
    (piOneProjection f x).range = (piOneBaseMap f x).ker := by
  apply le_antisymm
  · rintro a ⟨b, rfl⟩
    exact piOneProjection_in_kernel f x b
  · intro a ha
    obtain ⟨σ, rfl⟩ := π.mk_surjective a
    have hGroup : piOneBaseMap f x (π.mk σ) =
        (inferInstance : Group (π 1 Y (targetPoint f x))).one :=
      MonoidHom.mem_ker.mp ha
    have hNative : piOneBaseMap f x (π.mk σ) = (1 : π 1 Y (targetPoint f x)) :=
      hGroup.trans (piOne_nativeUnit_eq_groupUnit Y (targetPoint f x)).symm
    have hClass : π.mk (SSet.PtSimplex.map f rfl σ) = (1 : π 1 Y (targetPoint f x)) :=
      (π.map_mk f rfl σ).symm.trans hNative
    let τ := loopLiftOfTargetNull f x σ hClass
    refine ⟨π.mk τ, ?_⟩
    rw [piOneProjection_mk, loopLiftOfTargetNull_projection]

private def piOneKernelMap
    {X Y : SSet.{u}} [SSet.KanComplex X] [SSet.KanComplex Y]
    (f : X ⟶ Y) (x : X _⦋0⦌) :
    π 1 (space f x) (point f x) →* (piOneBaseMap f x).ker :=
  (piOneProjection f x).codRestrict _ (piOneProjection_in_kernel f x)

private def piOneKernelEquiv
    {X Y : SSet.{u}} [SSet.KanComplex X] [SSet.KanComplex Y]
    (f : X ⟶ Y) (x : X _⦋0⦌) :
    π 1 (space f x) (point f x) ≃* (piOneBaseMap f x).ker := by
  apply MulEquiv.ofBijective (piOneKernelMap f x)
  constructor
  · intro a b h
    apply piOneProjection_injective f x
    exact congrArg Subtype.val h
  · intro a
    have ha : a.val ∈ (piOneProjection f x).range := by
      rw [piOneProjection_range_eq_kernel]
      exact a.property
    obtain ⟨b, hb⟩ := ha
    exact ⟨b, Subtype.ext hb⟩

private theorem piOneKernelEquiv_coe
    {X Y : SSet.{u}} [SSet.KanComplex X] [SSet.KanComplex Y]
    (f : X ⟶ Y) (x : X _⦋0⦌)
    (a : π 1 (space f x) (point f x)) :
    (piOneKernelEquiv f x a).val = piOneProjection f x a := by
  rfl

end OriginalSphericalNativePullback

namespace OriginalSphericalNativePullback

attribute [local instance] kan nativeCover_kanComplex

private theorem sourcePath_nonempty
    {X : SSet.{u}} [SSet.KanComplex X] [X.IsConnected]
    (x z : X _⦋0⦌) :
    Nonempty (SSet.FundamentalGroupoid.mk x ⟶ SSet.FundamentalGroupoid.mk z) := by
  let U := nativeUniversalCover X x
  obtain ⟨v⟩ := U.vertex_fiber_nonempty z
  exact ⟨nativeCoverVertexPathEquiv z v⟩

private theorem groupoidHom_from_base_surjective
    {X Y : SSet.{u}} [SSet.KanComplex X] [SSet.KanComplex Y] [X.IsConnected]
    (f : X ⟶ Y) (x z : X _⦋0⦌) (hs : Function.Surjective (piOneBaseMap f x)) :
    Function.Surjective
      ((SSet.mapFundamentalGroupoid f).map
        (X := SSet.FundamentalGroupoid.mk x) (Y := SSet.FundamentalGroupoid.mk z)) := by
  intro γ
  obtain ⟨a₀⟩ := sourcePath_nonempty x z
  let F := SSet.mapFundamentalGroupoid f
  let s := F.map a₀
  let d : End (SSet.FundamentalGroupoid.mk (targetPoint f x)) := .of (γ ≫ inv s)
  let eX := piOneMulEquivFundamentalGroupoidEnd (X := X) x
  let eY := piOneMulEquivFundamentalGroupoidEnd (X := Y) (targetPoint f x)
  obtain ⟨a, ha⟩ := hs (eY.symm d)
  have hEval : piOneBaseMap f x a = π.map f rfl 1 a := rfl
  have hNative : eY (π.map f rfl 1 a) =
      F.mapEnd (SSet.FundamentalGroupoid.mk x) (eX a) :=
    piOneMulEquivFundamentalGroupoidEnd_naturality f x a
  have hn : eY (piOneBaseMap f x a) =
      F.mapEnd (SSet.FundamentalGroupoid.mk x) (eX a) :=
    (congrArg eY hEval).trans hNative
  have hEnd : F.map (eX a).asHom = d.asHom := by
    exact congrArg End.asHom
      (hn.symm.trans ((congrArg eY ha).trans (eY.apply_symm_apply d)))
  refine ⟨(eX a).asHom ≫ a₀, ?_⟩
  rw [F.map_comp, hEnd]
  change (γ ≫ inv s) ≫ s = γ
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

end OriginalSphericalNativePullback

namespace OriginalSphericalNativePullback

attribute [local instance] kan nativeCover_kanComplex

private theorem flatSquare {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) :
    sourceProjection f x ≫ (f ≫ nativeCoverUnit Y) =
      underProjection f x ≫ nativeCoverNerveProjection Y (targetPoint f x) := by
  have hInner : nativeCoverProjection Y (targetPoint f x) ≫ nativeCoverUnit Y =
      nativeCoverUnderProjection Y (targetPoint f x) ≫
        nativeCoverNerveProjection Y (targetPoint f x) := by
    exact pullback.condition
  calc
    sourceProjection f x ≫ (f ≫ nativeCoverUnit Y) =
      (sourceProjection f x ≫ f) ≫ nativeCoverUnit Y := (Category.assoc _ _ _).symm
    _ = (coverProjection f x ≫ nativeCoverProjection Y (targetPoint f x)) ≫
        nativeCoverUnit Y := congrArg (fun t => t ≫ nativeCoverUnit Y) (square f x)
    _ = coverProjection f x ≫ (nativeCoverProjection Y (targetPoint f x) ≫
        nativeCoverUnit Y) := Category.assoc _ _ _
    _ = coverProjection f x ≫ (nativeCoverUnderProjection Y (targetPoint f x) ≫
        nativeCoverNerveProjection Y (targetPoint f x)) :=
      congrArg (fun t => coverProjection f x ≫ t) hInner
    _ = underProjection f x ≫ nativeCoverNerveProjection Y (targetPoint f x) :=
      (Category.assoc _ _ _).symm

private theorem point_under {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) :
    (underProjection f x).app _ (point f x) = underPoint f x := by
  have h := constPoint_under (T := (Δ[0] : SSet.{u})) f x
  have h₀ := congrArg SSet.yonedaEquiv h
  simpa only [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_const] using h₀

private theorem exists_edge_from_point
    {X Y : SSet.{u}} [SSet.KanComplex X] [SSet.KanComplex Y] [X.IsConnected]
    (f : X ⟶ Y) (x : X _⦋0⦌) (hs : Function.Surjective (piOneBaseMap f x))
    (v : (space f x) _⦋0⦌) : Nonempty ((space f x).Edge (point f x) v) := by
  let P := space f x
  let Γ := SSet.FundamentalGroupoid Y
  let y : Γ := SSet.FundamentalGroupoid.mk (targetPoint f x)
  let U : SSet.{u} := CategoryTheory.nerve (CategoryTheory.Under y)
  let B : SSet.{u} := CategoryTheory.nerve Γ
  let p := sourceProjection f x
  let r := underProjection f x
  let η : X ⟶ B := f ≫ nativeCoverUnit Y
  let q : U ⟶ B := nativeCoverNerveProjection Y (targetPoint f x)
  let z : X _⦋0⦌ := p.app (Opposite.op ⦋0⦌) v
  let a : U _⦋0⦌ := r.app (Opposite.op ⦋0⦌) v
  let V : CategoryTheory.Under y := CategoryTheory.nerveEquiv a
  let U₀ : CategoryTheory.Under y := CategoryTheory.Under.mk (𝟙 y)
  have ha : CategoryTheory.nerveEquiv.symm V = a :=
    (CategoryTheory.nerveEquiv (C := CategoryTheory.Under y)).symm_apply_apply a
  have hv : η.app (Opposite.op ⦋0⦌) z = q.app (Opposite.op ⦋0⦌) a := by
    exact congrArg (fun t : P ⟶ B => t.app (Opposite.op ⦋0⦌) v) (flatSquare f x)
  have hy : η.app (Opposite.op ⦋0⦌) z =
      CategoryTheory.nerveEquiv.symm (SSet.FundamentalGroupoid.mk (f.app _ z)) := by
    change (nativeCoverUnit Y).app _ (f.app _ z) = _
    exact SSet.fundamentalGroupoidNerveEquiv_app_zero Y Γ (𝟭 Γ) (f.app _ z)
  have hqV : q.app (Opposite.op ⦋0⦌) (CategoryTheory.nerveEquiv.symm V) =
      CategoryTheory.nerveEquiv.symm V.right := by
    exact CategoryTheory.nerveMap_app_mk₀ (CategoryTheory.Under.forget y) V
  have hqa : q.app (Opposite.op ⦋0⦌) a = CategoryTheory.nerveEquiv.symm V.right :=
    (congrArg (fun t : U _⦋0⦌ => q.app _ t) ha.symm).trans hqV
  have κ : V.right = SSet.FundamentalGroupoid.mk (f.app _ z) := by
    apply (CategoryTheory.nerveEquiv (C := Γ)).symm.injective
    exact hqa.symm.trans (hv.symm.trans hy)
  let γ : SSet.FundamentalGroupoid.mk (targetPoint f x) ⟶
      SSet.FundamentalGroupoid.mk (f.app _ z) := V.hom ≫ eqToHom κ
  obtain ⟨φ, hφ⟩ := groupoidHom_from_base_surjective f x z hs γ
  obtain ⟨e, he⟩ := SSet.FundamentalGroupoid.homMk_surjective (X := X) (x := x) (y := z) φ
  have hFe : SSet.FundamentalGroupoid.homMk (e.map f) = γ := by
    rw [← SSet.mapFundamentalGroupoid_map_homMk f e, he, hφ]
  let u : U₀ ⟶ V := CategoryTheory.Under.homMk V.hom (by
    exact Category.id_comp V.hom)
  let eu : U.Edge (underPoint f x) (CategoryTheory.nerveEquiv.symm V) :=
    CategoryTheory.nerve.edgeMk u
  let eX : (Δ[1] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm e.edge
  let eU : (Δ[1] : SSet.{u}) ⟶ U := SSet.yonedaEquiv.symm eu.edge
  have hx1 : η.app (Opposite.op ⦋1⦌) e.edge =
      (ComposableArrows.mk₁ V.hom : B _⦋1⦌) := by
    have hid : η.app (Opposite.op ⦋1⦌) e.edge =
        (ComposableArrows.mk₁ (SSet.FundamentalGroupoid.homMk (e.map f)) : B _⦋1⦌) := by
      change (nativeCoverUnit Y).app _ (e.map f).edge = _
      exact SSet.fundamentalGroupoidNerveEquiv_app_edge Y Γ (𝟭 Γ) (e.map f)
    exact hid.trans ((congrArg (fun t => (ComposableArrows.mk₁ t : B _⦋1⦌)) hFe).trans
      (ComposableArrows.mk₁_comp_eqToHom V.hom κ))
  have hq1 : q.app (Opposite.op ⦋1⦌) eu.edge =
      (ComposableArrows.mk₁ V.hom : B _⦋1⦌) := by
    have hEdge : eu.edge = (ComposableArrows.mk₁ u : U _⦋1⦌) :=
      CategoryTheory.nerve.edgeMk_edge u
    exact (congrArg (fun t : U _⦋1⦌ => q.app (Opposite.op ⦋1⦌) t) hEdge).trans
      (CategoryTheory.nerveMap_app_mk₁ (CategoryTheory.Under.forget y) u)
  have hcomm : eX ≫ η = eU ≫ q := by
    calc
      eX ≫ η = SSet.yonedaEquiv.symm (η.app _ e.edge) :=
        SSet.yonedaEquiv_symm_comp e.edge η
      _ = SSet.yonedaEquiv.symm (ComposableArrows.mk₁ V.hom) :=
        congrArg SSet.yonedaEquiv.symm hx1
      _ = SSet.yonedaEquiv.symm (q.app _ eu.edge) :=
        congrArg SSet.yonedaEquiv.symm hq1.symm
      _ = eU ≫ q := (SSet.yonedaEquiv_symm_comp eu.edge q).symm
  let L : (Δ[1] : SSet.{u}) ⟶ P := flatLift f x eX eU hcomm
  have hpL : L ≫ p = eX := flatLift_source f x eX eU hcomm
  have hrL : L ≫ r = eU := flatLift_under f x eX eU hcomm
  have hpb : p.app (Opposite.op ⦋0⦌) (point f x) = x := point_source f x
  have hrb : r.app (Opposite.op ⦋0⦌) (point f x) = underPoint f x := point_under f x
  have hsrcp : (SSet.stdSimplex.δ (1 : Fin 2) ≫ L) ≫ p =
      (SSet.const (point f x) : (Δ[0] : SSet.{u}) ⟶ P) ≫ p := by
    calc
      (SSet.stdSimplex.δ (1 : Fin 2) ≫ L) ≫ p =
        SSet.stdSimplex.δ (1 : Fin 2) ≫ eX := by rw [Category.assoc, hpL]
      _ = SSet.const x := by
        exact (SSet.Edge.δ_one_yonedaEquiv_symm e).trans
          (SSet.yonedaEquiv_symm_zero (X := X) (x))
      _ = _ := (constPoint_source f x).symm
  have hsrcr : (SSet.stdSimplex.δ (1 : Fin 2) ≫ L) ≫ r =
      (SSet.const (point f x) : (Δ[0] : SSet.{u}) ⟶ P) ≫ r := by
    calc
      (SSet.stdSimplex.δ (1 : Fin 2) ≫ L) ≫ r =
        SSet.stdSimplex.δ (1 : Fin 2) ≫ eU := by rw [Category.assoc, hrL]
      _ = SSet.const (underPoint f x) := by
        exact (SSet.Edge.δ_one_yonedaEquiv_symm eu).trans
          (SSet.yonedaEquiv_symm_zero (X := U) (underPoint f x))
      _ = _ := (constPoint_under f x).symm
  have htgtp : (SSet.stdSimplex.δ (0 : Fin 2) ≫ L) ≫ p =
      (SSet.const v : (Δ[0] : SSet.{u}) ⟶ P) ≫ p := by
    calc
      (SSet.stdSimplex.δ (0 : Fin 2) ≫ L) ≫ p =
        SSet.stdSimplex.δ (0 : Fin 2) ≫ eX := by rw [Category.assoc, hpL]
      _ = SSet.const z := by
        exact (SSet.Edge.δ_zero_yonedaEquiv_symm e).trans
          (SSet.yonedaEquiv_symm_zero (X := X) (z))
      _ = _ := (SSet.const_comp v p).symm
  have htgtr : (SSet.stdSimplex.δ (0 : Fin 2) ≫ L) ≫ r =
      (SSet.const v : (Δ[0] : SSet.{u}) ⟶ P) ≫ r := by
    calc
      (SSet.stdSimplex.δ (0 : Fin 2) ≫ L) ≫ r =
        SSet.stdSimplex.δ (0 : Fin 2) ≫ eU := by rw [Category.assoc, hrL]
      _ = SSet.const (CategoryTheory.nerveEquiv.symm V) := by
        exact (SSet.Edge.δ_zero_yonedaEquiv_symm eu).trans
          (SSet.yonedaEquiv_symm_zero (X := U) (CategoryTheory.nerveEquiv.symm V))
      _ = SSet.const a := congrArg SSet.const ha
      _ = _ := (SSet.const_comp v r).symm
  have hsrc : SSet.stdSimplex.δ (1 : Fin 2) ≫ L = SSet.const (point f x) :=
    hom_ext f x hsrcp hsrcr
  have htgt : SSet.stdSimplex.δ (0 : Fin 2) ≫ L = SSet.const v :=
    hom_ext f x htgtp htgtr
  refine ⟨SSet.Edge.mk (SSet.yonedaEquiv L) ?_ ?_⟩
  · exact (SSet.stdSimplex.yonedaEquiv_δ_comp L (1 : Fin 2)).symm.trans
      ((congrArg SSet.yonedaEquiv hsrc).trans (SSet.yonedaEquiv_const (point f x)))
  · exact (SSet.stdSimplex.yonedaEquiv_δ_comp L (0 : Fin 2)).symm.trans
      ((congrArg SSet.yonedaEquiv htgt).trans (SSet.yonedaEquiv_const v))

private theorem connected_of_piOne_surjective
    {X Y : SSet.{u}} [SSet.KanComplex X] [SSet.KanComplex Y] [X.IsConnected]
    (f : X ⟶ Y) (x : X _⦋0⦌) (hs : Function.Surjective (piOneBaseMap f x)) :
    (space f x).IsConnected := by
  apply (SSet.isConnected_iff (X := space f x)).mpr
  constructor
  · constructor
    intro a b
    obtain ⟨v, rfl⟩ := SSet.π₀.mk_surjective a
    obtain ⟨w, rfl⟩ := SSet.π₀.mk_surjective b
    obtain ⟨ev⟩ := exists_edge_from_point f x hs v
    obtain ⟨ew⟩ := exists_edge_from_point f x hs w
    exact (SSet.π₀.sound ev).symm.trans (SSet.π₀.sound ew)
  · exact ⟨point f x⟩

end OriginalSphericalNativePullback

namespace OriginalSphericalNativePullback

private def realizationPiOneEquiv
    (K : SSet.{u}) [SSet.KanComplex K] (v : K _⦋0⦌) :
    π 1 K v ≃* FundamentalGroup (SSet.toTop.obj K) (SSet.realizedVertex v) :=
  (piOneMulEquivFundamentalGroupoidEnd v).trans
    (SSet.realizationFundamentalGroupoidFunctorEndMulEquiv K v)

private theorem realizationPiOne_subsingleton
    (K : SSet.{u}) [SSet.KanComplex K] (v : K _⦋0⦌)
    [Subsingleton (π 1 K v)] :
    Subsingleton (FundamentalGroup (SSet.toTop.obj K) (SSet.realizedVertex v)) := by
  constructor
  intro a b
  apply (realizationPiOneEquiv K v).symm.injective
  exact Subsingleton.elim _ _

private theorem realizationPiOne_perfect
    (K : SSet.{u}) [SSet.KanComplex K] (v : K _⦋0⦌)
    [Group.IsPerfect (π 1 K v)] :
    Group.IsPerfect (FundamentalGroup (SSet.toTop.obj K) (SSet.realizedVertex v)) :=
  Group.IsPerfect.ofSurjective (f := (realizationPiOneEquiv K v).toMonoidHom)
    (realizationPiOneEquiv K v).surjective

private theorem realizedHomologyOne_isZero_of_piOne_perfect
    (K : SSet.{u}) [SSet.KanComplex K] [K.IsConnected] (v : K _⦋0⦌)
    [Group.IsPerfect (π 1 K v)] :
    IsZero (((singularHomologyFunctor AddCommGrpCat.{u} 1).obj
      (singularIntegralCoefficients : AddCommGrpCat.{u})).obj (SSet.toTop.obj K)) := by
  let Z := SSet.toTop.obj K
  let z := SSet.realizedVertex v
  let : PathConnectedSpace Z := SSet.pathConnectedSpace_realization_of_isConnected K
  let : Group.IsPerfect (FundamentalGroup Z z) := realizationPiOne_perfect K v
  let : Group.IsPerfect (Abelianization (FundamentalGroup Z z)) :=
    Group.IsPerfect.ofSurjective (f := Abelianization.of)
      (QuotientGroup.mk'_surjective (commutator (FundamentalGroup Z z)))
  let : Subsingleton (Abelianization (FundamentalGroup Z z)) := inferInstance
  let : Subsingleton (Additive (Abelianization (FundamentalGroup Z z))) := inferInstance
  have hA : IsZero (AddCommGrpCat.of (Additive (Abelianization (FundamentalGroup Z z)))) :=
    AddCommGrpCat.isZero_of_subsingleton _
  exact hA.of_iso (TopCat.fundamentalGroupAbelianizationHomologyOneIso Z z).symm

end OriginalSphericalNativePullback

namespace OriginalSphericalNativePullback

attribute [local instance] kan nativeCover_kanComplex TopCat.toSSet_obj_kanComplex

/- These calls reuse the public computed nonabelian comparison laws.
No point equality is supplied as an additional input. -/

private def singularPiOneEquiv (X : TopCat.{u}) (x : X) :
    π 1 (TopCat.toSSet.obj X) (TopCat.toSSetObj₀Equiv.symm x) ≃*
      FundamentalGroup X x :=
  (piOneMulEquivFundamentalGroupoidEnd (TopCat.toSSetObj₀Equiv.symm x)).trans
    (TopCat.singularFundamentalGroupoidEndMulEquiv X x)

private def singularTargetPiOneEquiv
    {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    π 1 (TopCat.toSSet.obj Y)
        (targetPoint (TopCat.toSSet.map f) (TopCat.toSSetObj₀Equiv.symm x)) ≃*
      FundamentalGroup Y (f x) := by
  let e := TopCat.singularMappedVertexIso f x
  let c : End (SSet.FundamentalGroupoid.mk
        (targetPoint (TopCat.toSSet.map f) (TopCat.toSSetObj₀Equiv.symm x))) ≃*
      End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm (f x))) := by
    exact e.conj
  exact (piOneMulEquivFundamentalGroupoidEnd _).trans
    (c.trans (TopCat.singularFundamentalGroupoidEndMulEquiv Y (f x)))

private theorem singularPiOneEquiv_square
    {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X)
    (a : π 1 (TopCat.toSSet.obj X) (TopCat.toSSetObj₀Equiv.symm x)) :
    singularTargetPiOneEquiv f x
        (piOneBaseMap (TopCat.toSSet.map f) (TopCat.toSSetObj₀Equiv.symm x) a) =
      FundamentalGroup.mapOfEq f.hom rfl (singularPiOneEquiv X x a) := by
  let sx := TopCat.toSSetObj₀Equiv.symm x
  let sy := TopCat.toSSetObj₀Equiv.symm (f x)
  let sf := TopCat.toSSet.map f
  let e := TopCat.singularMappedVertexIso f x
  let EX := TopCat.singularFundamentalGroupoidEndMulEquiv X x
  let EY := TopCat.singularFundamentalGroupoidEndMulEquiv Y (f x)
  have hSource : EX.symm (singularPiOneEquiv X x a) =
      piOneMulEquivFundamentalGroupoidEnd sx a :=
    EX.symm_apply_apply (piOneMulEquivFundamentalGroupoidEnd sx a)
  have hEval : piOneBaseMap sf sx a = π.map sf rfl 1 a := rfl
  have hNative : piOneMulEquivFundamentalGroupoidEnd
      (targetPoint sf sx) (piOneBaseMap sf sx a) =
        (SSet.mapFundamentalGroupoid sf).mapEnd
          (SSet.FundamentalGroupoid.mk sx) (piOneMulEquivFundamentalGroupoidEnd sx a) :=
    (congrArg (piOneMulEquivFundamentalGroupoidEnd (targetPoint sf sx)) hEval).trans
      (piOneMulEquivFundamentalGroupoidEnd_naturality sf sx a)
  have hLeft : EY.symm
      (singularTargetPiOneEquiv f x (piOneBaseMap sf sx a)) =
        SSet.basedFundamentalGroupHom sf sx sy e
          (piOneMulEquivFundamentalGroupoidEnd sx a) := by
    have hCancel : EY.symm
        (singularTargetPiOneEquiv f x (piOneBaseMap sf sx a)) =
          e.conj (piOneMulEquivFundamentalGroupoidEnd (targetPoint sf sx)
            (piOneBaseMap sf sx a)) :=
      EY.symm_apply_apply _
    exact hCancel.trans (congrArg e.conj hNative)
  have hOriginal := TopCat.singularEnd_inverse_naturality f x
    (singularPiOneEquiv X x a)
  have hRight : EY.symm (FundamentalGroup.mapOfEq (x := x) (y := f x) f.hom rfl
      (singularPiOneEquiv X x a)) =
        SSet.basedFundamentalGroupHom sf sx sy e
          (piOneMulEquivFundamentalGroupoidEnd sx a) :=
    hOriginal.trans (congrArg (SSet.basedFundamentalGroupHom sf sx sy e) hSource)
  exact EY.symm.injective (hLeft.trans hRight.symm)

private theorem singularPiOneMap_surjective
    {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X)
    (hs : Function.Surjective (FundamentalGroup.mapOfEq (x := x) (y := f x) f.hom rfl)) :
    Function.Surjective
      (piOneBaseMap (TopCat.toSSet.map f) (TopCat.toSSetObj₀Equiv.symm x)) := by
  intro b
  obtain ⟨g, hg⟩ := hs (singularTargetPiOneEquiv f x b)
  refine ⟨(singularPiOneEquiv X x).symm g, ?_⟩
  apply (singularTargetPiOneEquiv f x).injective
  have h := singularPiOneEquiv_square f x ((singularPiOneEquiv X x).symm g)
  rw [(singularPiOneEquiv X x).apply_symm_apply] at h
  exact h.trans hg

private abbrev actualMap (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :=
  TopCat.toSSet.map (LoopCellAttachment.inclusion X x P)

private abbrev actualBase (X : TopCat.{u}) (x : X) :=
  TopCat.toSSetObj₀Equiv.symm x

private abbrev actualPullback (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :=
  space (actualMap X x P) (actualBase X x)

private abbrev actualPoint (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :=
  point (actualMap X x P) (actualBase X x)

private theorem actualPiOneBaseMap_surjective
    (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    Function.Surjective (piOneBaseMap (actualMap X x P) (actualBase X x)) :=
  singularPiOneMap_surjective (LoopCellAttachment.inclusion X x P) x
    (LoopCellAttachment.pi1Map_surjective X x P)

private def actualPiOneToOriginal
    (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    π 1 (actualPullback X x P) (actualPoint X x P) →* FundamentalGroup X x :=
  (singularPiOneEquiv X x).toMonoidHom.comp
    (piOneProjection (actualMap X x P) (actualBase X x))

private theorem actualPiOneToOriginal_injective
    (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    Function.Injective (actualPiOneToOriginal X x P) :=
  (singularPiOneEquiv X x).injective.comp
    (piOneProjection_injective (actualMap X x P) (actualBase X x))

private theorem actualPiOneToOriginal_range
    (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    (actualPiOneToOriginal X x P).range = P := by
  apply le_antisymm
  · rintro g ⟨a, rfl⟩
    let b := piOneProjection (actualMap X x P) (actualBase X x) a
    let e := singularTargetPiOneEquiv (LoopCellAttachment.inclusion X x P) x
    have hb : piOneBaseMap (actualMap X x P) (actualBase X x) b =
        (inferInstance : Group (π 1 (TopCat.toSSet.obj (LoopCellAttachment.space X x P))
          (targetPoint (actualMap X x P) (actualBase X x)))).one :=
      MonoidHom.mem_ker.mp
        (piOneProjection_in_kernel (actualMap X x P) (actualBase X x) a)
    have hSquare := singularPiOneEquiv_square
      (LoopCellAttachment.inclusion X x P) x b
    have hKilled : LoopCellAttachment.pi1Map X x P
        (actualPiOneToOriginal X x P a) = 1 :=
      hSquare.symm.trans ((congrArg e hb).trans e.toMonoidHom.map_one)
    have hKer : actualPiOneToOriginal X x P a ∈ (LoopCellAttachment.pi1Map X x P).ker :=
      MonoidHom.mem_ker.mpr hKilled
    exact (le_of_eq (AlgebraicTopology.CellQuotientVanKampen.ker_pi1Map X x P)) hKer
  · intro g hg
    let a := (singularPiOneEquiv X x).symm g
    let e := singularTargetPiOneEquiv (LoopCellAttachment.inclusion X x P) x
    have hSquare := singularPiOneEquiv_square (LoopCellAttachment.inclusion X x P) x a
    have he : singularPiOneEquiv X x a = g :=
      (singularPiOneEquiv X x).apply_symm_apply g
    have hKilled : LoopCellAttachment.pi1Map X x P (singularPiOneEquiv X x a) = 1 :=
      (congrArg (LoopCellAttachment.pi1Map X x P) he).trans
        (LoopCellAttachment.pi1Map_kills X x P ⟨g, hg⟩)
    have hGroup : piOneBaseMap (actualMap X x P) (actualBase X x) a =
        (inferInstance : Group (π 1 (TopCat.toSSet.obj (LoopCellAttachment.space X x P))
          (targetPoint (actualMap X x P) (actualBase X x)))).one :=
      e.injective (hSquare.trans (hKilled.trans e.toMonoidHom.map_one.symm))
    have ha : a ∈ (piOneBaseMap (actualMap X x P) (actualBase X x)).ker :=
      MonoidHom.mem_ker.mpr hGroup
    have haRange : a ∈ (piOneProjection (actualMap X x P) (actualBase X x)).range :=
      (le_of_eq (piOneProjection_range_eq_kernel (actualMap X x P) (actualBase X x)).symm) ha
    obtain ⟨b, hb⟩ := haRange
    refine ⟨b, ?_⟩
    exact (congrArg (singularPiOneEquiv X x) hb).trans
      ((singularPiOneEquiv X x).apply_symm_apply g)

private def actualPiOneSubgroupMap
    (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    π 1 (actualPullback X x P) (actualPoint X x P) →* P :=
        (actualPiOneToOriginal X x P).codRestrict P (fun a =>
    (le_of_eq (actualPiOneToOriginal_range X x P))
      (show actualPiOneToOriginal X x P a ∈ (actualPiOneToOriginal X x P).range from ⟨a, rfl⟩))

private def actualPiOneSubgroupEquiv
    (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    π 1 (actualPullback X x P) (actualPoint X x P) ≃* P := by
  apply MulEquiv.ofBijective (actualPiOneSubgroupMap X x P)
  constructor
  · intro a b h
    apply actualPiOneToOriginal_injective X x P
    exact congrArg Subtype.val h
  · intro p
    have hp : p.val ∈ (actualPiOneToOriginal X x P).range := by
      rw [actualPiOneToOriginal_range X x P]
      exact p.property
    obtain ⟨a, ha⟩ := hp
    exact ⟨a, Subtype.ext ha⟩

private theorem actualPiOneSubgroupEquiv_value
    (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) [P.Normal]
    (a : π 1 (actualPullback X x P) (actualPoint X x P)) :
    (actualPiOneSubgroupEquiv X x P a).val = actualPiOneToOriginal X x P a := by
  rfl

private theorem actualPullback_connected
    (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    (actualPullback X x P).IsConnected :=
  connected_of_piOne_surjective (actualMap X x P) (actualBase X x)
    (actualPiOneBaseMap_surjective X x P)

private theorem actualPullback_piOne_perfect
    (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x))
    [P.Normal] [Group.IsPerfect P] :
    Group.IsPerfect (π 1 (actualPullback X x P) (actualPoint X x P)) :=
  Group.IsPerfect.ofSurjective (f := (actualPiOneSubgroupEquiv X x P).symm.toMonoidHom)
    (actualPiOneSubgroupEquiv X x P).symm.surjective

private theorem actualPullback_realization_pathConnected
    (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    PathConnectedSpace (SSet.toTop.obj (actualPullback X x P)) := by
  let := actualPullback_connected X x P
  exact SSet.pathConnectedSpace_realization_of_isConnected (actualPullback X x P)

private theorem actualPullback_homologyOne_isZero
    (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    IsZero (((singularHomologyFunctor AddCommGrpCat.{u} 1).obj
      (singularIntegralCoefficients : AddCommGrpCat.{u})).obj
        (SSet.toTop.obj (actualPullback X x P))) := by
  let := actualPullback_connected X x P
  let := actualPullback_piOne_perfect X x P
  exact realizedHomologyOne_isZero_of_piOne_perfect
    (actualPullback X x P) (actualPoint X x P)

end OriginalSphericalNativePullback

namespace OriginalSphericalNativePullback

private def simplexDiskIso (n : ℕ) :
    SSet.toTop.obj (Δ[n] : SSet.{u}) ≅ (classicalCellDiskPair.{u} n).fst :=
  SSet.stdSimplex.toClassicalCellDiskIso n

private def simplexBoundaryIso (n : ℕ) :
    SSet.toTop.obj (SSet.boundary.{u} n).toSSet ≅ (classicalCellDiskPair.{u} n).snd :=
  SSet.boundary.toClassicalCellBoundaryIso n

private theorem simplexDiskIso_comm (n : ℕ) :
    SSet.toTop.map (SSet.boundary.{u} n).ι ≫ (simplexDiskIso n).hom =
      (simplexBoundaryIso n).hom ≫ (classicalCellDiskPair.{u} n).map := by
  exact SSet.boundary.toClassicalCellDiskIso_comm n

private theorem simplexDiskIso_inv_comm (n : ℕ) :
    (simplexBoundaryIso n).inv ≫ SSet.toTop.map (SSet.boundary.{u} n).ι =
      (classicalCellDiskPair.{u} n).map ≫ (simplexDiskIso n).inv := by
  exact SSet.boundary.toClassicalCellDiskIso_inv_comm n

end OriginalSphericalNativePullback

namespace OriginalSphericalNativePullback

attribute [local instance] kan nativeCover_kanComplex TopCat.toSSet_obj_kanComplex

private theorem realizedAdjunct_counit {K : SSet.{u}} {Y : TopCat.{u}}
    (a : SSet.toTop.obj K ⟶ Y) :
    SSet.toTop.map (sSetTopAdj.homEquiv K Y a) ≫ sSetTopAdj.counit.app Y = a := by
  have h := (sSetTopAdj.homEquiv K Y).symm_apply_apply a
  rw [Adjunction.homEquiv_counit] at h
  exact h

private def originalDiskAdjunct
    (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) (p : P) :
    (Δ[2] : SSet.{u}) ⟶ TopCat.toSSet.obj (LoopCellAttachment.space X x P) :=
  sSetTopAdj.homEquiv _ _
    ((simplexDiskIso 2).hom ≫ LoopCellAttachment.cell X x P p)

private def originalBoundaryAdjunct
    (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) (p : P) :
    (SSet.boundary.{u} 2).toSSet ⟶ TopCat.toSSet.obj X :=
  sSetTopAdj.homEquiv _ _
    ((simplexBoundaryIso 2).hom ≫ LoopCellAttachment.attachingMap X x P p)

private theorem originalAdjunct_square
    (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) (p : P) :
    originalBoundaryAdjunct X x P p ≫ actualMap X x P =
      (SSet.boundary.{u} 2).ι ≫ originalDiskAdjunct X x P p := by
  have h : SSet.toTop.map (SSet.boundary.{u} 2).ι ≫
      ((simplexDiskIso 2).hom ≫ LoopCellAttachment.cell X x P p) =
    ((simplexBoundaryIso 2).hom ≫ LoopCellAttachment.attachingMap X x P p) ≫
      LoopCellAttachment.inclusion X x P := by
    calc
      SSet.toTop.map (SSet.boundary.{u} 2).ι ≫
          ((simplexDiskIso 2).hom ≫ LoopCellAttachment.cell X x P p) =
        (SSet.toTop.map (SSet.boundary.{u} 2).ι ≫ (simplexDiskIso 2).hom) ≫
          LoopCellAttachment.cell X x P p := (Category.assoc _ _ _).symm
      _ = ((simplexBoundaryIso 2).hom ≫ (classicalCellDiskPair.{u} 2).map) ≫
          LoopCellAttachment.cell X x P p := by rw [simplexDiskIso_comm]
      _ = (simplexBoundaryIso 2).hom ≫
          ((classicalCellDiskPair.{u} 2).map ≫ LoopCellAttachment.cell X x P p) :=
        Category.assoc _ _ _
      _ = (simplexBoundaryIso 2).hom ≫
          (LoopCellAttachment.attachingMap X x P p ≫ LoopCellAttachment.inclusion X x P) :=
        congrArg (fun t => (simplexBoundaryIso 2).hom ≫ t)
          (LoopCellAttachment.boundary_gluing X x P p).symm
      _ = ((simplexBoundaryIso 2).hom ≫ LoopCellAttachment.attachingMap X x P p) ≫
          LoopCellAttachment.inclusion X x P := (Category.assoc _ _ _).symm
  exact (sSetTopAdj.homEquiv_naturality_left_square (SSet.boundary.{u} 2).ι
    ((simplexDiskIso 2).hom ≫ LoopCellAttachment.cell X x P p)
    ((simplexBoundaryIso 2).hom ≫ LoopCellAttachment.attachingMap X x P p)
    (LoopCellAttachment.inclusion X x P) h).symm

private theorem actualTarget_pathConnected
    (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    PathConnectedSpace (LoopCellAttachment.space X x P) :=
  CellFamilyAttachment.pathConnectedSpace X 1 (LoopCellAttachment.attachingMap X x P)

private theorem actualTarget_simplicial_connected
    (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    (TopCat.toSSet.obj (LoopCellAttachment.space X x P)).IsConnected := by
  let := actualTarget_pathConnected X x P
  infer_instance

private def diskStartVertex
    (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) (p : P) :
    {v : (cover (actualMap X x P) (actualBase X x)) _⦋0⦌ //
      (nativeCoverProjection (TopCat.toSSet.obj (LoopCellAttachment.space X x P))
        (targetPoint (actualMap X x P) (actualBase X x))).app _ v =
          (originalDiskAdjunct X x P p).app _ (SSet.stdSimplex.obj₀Equiv.symm
            (⟨0, Nat.zero_lt_succ 2⟩ : Fin 3))} := by
  let Y := TopCat.toSSet.obj (LoopCellAttachment.space X x P)
  let y := targetPoint (actualMap X x P) (actualBase X x)
  letI : Y.IsConnected := actualTarget_simplicial_connected X x P
  exact Classical.choice ((nativeUniversalCover Y y).vertex_fiber_nonempty _)

private theorem diskStartVertex_lifts
    (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) (p : P) :
    (SSet.yonedaEquiv.symm (SSet.stdSimplex.obj₀Equiv.symm
      (⟨0, Nat.zero_lt_succ 2⟩ : Fin 3)) : (Δ[0] : SSet.{u}) ⟶ Δ[2]) ≫
        originalDiskAdjunct X x P p =
      SSet.const ((nativeCoverProjection
        (TopCat.toSSet.obj (LoopCellAttachment.space X x P))
        (targetPoint (actualMap X x P) (actualBase X x))).app _
          (diskStartVertex X x P p).val) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, SSet.yonedaEquiv_const]
  exact (diskStartVertex X x P p).property.symm

private def liftedDiskSimplex
    (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) (p : P) :
    (Δ[2] : SSet.{u}) ⟶ cover (actualMap X x P) (actualBase X x) :=
  nativeCoverSimplexLiftFromFirstMap (originalDiskAdjunct X x P p)
    (diskStartVertex X x P p).val (diskStartVertex_lifts X x P p)

private theorem liftedDiskSimplex_projection
    (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) (p : P) :
    liftedDiskSimplex X x P p ≫
        nativeCoverProjection (TopCat.toSSet.obj (LoopCellAttachment.space X x P))
          (targetPoint (actualMap X x P) (actualBase X x)) =
      originalDiskAdjunct X x P p :=
  nativeCoverSimplexLiftFromFirstMap_projection _ _ _

private def liftedBoundarySimplex
    (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) (p : P) :
    (SSet.boundary.{u} 2).toSSet ⟶ actualPullback X x P :=
  pullback.lift (originalBoundaryAdjunct X x P p)
    ((SSet.boundary.{u} 2).ι ≫ liftedDiskSimplex X x P p) (by
      rw [Category.assoc, liftedDiskSimplex_projection]
      exact originalAdjunct_square X x P p)

private theorem liftedBoundarySimplex_source
    (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) (p : P) :
    liftedBoundarySimplex X x P p ≫
        sourceProjection (actualMap X x P) (actualBase X x) =
      originalBoundaryAdjunct X x P p := by
  dsimp only [liftedBoundarySimplex, sourceProjection, space, actualPullback]
  exact pullback.lift_fst _ _ _

private theorem liftedBoundarySimplex_cover
    (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) (p : P) :
    liftedBoundarySimplex X x P p ≫
        coverProjection (actualMap X x P) (actualBase X x) =
      (SSet.boundary.{u} 2).ι ≫ liftedDiskSimplex X x P p := by
  dsimp only [liftedBoundarySimplex, coverProjection, space, actualPullback]
  exact pullback.lift_snd _ _ _

private theorem actualMap_mono
    (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    Mono (actualMap X x P) := by
  let : Mono (LoopCellAttachment.inclusion X x P) :=
    (TopCat.mono_iff_injective _).mpr
        (LoopCellAttachment.inclusion_isClosedEmbedding X x P).injective
  infer_instance

private theorem coverProjection_mono
    (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    Mono (coverProjection (actualMap X x P) (actualBase X x)) := by
  let := actualMap_mono X x P
  dsimp only [coverProjection, space]
  infer_instance

private theorem realizedCoverProjection_closed
    (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    IsClosedEmbedding (SSet.toTop.map
      (coverProjection (actualMap X x P) (actualBase X x))) := by
  let := coverProjection_mono X x P
  exact TopCat.closedT1Embeddings_le_isClosedEmbedding _
    (SSet.closedT1Embeddings_toTop_map_of_mono _)

private def liftedPair
    (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) : TopPair.{u} :=
  TopPair.of (SSet.toTop.map (coverProjection (actualMap X x P) (actualBase X x)))
    (realizedCoverProjection_closed X x P).isEmbedding

private def liftedCharacteristicDiskPair
    (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) (p : P) :
    classicalCellDiskPair.{u} 2 ⟶ liftedPair X x P :=
  TopPair.ofHom
    ((simplexDiskIso 2).inv ≫ SSet.toTop.map (liftedDiskSimplex X x P p))
    ((simplexBoundaryIso 2).inv ≫ SSet.toTop.map (liftedBoundarySimplex X x P p)) (by
      calc
        ((simplexBoundaryIso 2).inv ≫ SSet.toTop.map (liftedBoundarySimplex X x P p)) ≫
            SSet.toTop.map (coverProjection (actualMap X x P) (actualBase X x)) =
          (simplexBoundaryIso 2).inv ≫ SSet.toTop.map
            (liftedBoundarySimplex X x P p ≫
              coverProjection (actualMap X x P) (actualBase X x)) := by
            rw [SSet.toTop.map_comp, Category.assoc]
        _ = (simplexBoundaryIso 2).inv ≫ SSet.toTop.map
            ((SSet.boundary.{u} 2).ι ≫ liftedDiskSimplex X x P p) := by
            rw [liftedBoundarySimplex_cover]
        _ = ((simplexBoundaryIso 2).inv ≫ SSet.toTop.map (SSet.boundary.{u} 2).ι) ≫
            SSet.toTop.map (liftedDiskSimplex X x P p) := by
            rw [SSet.toTop.map_comp, Category.assoc]
        _ = ((classicalCellDiskPair.{u} 2).map ≫ (simplexDiskIso 2).inv) ≫
            SSet.toTop.map (liftedDiskSimplex X x P p) := by rw [simplexDiskIso_inv_comm]
        _ = (classicalCellDiskPair.{u} 2).map ≫
            ((simplexDiskIso 2).inv ≫ SSet.toTop.map (liftedDiskSimplex X x P p)) :=
          Category.assoc _ _ _)

private def liftedPairToOriginal
    (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    liftedPair X x P ⟶ LoopCellAttachment.relativePair X x P :=
  TopPair.ofHom
    (SSet.toTop.map (nativeCoverProjection
      (TopCat.toSSet.obj (LoopCellAttachment.space X x P))
      (targetPoint (actualMap X x P) (actualBase X x))) ≫
        sSetTopAdj.counit.app (LoopCellAttachment.space X x P))
    (SSet.toTop.map (sourceProjection (actualMap X x P) (actualBase X x)) ≫
      sSetTopAdj.counit.app X) (by
      change (SSet.toTop.map (sourceProjection (actualMap X x P) (actualBase X x)) ≫
          sSetTopAdj.counit.app X) ≫ LoopCellAttachment.inclusion X x P =
        SSet.toTop.map (coverProjection (actualMap X x P) (actualBase X x)) ≫
          (SSet.toTop.map (nativeCoverProjection
            (TopCat.toSSet.obj (LoopCellAttachment.space X x P))
            (targetPoint (actualMap X x P) (actualBase X x))) ≫
              sSetTopAdj.counit.app (LoopCellAttachment.space X x P))
      have hn := sSetTopAdj.counit.naturality (LoopCellAttachment.inclusion X x P)
      change SSet.toTop.map (actualMap X x P) ≫
          sSetTopAdj.counit.app (LoopCellAttachment.space X x P) =
        sSetTopAdj.counit.app X ≫ LoopCellAttachment.inclusion X x P at hn
      calc
        (SSet.toTop.map (sourceProjection (actualMap X x P) (actualBase X x)) ≫
            sSetTopAdj.counit.app X) ≫ LoopCellAttachment.inclusion X x P =
          SSet.toTop.map (sourceProjection (actualMap X x P) (actualBase X x)) ≫
            (sSetTopAdj.counit.app X ≫ LoopCellAttachment.inclusion X x P) :=
          Category.assoc _ _ _
        _ = SSet.toTop.map (sourceProjection (actualMap X x P) (actualBase X x)) ≫
            (SSet.toTop.map (actualMap X x P) ≫
              sSetTopAdj.counit.app (LoopCellAttachment.space X x P)) := by rw [← hn]
        _ = SSet.toTop.map
            (sourceProjection (actualMap X x P) (actualBase X x) ≫ actualMap X x P) ≫
              sSetTopAdj.counit.app (LoopCellAttachment.space X x P) := by
            rw [SSet.toTop.map_comp, Category.assoc]
        _ = SSet.toTop.map
            (coverProjection (actualMap X x P) (actualBase X x) ≫
              nativeCoverProjection (TopCat.toSSet.obj (LoopCellAttachment.space X x P))
                (targetPoint (actualMap X x P) (actualBase X x))) ≫
              sSetTopAdj.counit.app (LoopCellAttachment.space X x P) := by rw [square]
        _ = SSet.toTop.map (coverProjection (actualMap X x P) (actualBase X x)) ≫
            (SSet.toTop.map (nativeCoverProjection
              (TopCat.toSSet.obj (LoopCellAttachment.space X x P))
              (targetPoint (actualMap X x P) (actualBase X x))) ≫
                sSetTopAdj.counit.app (LoopCellAttachment.space X x P)) := by
            rw [SSet.toTop.map_comp, Category.assoc])

private theorem liftedCharacteristicDiskPair_fst_down
    (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) (p : P) :
    TopPair.Hom.fst (liftedCharacteristicDiskPair X x P p) ≫
        TopPair.Hom.fst (liftedPairToOriginal X x P) = LoopCellAttachment.cell X x P p := by
  change ((simplexDiskIso 2).inv ≫ SSet.toTop.map (liftedDiskSimplex X x P p)) ≫
      (SSet.toTop.map (nativeCoverProjection
        (TopCat.toSSet.obj (LoopCellAttachment.space X x P))
        (targetPoint (actualMap X x P) (actualBase X x))) ≫
          sSetTopAdj.counit.app (LoopCellAttachment.space X x P)) = _
  rw [Category.assoc, ← Category.assoc (SSet.toTop.map _) (SSet.toTop.map _),
    ← SSet.toTop.map_comp, liftedDiskSimplex_projection]
  have hAdjunct : SSet.toTop.map (originalDiskAdjunct X x P p) ≫
      sSetTopAdj.counit.app (LoopCellAttachment.space X x P) =
        (simplexDiskIso 2).hom ≫ LoopCellAttachment.cell X x P p :=
    realizedAdjunct_counit ((simplexDiskIso 2).hom ≫ LoopCellAttachment.cell X x P p)
  exact (congrArg (fun t : SSet.toTop.obj (Δ[2] : SSet.{u}) ⟶
      LoopCellAttachment.space X x P => (simplexDiskIso 2).inv ≫ t) hAdjunct).trans
    ((simplexDiskIso 2).inv_hom_id_assoc (LoopCellAttachment.cell X x P p))

private theorem liftedCharacteristicDiskPair_snd_down
    (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) (p : P) :
    TopPair.Hom.snd (liftedCharacteristicDiskPair X x P p) ≫
        TopPair.Hom.snd (liftedPairToOriginal X x P) =
      LoopCellAttachment.attachingMap X x P p := by
  change ((simplexBoundaryIso 2).inv ≫ SSet.toTop.map (liftedBoundarySimplex X x P p)) ≫
      (SSet.toTop.map (sourceProjection (actualMap X x P) (actualBase X x)) ≫
        sSetTopAdj.counit.app X) = _
  rw [Category.assoc, ← Category.assoc (SSet.toTop.map _) (SSet.toTop.map _),
    ← SSet.toTop.map_comp, liftedBoundarySimplex_source]
  have hAdjunct : SSet.toTop.map (originalBoundaryAdjunct X x P p) ≫
      sSetTopAdj.counit.app X =
        (simplexBoundaryIso 2).hom ≫ LoopCellAttachment.attachingMap X x P p :=
    realizedAdjunct_counit
      ((simplexBoundaryIso 2).hom ≫ LoopCellAttachment.attachingMap X x P p)
  exact (congrArg (fun t : SSet.toTop.obj (SSet.boundary.{u} 2).toSSet ⟶ X =>
      (simplexBoundaryIso 2).inv ≫ t) hAdjunct).trans
    ((simplexBoundaryIso 2).inv_hom_id_assoc (LoopCellAttachment.attachingMap X x P p))

private theorem liftedCharacteristicDiskPair_down
    (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) (p : P) :
    liftedCharacteristicDiskPair X x P p ≫ liftedPairToOriginal X x P =
      LoopCellAttachment.cellPairMap X x P p := by
  apply MorphismProperty.Arrow.Hom.ext
  · change TopPair.Hom.snd (liftedCharacteristicDiskPair X x P p) ≫
      TopPair.Hom.snd (liftedPairToOriginal X x P) =
        TopPair.Hom.snd (LoopCellAttachment.cellPairMap X x P p)
    rw [LoopCellAttachment.cellPairMap_snd]
    exact liftedCharacteristicDiskPair_snd_down X x P p
  · change TopPair.Hom.fst (liftedCharacteristicDiskPair X x P p) ≫
      TopPair.Hom.fst (liftedPairToOriginal X x P) =
        TopPair.Hom.fst (LoopCellAttachment.cellPairMap X x P p)
    rw [LoopCellAttachment.cellPairMap_fst]
    exact liftedCharacteristicDiskPair_fst_down X x P p

end OriginalSphericalNativePullback

namespace OriginalSphericalNativePullback

attribute [local instance] kan nativeCover_kanComplex TopCat.toSSet_obj_kanComplex

private abbrev coefficients : AddCommGrpCat.{u} := singularIntegralCoefficients
private abbrev homologyTwo := (singularHomologyFunctor AddCommGrpCat.{u} 2).obj coefficients
private abbrev relativeHomologyTwo := relativeSingularHomologyFunctor AddCommGrpCat.{u}
    coefficients 2

private def liftedPairBasePoint
    (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    (liftedPair X x P).fst :=
  SSet.realizedVertex (nativeCoverIdentityPoint
    (TopCat.toSSet.obj (LoopCellAttachment.space X x P))
    (targetPoint (actualMap X x P) (actualBase X x)))

private theorem liftedPair_fst_pathConnected
    (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    PathConnectedSpace (liftedPair X x P).fst := by
  let K := cover (actualMap X x P) (actualBase X x)
  let : K.IsConnected := nativeCover_isConnected
  exact SSet.pathConnectedSpace_realization_of_isConnected K

private theorem liftedPair_fst_piOne_subsingleton
    (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    Subsingleton (FundamentalGroup (liftedPair X x P).fst (liftedPairBasePoint X x P)) := by
  let K := cover (actualMap X x P) (actualBase X x)
  let v := nativeCoverIdentityPoint
    (TopCat.toSSet.obj (LoopCellAttachment.space X x P))
    (targetPoint (actualMap X x P) (actualBase X x))
  let : Subsingleton (π 1 K v) :=
    (nativeCover_isConnected_and_piOne_subsingleton
      (X := TopCat.toSSet.obj (LoopCellAttachment.space X x P))
      (x := targetPoint (actualMap X x P) (actualBase X x))).2 v
  exact realizationPiOne_subsingleton K v

private def liftedPairQuotient
    (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    homologyTwo.obj (liftedPair X x P).fst ⟶ relativeHomologyTwo.obj (liftedPair X x P) :=
  singularHomologyPairQuotientMap AddCommGrpCat.{u} coefficients (liftedPair X x P) 2

private theorem liftedPairQuotient_epi
    (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    Epi (liftedPairQuotient X x P) := by
  let R : AddCommGrpCat.{u} := coefficients
  let A : TopPair.{u} := liftedPair X x P
  let E : TopPair.HomologyTheoryData.{u} AddCommGrpCat.{u} :=
    singularHomologyIntData AddCommGrpCat.{u} R
  have hOldNat : IsZero (((singularHomologyFunctor AddCommGrpCat.{u} 1).obj R).obj A.snd) :=
    actualPullback_homologyOne_isZero X x P
  have hOldInt : IsZero ((E.H ((2 : ℤ) - 1)).obj A.snd) := by
    change IsZero ((singularHomologyIntFunctor AddCommGrpCat.{u} R 1).obj A.snd)
    exact hOldNat.of_iso ((singularHomologyNatToIntIso AddCommGrpCat.{u} R 1).app A.snd)
  have hBoundary : E.boundary 2 A = 0 := hOldInt.eq_of_tgt _ _
  let f : (E.H 2).obj A.fst ⟶ (E.Hₚ 2).obj A := E.toRelative 2 A
  let eAbsolute : homologyTwo.obj A.fst ≅ (E.H 2).obj A.fst :=
    ((singularHomologyNatToIntIso AddCommGrpCat.{u} R 2).app A.fst).symm
  let eRelative : (E.Hₚ 2).obj A ≅ relativeHomologyTwo.obj A :=
    (relativeSingularHomologyNatToIntIso AddCommGrpCat.{u} R 2).app A
  let : Epi f :=
      (TopPair.HomologyTheoryData.IsExact.exact_toRelative_boundary E 2 A).epi_f hBoundary
  have hEpi : Epi (eAbsolute.hom ≫ f ≫ eRelative.hom) := by infer_instance
  have hq : liftedPairQuotient X x P = eAbsolute.hom ≫ f ≫ eRelative.hom :=
    (singularHomologyIntData_toRelative_natAgreement AddCommGrpCat.{u} R 2 A).symm
  exact hq.symm ▸ hEpi

private theorem liftedPairQuotient_surjective
    (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    Function.Surjective (liftedPairQuotient X x P) := by
  let := liftedPairQuotient_epi X x P
  exact (AddCommGrpCat.epi_iff_surjective (liftedPairQuotient X x P)).mp inferInstance

private def liftedRelativeGenerator
    (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) (p : P) :
    coefficients ⟶ relativeHomologyTwo.obj (liftedPair X x P) :=
  (classicalCellDiskPairRelativeHomologyIsoOfUnivLE.{u} coefficients 2).hom ≫
    relativeHomologyTwo.map (liftedCharacteristicDiskPair X x P p)

private theorem liftedRelativeGenerator_down
    (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) (p : P) :
    liftedRelativeGenerator X x P p ≫ relativeHomologyTwo.map (liftedPairToOriginal X x P) =
      LoopCellAttachment.relativeGenerator X x P coefficients p := by
  let R : AddCommGrpCat.{u} := coefficients
  let H : TopPair.{u} ⥤ AddCommGrpCat.{u} :=
    relativeSingularHomologyFunctor AddCommGrpCat.{u} R 2
  let d : classicalCellDiskPair.{u} 2 ⟶ liftedPair X x P :=
    liftedCharacteristicDiskPair X x P p
  let f : liftedPair X x P ⟶ LoopCellAttachment.relativePair X x P :=
    liftedPairToOriginal X x P
  let g : R ⟶ H.obj (classicalCellDiskPair.{u} 2) :=
    (classicalCellDiskPairRelativeHomologyIsoOfUnivLE.{u} R 2).hom
  have hDefinition : liftedRelativeGenerator X x P p = g ≫ H.map d := rfl
  have hComposite : H.map d ≫ H.map f = H.map (d ≫ f) :=
    (H.map_comp d f).symm
  have hPair : d ≫ f = LoopCellAttachment.cellPairMap X x P p :=
    liftedCharacteristicDiskPair_down X x P p
  have hOriginal : g ≫ H.map (LoopCellAttachment.cellPairMap X x P p) =
      LoopCellAttachment.relativeGenerator X x P coefficients p :=
    (LoopCellAttachment.relativeGenerator_eq_characteristic X x P R p).symm
  calc
    liftedRelativeGenerator X x P p ≫ H.map f = (g ≫ H.map d) ≫ H.map f :=
      congrArg (fun t : R ⟶ H.obj (liftedPair X x P) => t ≫ H.map f) hDefinition
    _ = g ≫ (H.map d ≫ H.map f) := Category.assoc _ _ _
    _ = g ≫ H.map (d ≫ f) :=
      congrArg (fun t => g ≫ t) hComposite
    _ = g ≫ H.map (LoopCellAttachment.cellPairMap X x P p) :=
      congrArg (fun t : classicalCellDiskPair.{u} 2 ⟶
        LoopCellAttachment.relativePair X x P => g ≫ H.map t) hPair
    _ = LoopCellAttachment.relativeGenerator X x P coefficients p := hOriginal

private def liftedAbsoluteGenerator
    (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] (p : P) :
    homologyTwo.obj (liftedPair X x P).fst :=
  Classical.choose (liftedPairQuotient_surjective X x P
    (liftedRelativeGenerator X x P p (ULift.up (1 : ℤ))))

private theorem liftedAbsoluteGenerator_projection
    (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] (p : P) :
    liftedPairQuotient X x P (liftedAbsoluteGenerator X x P p) =
      liftedRelativeGenerator X x P p (ULift.up (1 : ℤ)) :=
  Classical.choose_spec (liftedPairQuotient_surjective X x P _)

private def liftedSphericalGenerator
    (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] (p : P) :
    (classicalCellDiskPair.{u} 3).snd ⟶ (liftedPair X x P).fst := by
  letI := liftedPair_fst_pathConnected X x P
  letI := liftedPair_fst_piOne_subsingleton X x P
  exact TopCat.classicalSphereHomologyTwoRepresentative
    (liftedPair X x P).fst (liftedPairBasePoint X x P) (liftedAbsoluteGenerator X x P p)

private theorem liftedSphericalGenerator_homology
    (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] (p : P)
    (a : coefficients.{u}) :
    (classicalCellBoundaryHomologyTwoGenerator.{u} ≫
      homologyTwo.map (liftedSphericalGenerator X x P p)) a =
        a.down • liftedAbsoluteGenerator X x P p := by
  let := liftedPair_fst_pathConnected X x P
  let := liftedPair_fst_piOne_subsingleton X x P
  exact TopCat.classicalSphereHomologyTwoRepresentative_homology
    (liftedPair X x P).fst (liftedPairBasePoint X x P) (liftedAbsoluteGenerator X x P p) a

private def originalSphericalGenerator
    (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] (p : P) :
    (classicalCellDiskPair.{u} 3).snd ⟶ LoopCellAttachment.space X x P :=
  liftedSphericalGenerator X x P p ≫ TopPair.Hom.fst (liftedPairToOriginal X x P)

private theorem liftedPairQuotient_naturality_down
    (X : TopCat.{u}) (x : X) (P : Subgroup (FundamentalGroup X x)) :
    liftedPairQuotient X x P ≫ relativeHomologyTwo.map (liftedPairToOriginal X x P) =
      homologyTwo.map (TopPair.Hom.fst (liftedPairToOriginal X x P)) ≫
        LoopCellAttachment.absoluteToRelativeHomologyTwo X x P := by
  let R : AddCommGrpCat.{u} := coefficients
  let A : TopPair.{u} := liftedPair X x P
  let B : TopPair.{u} := LoopCellAttachment.relativePair X x P
  let f : A ⟶ B := liftedPairToOriginal X x P
  let H : TopCat.{u} ⥤ AddCommGrpCat.{u} :=
    (singularHomologyFunctor AddCommGrpCat.{u} 2).obj R
  let Hrel : TopPair.{u} ⥤ AddCommGrpCat.{u} :=
    relativeSingularHomologyFunctor AddCommGrpCat.{u} R 2
  have hLifted : liftedPairQuotient X x P =
      singularHomologyPairQuotientMap AddCommGrpCat.{u} R A 2 := rfl
  have hOriginal : (show H.obj B.fst ⟶ Hrel.obj B from
      LoopCellAttachment.absoluteToRelativeHomologyTwo X x P) =
        singularHomologyPairQuotientMap AddCommGrpCat.{u} R B 2 :=
    (LoopCellAttachment.absoluteToRelativeHomologyTwo_eq_int_projection X x P).trans
      (singularHomologyIntData_toRelative_natAgreement AddCommGrpCat.{u} R 2 B)
  have hNat : singularHomologyPairQuotientMap AddCommGrpCat.{u} R A 2 ≫ Hrel.map f =
      H.map (TopPair.Hom.fst f) ≫
        singularHomologyPairQuotientMap AddCommGrpCat.{u} R B 2 :=
    singularHomologyPairQuotientMap_naturality AddCommGrpCat.{u} R 2 f
  exact (congrArg (fun q : H.obj A.fst ⟶ Hrel.obj A => q ≫ Hrel.map f) hLifted).trans
    (hNat.trans (congrArg (fun q : H.obj B.fst ⟶ Hrel.obj B =>
      H.map (TopPair.Hom.fst f) ≫ q) hOriginal.symm))

private theorem originalSphericalGenerator_value
    (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] (p : P)
    (a : coefficients.{u}) :
    (classicalCellBoundaryHomologyTwoGenerator.{u} ≫
      homologyTwo.map (originalSphericalGenerator X x P p) ≫
        LoopCellAttachment.absoluteToRelativeHomologyTwo X x P) a =
      LoopCellAttachment.relativeGenerator X x P coefficients p a := by
  let R : AddCommGrpCat.{u} := coefficients
  let A : TopPair.{u} := liftedPair X x P
  let B : TopPair.{u} := LoopCellAttachment.relativePair X x P
  let H : TopCat.{u} ⥤ AddCommGrpCat.{u} :=
    (singularHomologyFunctor AddCommGrpCat.{u} 2).obj R
  let Hrel : TopPair.{u} ⥤ AddCommGrpCat.{u} :=
    relativeSingularHomologyFunctor AddCommGrpCat.{u} R 2
  let f : A ⟶ B := liftedPairToOriginal X x P
  let d : A.fst ⟶ LoopCellAttachment.space X x P :=
    TopPair.Hom.fst f
  let q : H.obj A.fst ⟶ Hrel.obj A := liftedPairQuotient X x P
  let r : Hrel.obj A ⟶ Hrel.obj B := Hrel.map f
  let qOriginal : H.obj (LoopCellAttachment.space X x P) ⟶ Hrel.obj B :=
    LoopCellAttachment.absoluteToRelativeHomologyTwo X x P
  let S : (classicalCellDiskPair.{u} 3).snd ⟶ A.fst :=
    liftedSphericalGenerator X x P p
  let g : R ⟶ H.obj (classicalCellDiskPair.{u} 3).snd :=
    classicalCellBoundaryHomologyTwoGenerator.{u}
  let z : H.obj A.fst := (g ≫ H.map S) a
  have hMap : H.map (originalSphericalGenerator X x P p) = H.map S ≫ H.map d := by
    have hDefinition : originalSphericalGenerator X x P p = S ≫ d := rfl
    exact (congrArg H.map hDefinition).trans (H.map_comp S d)
  have hLeft : (g ≫ H.map (originalSphericalGenerator X x P p) ≫ qOriginal) a =
      qOriginal (H.map d z) := by
    have hWhole : g ≫ H.map (originalSphericalGenerator X x P p) ≫ qOriginal =
        (g ≫ H.map S) ≫ (H.map d ≫ qOriginal) := by
      exact (congrArg (fun t => g ≫ t ≫ qOriginal) hMap).trans
        ((congrArg (fun t => g ≫ t) (Category.assoc (H.map S) (H.map d) qOriginal)).trans
          (Category.assoc g (H.map S) (H.map d ≫ qOriginal)).symm)
    exact ConcreteCategory.congr_hom hWhole a
  have hNat : r (q z) = qOriginal (H.map d z) :=
    ConcreteCategory.congr_hom (liftedPairQuotient_naturality_down X x P) z
  have hSphere : z = a.down • liftedAbsoluteGenerator X x P p :=
    liftedSphericalGenerator_homology X x P p a
  have hPreimage := liftedAbsoluteGenerator_projection X x P p
  have hGenerator := ConcreteCategory.congr_hom (liftedRelativeGenerator_down X x P p)
    (ULift.up (1 : ℤ))
  have hCoefficient : a = a.down • (ULift.up (1 : ℤ) : coefficients.{u}) := by
    apply ULift.down_injective
    simp
  calc
    (g ≫ H.map (originalSphericalGenerator X x P p) ≫ qOriginal) a =
        qOriginal (H.map d z) := hLeft
    _ = r (q z) := hNat.symm
    _ = r (q (a.down • liftedAbsoluteGenerator X x P p)) :=
      congrArg (fun b => r (q b)) hSphere
    _ = a.down • r (q (liftedAbsoluteGenerator X x P p)) := by
      exact (congrArg r (q.hom.map_zsmul a.down (liftedAbsoluteGenerator X x P p))).trans
        (r.hom.map_zsmul a.down (q (liftedAbsoluteGenerator X x P p)))
    _ = a.down • r (liftedRelativeGenerator X x P p (ULift.up (1 : ℤ))) :=
      congrArg (fun b => a.down • r b) hPreimage
    _ = a.down • LoopCellAttachment.relativeGenerator X x P coefficients p (ULift.up (1 : ℤ)) :=
      congrArg (fun b => a.down • b) hGenerator
    _ = LoopCellAttachment.relativeGenerator X x P coefficients p a := by
      exact ((LoopCellAttachment.relativeGenerator X x P coefficients p).hom.map_zsmul
        a.down (ULift.up (1 : ℤ))).symm.trans
          (congrArg (LoopCellAttachment.relativeGenerator X x P coefficients p) hCoefficient.symm)

private theorem originalSphericalGenerator_homology
    (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] (p : P) :
    classicalCellBoundaryHomologyTwoGenerator.{u} ≫
        homologyTwo.map (originalSphericalGenerator X x P p) ≫
          LoopCellAttachment.absoluteToRelativeHomologyTwo X x P =
      LoopCellAttachment.relativeGenerator X x P coefficients p := by
  apply AddCommGrpCat.ext
  intro a
  exact originalSphericalGenerator_value X x P p a

private theorem exists_originalSphericalGenerators
    (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    ∃ h : ∀ _p : P, (classicalCellDiskPair.{u} 3).snd ⟶ LoopCellAttachment.space X x P,
      ∀ p : P, classicalCellBoundaryHomologyTwoGenerator.{u} ≫ homologyTwo.map (h p) ≫
        LoopCellAttachment.absoluteToRelativeHomologyTwo X x P =
          LoopCellAttachment.relativeGenerator X x P coefficients p :=
  ⟨originalSphericalGenerator X x P, originalSphericalGenerator_homology X x P⟩

end OriginalSphericalNativePullback

namespace OriginalSphericalNativePullback

private theorem joinedSaturated_isClosedCW
    {X : Type u} [TopologicalSpace X] [T2Space X] [CWComplex (Set.univ : Set X)]
    (s : Set X) (hs : ∀ a b : X, Joined a b → (a ∈ s ↔ b ∈ s)) : IsClosed s := by
  apply (CWComplex.closed (Set.univ : Set X) s (Set.subset_univ s)).2
  intro n i
  let C : Set X := CWComplex.closedCell (C := (Set.univ : Set X)) n i
  have hC : IsPathConnected C :=
    (Metric.isPathConnected_closedBall (x := (0 : Fin n → ℝ)) (r := 1) (by positivity)).image'
      (Topology.CWComplex.continuousOn (C := (Set.univ : Set X)) n i)
  by_cases h : (s ∩ C).Nonempty
  · obtain ⟨a, ha⟩ := h
    have hSub : C ⊆ s := by
      intro b hb
      exact (hs a b (hC.joinedIn a ha.2 b hb).joined).mp ha.1
    rw [Set.inter_eq_right.mpr hSub]
    exact CWComplex.isClosed_closedCell
  · rw [Set.not_nonempty_iff_eq_empty.mp h]
    exact isClosed_empty

private theorem connectedClassicalCW_pathConnected
    (X : TopCat.{u}) [T2Space X] [ConnectedSpace X]
    [CWComplex (Set.univ : Set X)] (x : X) : PathConnectedSpace X := by
  let s : Set X := {z | Joined x z}
  have hs : ∀ a b : X, Joined a b → (a ∈ s ↔ b ∈ s) := by
    intro a b hab
    exact ⟨fun hxa => hxa.trans hab, fun hxb => hxb.trans hab.symm⟩
  have hClosed : IsClosed s := joinedSaturated_isClosedCW s hs
  have hCompl : IsClosed sᶜ := joinedSaturated_isClosedCW sᶜ (fun a b h => (hs a b h).not)
  have hClopen : IsClopen s := ⟨hClosed, isClosed_compl_iff.mp hCompl⟩
  have hAll : s = Set.univ := hClopen.eq_univ ⟨x, Joined.refl x⟩
  apply pathConnectedSpace_iff_eq.mpr
  exact ⟨x, hAll⟩

private theorem exists_originalSphericalGenerators_of_connectedCW
    (X : TopCat.{u}) [T2Space X] [ConnectedSpace X]
    [CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    ∃ h : ∀ _p : P,
        (classicalCellDiskPair.{u} 3).snd ⟶ AlgebraicTopology.LoopCellAttachment.space X x P,
      ∀ p : P, classicalCellBoundaryHomologyTwoGenerator.{u} ≫ homologyTwo.map (h p) ≫
        AlgebraicTopology.LoopCellAttachment.absoluteToRelativeHomologyTwo X x P =
          AlgebraicTopology.LoopCellAttachment.relativeGenerator X x P coefficients p := by
  let : PathConnectedSpace X := connectedClassicalCW_pathConnected X x
  exact exists_originalSphericalGenerators X x P

end OriginalSphericalNativePullback

public section

namespace AlgebraicTopology.LoopCellSphericalGenerators

attribute [local instance] TopCat.toSSet_obj_kanComplex

/-- The singular map of the original subgroup-indexed two-cell inclusion. -/
abbrev nativeInclusion (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    TopCat.toSSet.obj X ⟶ TopCat.toSSet.obj (LoopCellAttachment.space X x P) :=
  TopCat.toSSet.map (LoopCellAttachment.inclusion X x P)

/-- The original point as a vertex of the singular simplicial set. -/
abbrev nativeBasePoint (X : TopCat.{u}) (x : X) : (TopCat.toSSet.obj X) _⦋0⦌ :=
  TopCat.toSSetObj₀Equiv.symm x

/-- The actual image vertex of the original singular inclusion. -/
abbrev nativeTargetPoint (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    (TopCat.toSSet.obj (LoopCellAttachment.space X x P)) _⦋0⦌ :=
  (nativeInclusion X x P).app (Opposite.op ⦋0⦌) (nativeBasePoint X x)

/-- The existing native cover of the original singular two-cell target. -/
abbrev nativeCover (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) : SSet.{u} :=
  SSet.KanComplex.nativeCover (TopCat.toSSet.obj (LoopCellAttachment.space X x P))
    (nativeTargetPoint X x P)

/-- The literal pullback of that cover along the original singular inclusion. -/
abbrev nativePullback (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) : SSet.{u} :=
  pullback (nativeInclusion X x P)
    (SSet.KanComplex.nativeCoverProjection
      (TopCat.toSSet.obj (LoopCellAttachment.space X x P)) (nativeTargetPoint X x P))

/-- The actual first projection to the original singular space. -/
abbrev nativePullbackProjection (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) : nativePullback X x P ⟶ TopCat.toSSet.obj X :=
  pullback.fst (nativeInclusion X x P)
    (SSet.KanComplex.nativeCoverProjection
      (TopCat.toSSet.obj (LoopCellAttachment.space X x P)) (nativeTargetPoint X x P))

/-- The actual second projection to the same native target cover. -/
abbrev nativePullbackToCover (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) : nativePullback X x P ⟶ nativeCover X x P :=
  pullback.snd (nativeInclusion X x P)
    (SSet.KanComplex.nativeCoverProjection
      (TopCat.toSSet.obj (LoopCellAttachment.space X x P)) (nativeTargetPoint X x P))

/-- The pullback vertex over the original point and the identity cover vertex. -/
@[expose]
def nativePullbackPoint (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) : (nativePullback X x P) _⦋0⦌ :=
  SSet.yonedaEquiv (pullback.lift (SSet.const (nativeBasePoint X x))
    (SSet.const (SSet.KanComplex.nativeCoverIdentityPoint
      (TopCat.toSSet.obj (LoopCellAttachment.space X x P)) (nativeTargetPoint X x P)))
    (by simp only [SSet.const_comp, SSet.KanComplex.nativeCoverProjection_identityPoint]))

/-- The computed native pullback is Kan; no Kan witness is supplied by a caller. -/
theorem nativePullback_kan (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) : SSet.KanComplex (nativePullback X x P) := by
  exact OriginalSphericalNativePullback.kan
    (nativeInclusion X x P) (nativeBasePoint X x)

/-- The computed point projects to the original singular base vertex. -/
theorem nativePullbackPoint_projection (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    (nativePullbackProjection X x P).app _ (nativePullbackPoint X x P) =
      nativeBasePoint X x := by
  exact OriginalSphericalNativePullback.point_source
    (nativeInclusion X x P) (nativeBasePoint X x)

/-- The actual pullback fundamental group is the original normal subgroup. -/
def nativePullbackPiOneEquiv (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    letI := nativePullback_kan X x P
    SSet.KanComplex.π 1 (nativePullback X x P) (nativePullbackPoint X x P) ≃* P := by
  letI := nativePullback_kan X x P
  exact OriginalSphericalNativePullback.actualPiOneSubgroupEquiv X x P

/-- This equivalence retains the actual original projection on every class. -/
theorem nativePullbackPiOneEquiv_value (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] :
    letI := nativePullback_kan X x P
    ∀ a : SSet.KanComplex.π 1 (nativePullback X x P) (nativePullbackPoint X x P),
      (nativePullbackPiOneEquiv X x P a).val =
        ((SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd (nativeBasePoint X x)).trans
          (TopCat.singularFundamentalGroupoidEndMulEquiv X x))
          (SSet.KanComplex.π.map (nativePullbackProjection X x P)
            (nativePullbackPoint_projection X x P) 1 a) := by
  let := nativePullback_kan X x P
  intro a
  exact OriginalSphericalNativePullback.actualPiOneSubgroupEquiv_value X x P a

/-- Perfectness gives zero first homology of the computed old cover. -/
theorem homologyOne_nativePullback_isZero (X : TopCat.{u}) [PathConnectedSpace X]
    (x : X) (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    IsZero (((singularHomologyFunctor AddCommGrpCat.{u} 1).obj
      (singularIntegralCoefficients : AddCommGrpCat.{u})).obj
        (SSet.toTop.obj (nativePullback X x P))) := by
  exact OriginalSphericalNativePullback.actualPullback_homologyOne_isZero X x P

/-- The actual realized old-cover inclusion is a closed embedding. -/
theorem realizedPullbackToCover_isClosedEmbedding (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    IsClosedEmbedding (SSet.toTop.map (nativePullbackToCover X x P)) := by
  exact OriginalSphericalNativePullback.realizedCoverProjection_closed X x P

/-- The original realized cover and its actual closed old-cover inclusion. -/
abbrev liftedPair (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) : TopPair.{u} :=
  TopPair.of (SSet.toTop.map (nativePullbackToCover X x P))
    (realizedPullbackToCover_isClosedEmbedding X x P).isEmbedding

/-- The matched simplex-boundary/classical-disk arrow isomorphism in every degree. -/
def diskBoundaryArrowIso (n : ℕ) :
    Arrow.mk (SSet.toTop.map (SSet.boundary.{u} n).ι) ≅
      Arrow.mk (classicalCellDiskPair.{u} n).map :=
  SSet.boundary.toClassicalCellDiskArrowIso n

/-- The original public Arrow API is the same neutral matched parametrization. -/
theorem diskBoundaryArrowIso_eq (n : ℕ) :
    diskBoundaryArrowIso.{u} n = SSet.boundary.toClassicalCellDiskArrowIso.{u} n := by
  rfl

/-- The computed native lift of the SAME original characteristic two-disk. -/
def nativeDiskLift (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) (p : P) :
    (Δ[2] : SSet.{u}) ⟶ nativeCover X x P :=
  OriginalSphericalNativePullback.liftedDiskSimplex X x P p

/-- The whole native disk projects to the adjoint of the original characteristic map. -/
theorem nativeDiskLift_projection (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) (p : P) :
    nativeDiskLift X x P p ≫ SSet.KanComplex.nativeCoverProjection
      (TopCat.toSSet.obj (LoopCellAttachment.space X x P)) (nativeTargetPoint X x P) =
      sSetTopAdj.homEquiv (Δ[2] : SSet.{u}) (LoopCellAttachment.space X x P)
        ((diskBoundaryArrowIso 2).hom.right ≫ LoopCellAttachment.cell X x P p) := by
  dsimp only [diskBoundaryArrowIso]
  rw [SSet.boundary.toClassicalCellDiskArrowIso_hom_right]
  exact OriginalSphericalNativePullback.liftedDiskSimplex_projection X x P p

/-- The actual boundary lift into the SAME original native pullback. -/
def nativeBoundaryLift (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) (p : P) :
    (SSet.boundary.{u} 2).toSSet ⟶ nativePullback X x P :=
  OriginalSphericalNativePullback.liftedBoundarySimplex X x P p

/-- The boundary lift projects to the adjoint of the SAME original attaching map. -/
theorem nativeBoundaryLift_source (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) (p : P) :
    nativeBoundaryLift X x P p ≫ nativePullbackProjection X x P =
      sSetTopAdj.homEquiv (SSet.boundary.{u} 2).toSSet X
        ((diskBoundaryArrowIso 2).hom.left ≫ LoopCellAttachment.attachingMap X x P p) := by
  dsimp only [diskBoundaryArrowIso]
  rw [SSet.boundary.toClassicalCellDiskArrowIso_hom_left]
  exact OriginalSphericalNativePullback.liftedBoundarySimplex_source X x P p

/-- The boundary lift into the cover is exactly the boundary of the SAME native disk lift. -/
theorem nativeBoundaryLift_toCover (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) (p : P) :
    nativeBoundaryLift X x P p ≫ nativePullbackToCover X x P =
      (SSet.boundary.{u} 2).ι ≫ nativeDiskLift X x P p := by
  exact OriginalSphericalNativePullback.liftedBoundarySimplex_cover X x P p

/-- The computed lift of the entire original characteristic disk pair. -/
def liftedCharacteristicDiskPair (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) (p : P) :
    classicalCellDiskPair.{u} 2 ⟶ liftedPair X x P :=
  OriginalSphericalNativePullback.liftedCharacteristicDiskPair X x P p

/-- Its disk component uses the SAME matched arrow isomorphism and native disk lift. -/
theorem liftedCharacteristicDiskPair_fst (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) (p : P) :
    TopPair.Hom.fst (liftedCharacteristicDiskPair X x P p) =
      (diskBoundaryArrowIso 2).inv.right ≫ SSet.toTop.map (nativeDiskLift X x P p) := by
  dsimp only [diskBoundaryArrowIso]
  rw [SSet.boundary.toClassicalCellDiskArrowIso_inv_right]
  rfl

/-- Its boundary component uses the SAME matched arrow isomorphism and boundary lift. -/
theorem liftedCharacteristicDiskPair_snd (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) (p : P) :
    TopPair.Hom.snd (liftedCharacteristicDiskPair X x P p) =
      (diskBoundaryArrowIso 2).inv.left ≫ SSet.toTop.map (nativeBoundaryLift X x P p) := by
  dsimp only [diskBoundaryArrowIso]
  rw [SSet.boundary.toClassicalCellDiskArrowIso_inv_left]
  rfl

/-- The actual two-component projection from the lifted pair to the original attachment pair. -/
def liftedPairToOriginal (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    liftedPair X x P ⟶ LoopCellAttachment.relativePair X x P :=
  OriginalSphericalNativePullback.liftedPairToOriginal X x P

/-- Its disk-space projection is the original native projection followed by the counit. -/
theorem liftedPairToOriginal_fst (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    TopPair.Hom.fst (liftedPairToOriginal X x P) =
      SSet.toTop.map (SSet.KanComplex.nativeCoverProjection
        (TopCat.toSSet.obj (LoopCellAttachment.space X x P)) (nativeTargetPoint X x P)) ≫
        sSetTopAdj.counit.app (LoopCellAttachment.space X x P) := by
  rfl

/-- Its old-space projection is the original pullback projection followed by the counit. -/
theorem liftedPairToOriginal_snd (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    TopPair.Hom.snd (liftedPairToOriginal X x P) =
      SSet.toTop.map (nativePullbackProjection X x P) ≫ sSetTopAdj.counit.app X := by
  rfl

/-- The lifted whole pair projects STRICTLY to the original `p`-indexed pair map. -/
theorem liftedCharacteristicDiskPair_down (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) (p : P) :
    liftedCharacteristicDiskPair X x P p ≫ liftedPairToOriginal X x P =
      LoopCellAttachment.cellPairMap X x P p := by
  exact OriginalSphericalNativePullback.liftedCharacteristicDiskPair_down X x P p

/-- The actual ordinary relative-chain quotient in degree two for the computed lifted pair. -/
abbrev relativeProjection (X : TopCat.{u}) (x : X)
    (P : Subgroup (FundamentalGroup X x)) :
    (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
      (singularIntegralCoefficients : AddCommGrpCat.{u})).obj (liftedPair X x P).fst) ⟶
      (relativeSingularHomologyFunctor AddCommGrpCat.{u}
        (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).obj (liftedPair X x P) :=
  singularHomologyPairQuotientMap AddCommGrpCat.{u}
    (singularIntegralCoefficients : AddCommGrpCat.{u}) (liftedPair X x P) 2

/-- Its epimorphism is derived from the actual old-cover H1 and the pair sequence. -/
theorem relativeProjection_epi (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    Epi (relativeProjection X x P) := by
  exact OriginalSphericalNativePullback.liftedPairQuotient_epi X x P

/-- The actual upstairs absolute preimage obtained from the proved quotient epimorphism. -/
def absoluteGenerator (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] (p : P) :
    (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
      (singularIntegralCoefficients : AddCommGrpCat.{u})).obj (liftedPair X x P).fst) :=
  OriginalSphericalNativePullback.liftedAbsoluteGenerator X x P p

/-- Its quotient is the original relative two-disk coordinate on the computed lifted pair map. -/
theorem absoluteGenerator_projection (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] (p : P) :
    relativeProjection X x P (absoluteGenerator X x P p) =
      ((classicalCellDiskPairRelativeHomologyIsoOfUnivLE.{u}
        (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).hom ≫
        (relativeSingularHomologyFunctor AddCommGrpCat.{u}
          (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).map
            (liftedCharacteristicDiskPair X x P p)) (ULift.up (1 : ℤ)) := by
  exact OriginalSphericalNativePullback.liftedAbsoluteGenerator_projection X x P p

/-- Pushing this preimage down gives the SAME original indexed relative generator. -/
theorem absoluteGenerator_down (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] (p : P) :
    (relativeSingularHomologyFunctor AddCommGrpCat.{u}
      (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).map (liftedPairToOriginal X x P)
        (relativeProjection X x P (absoluteGenerator X x P p)) =
      LoopCellAttachment.relativeGenerator X x P
        (singularIntegralCoefficients : AddCommGrpCat.{u}) p (ULift.up (1 : ℤ)) := by
  change OriginalSphericalNativePullback.relativeHomologyTwo.map
    (OriginalSphericalNativePullback.liftedPairToOriginal X x P)
      (OriginalSphericalNativePullback.liftedPairQuotient X x P
        (OriginalSphericalNativePullback.liftedAbsoluteGenerator X x P p)) = _
  rw [OriginalSphericalNativePullback.liftedAbsoluteGenerator_projection]
  exact ConcreteCategory.congr_hom
    (OriginalSphericalNativePullback.liftedRelativeGenerator_down X x P p) _

/-- The actual sphere map for the original indexed generator, computed through its cover. -/
def sphericalGenerator (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] (p : P) :
    (classicalCellDiskPair.{u} 3).snd ⟶ LoopCellAttachment.space X x P :=
  OriginalSphericalNativePullback.originalSphericalGenerator X x P p

/-- The same sphere has the fixed ORIGINAL three-disk boundary equation at every coefficient. -/
theorem sphericalGenerator_value (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (p : P) (a : (singularIntegralCoefficients : AddCommGrpCat.{u})) :
    (classicalCellBoundaryHomologyTwoGenerator.{u} ≫
      (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
        (singularIntegralCoefficients : AddCommGrpCat.{u})).map (sphericalGenerator X x P p)) ≫
      LoopCellAttachment.absoluteToRelativeHomologyTwo X x P) a =
      LoopCellAttachment.relativeGenerator X x P
        (singularIntegralCoefficients : AddCommGrpCat.{u}) p a := by
  exact OriginalSphericalNativePullback.originalSphericalGenerator_value X x P p a

/-- The whole original fixed-generator homology morphism is preserved by the computed sphere. -/
theorem sphericalGenerator_homology (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] (p : P) :
    classicalCellBoundaryHomologyTwoGenerator.{u} ≫
      (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
        (singularIntegralCoefficients : AddCommGrpCat.{u})).map (sphericalGenerator X x P p)) ≫
      LoopCellAttachment.absoluteToRelativeHomologyTwo X x P =
        LoopCellAttachment.relativeGenerator X x P
          (singularIntegralCoefficients : AddCommGrpCat.{u}) p := by
  exact OriginalSphericalNativePullback.originalSphericalGenerator_homology X x P p

set_option linter.unusedVariables false in
/-- Every indexed relative generator of the original connected Hausdorff classical CW attachment
has an actual sphere map with this fixed-generator equation. -/
theorem exists_sphericalGenerators_of_connectedCW (X : TopCat.{u}) [T2Space X]
    [ConnectedSpace X] [CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    ∃ h : ∀ p : P, (classicalCellDiskPair.{u} 3).snd ⟶ LoopCellAttachment.space X x P,
      ∀ p : P, classicalCellBoundaryHomologyTwoGenerator.{u} ≫
        (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
          (singularIntegralCoefficients : AddCommGrpCat.{u})).map (h p)) ≫
          LoopCellAttachment.absoluteToRelativeHomologyTwo X x P =
            LoopCellAttachment.relativeGenerator X x P
              (singularIntegralCoefficients : AddCommGrpCat.{u}) p := by
  exact OriginalSphericalNativePullback.exists_originalSphericalGenerators_of_connectedCW X x P

/-- The already chosen sphere in the SAME native covering space, before its original projection. -/
def liftedSphericalGenerator (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] (p : P) :
    (classicalCellDiskPair.{u} 3).snd ⟶ (liftedPair X x P).fst := by
  exact OriginalSphericalNativePullback.liftedSphericalGenerator X x P p

/-- The actual upstairs three-disk boundary is the SAME selected lifted two-disk class,
for every integral coefficient. -/
theorem liftedSphericalGenerator_value (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (p : P) (a : (singularIntegralCoefficients : AddCommGrpCat.{u})) :
    (classicalCellBoundaryHomologyTwoGenerator.{u} ≫
        (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
          (singularIntegralCoefficients : AddCommGrpCat.{u})).map
            (liftedSphericalGenerator X x P p)) ≫ relativeProjection X x P) a =
      ((classicalCellDiskPairRelativeHomologyIsoOfUnivLE.{u, u}
          (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).hom ≫
        (relativeSingularHomologyFunctor AddCommGrpCat.{u}
          (singularIntegralCoefficients : AddCommGrpCat.{u}) 2).map
            (liftedCharacteristicDiskPair X x P p)) a := by
  let R : AddCommGrpCat.{u} := singularIntegralCoefficients
  let A : TopPair.{u} := liftedPair X x P
  let H : TopCat.{u} ⥤ AddCommGrpCat.{u} := (singularHomologyFunctor AddCommGrpCat.{u} 2).obj R
  let Hrel : TopPair.{u} ⥤ AddCommGrpCat.{u} :=
    relativeSingularHomologyFunctor AddCommGrpCat.{u} R 2
  let S : (classicalCellDiskPair.{u} 3).snd ⟶ A.fst := liftedSphericalGenerator X x P p
  let q : H.obj A.fst ⟶ Hrel.obj A := relativeProjection X x P
  let g : R ⟶ H.obj (classicalCellDiskPair.{u} 3).snd :=
      classicalCellBoundaryHomologyTwoGenerator.{u}
  let r : R ⟶ Hrel.obj A :=
    (classicalCellDiskPairRelativeHomologyIsoOfUnivLE.{u, u} R 2).hom ≫
      Hrel.map (liftedCharacteristicDiskPair X x P p)
  let z : H.obj A.fst := (g ≫ H.map S) a
  have hLeft : (g ≫ H.map S ≫ q) a = q z :=
    ConcreteCategory.congr_hom (Category.assoc g (H.map S) q).symm a
  have hSphere : z = a.down • absoluteGenerator X x P p :=
    OriginalSphericalNativePullback.liftedSphericalGenerator_homology X x P p a
  have hPreimage : q (absoluteGenerator X x P p) = r (ULift.up (1 : ℤ)) :=
    absoluteGenerator_projection X x P p
  have hCoefficient : a = a.down • (ULift.up (1 : ℤ) : R) := by
    apply ULift.down_injective
    simp
  exact hLeft.trans
    ((congrArg q hSphere).trans
      ((q.hom.map_zsmul a.down (absoluteGenerator X x P p)).trans
        ((congrArg (fun b => a.down • b) hPreimage).trans
          ((r.hom.map_zsmul a.down (ULift.up (1 : ℤ))).symm.trans
            (congrArg r hCoefficient.symm)))))

/-- Projection of this SAME upstairs sphere is exactly the original chosen spherical generator. -/
theorem liftedSphericalGenerator_down (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] (p : P) :
    liftedSphericalGenerator X x P p ≫
        (SSet.toTop.map (SSet.KanComplex.nativeCoverProjection
          (TopCat.toSSet.obj (LoopCellAttachment.space X x P)) (nativeTargetPoint X x P)) ≫
            sSetTopAdj.counit.app (LoopCellAttachment.space X x P)) =
      sphericalGenerator X x P p := by
  rfl

/-- The absolute homology class of the SAME already chosen spherical generator. -/
def sphericalHomologyTwoClass (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] (p : P) :
    (singularIntegralCoefficients : AddCommGrpCat.{u}) ⟶
      (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
        (singularIntegralCoefficients : AddCommGrpCat.{u})).obj (LoopCellAttachment.space X x P)) :=
  classicalCellBoundaryHomologyTwoGenerator.{u} ≫
    (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
      (singularIntegralCoefficients : AddCommGrpCat.{u})).map (sphericalGenerator X x P p))

/-- The section formed from the actual chosen sphere classes, on all original cells. -/
def sphericalHomologyTwoSection (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    LoopCellAttachment.homologyTwoCells X x P ⟶
      (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
        (singularIntegralCoefficients : AddCommGrpCat.{u})).obj (LoopCellAttachment.space X x P)) :=
  Sigma.desc (fun p : P => sphericalHomologyTwoClass X x P p)

/-- Each summand of this section is the same original sphere's whole homology map. -/
theorem sphericalHomologyTwoSection_ι (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] (p : P) :
    Sigma.ι (fun _ : P => (singularIntegralCoefficients : AddCommGrpCat.{u})) p ≫
      sphericalHomologyTwoSection X x P = sphericalHomologyTwoClass X x P p := by
  exact Sigma.ι_comp_desc (fun q : P => sphericalHomologyTwoClass X x P q) p

/-- The actual sphere class has the original free-cell projection, without
identifying it with a previously chosen arbitrary absolute lift. -/
theorem sphericalHomologyTwoClass_projection (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] (p : P) :
    sphericalHomologyTwoClass X x P p ≫ LoopCellAttachment.homologyTwoProjection X x P =
      Sigma.ι (fun _ : P => (singularIntegralCoefficients : AddCommGrpCat.{u})) p := by
  let R : AddCommGrpCat.{u} := singularIntegralCoefficients
  let c := sphericalHomologyTwoClass X x P p
  let q := LoopCellAttachment.absoluteToRelativeHomologyTwo X x P
  let e := LoopCellAttachment.relativeHomologyTwoIso X x P R
  let j := Sigma.ι (fun _ : P => R) p
  let r := LoopCellAttachment.relativeGenerator X x P R p
  have hSphere : c ≫ q = r := sphericalGenerator_homology X x P p
  have hCell : j ≫ e.hom = r :=
    (congrArg (fun k => j ≫ k) (LoopCellAttachment.relativeGenerator_desc X x P R).symm).trans
      (Sigma.ι_comp_desc (fun p : P => LoopCellAttachment.relativeGenerator X x P R p) p)
  change c ≫ (q ≫ e.inv) = j
  exact (Category.assoc c q e.inv).symm.trans
    ((congrArg (fun k => k ≫ e.inv) hSphere).trans
      ((congrArg (fun k => k ≫ e.inv) hCell.symm).trans
        ((Category.assoc j e.hom e.inv).trans
          ((congrArg (fun k => j ≫ k) e.hom_inv_id).trans (Category.comp_id j)))))

/-- The SAME sphere coproduct is a strict section of the full original projection. -/
theorem sphericalHomologyTwoSection_projection (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    sphericalHomologyTwoSection X x P ≫ LoopCellAttachment.homologyTwoProjection X x P =
      𝟙 (LoopCellAttachment.homologyTwoCells X x P) := by
  apply Sigma.hom_ext
  intro p
  let j := Sigma.ι (fun _ : P => (singularIntegralCoefficients : AddCommGrpCat.{u})) p
  let s := sphericalHomologyTwoSection X x P
  let q := LoopCellAttachment.homologyTwoProjection X x P
  exact (Category.assoc j s q).symm.trans
    ((congrArg (fun k => k ≫ q) (sphericalHomologyTwoSection_ι X x P p)).trans
      ((sphericalHomologyTwoClass_projection X x P p).trans (Category.comp_id j).symm))

/-- The stock exact-sequence constructor keeps the exact sphere section and
computes its compatible original-space retraction. -/
def sphericalHomologyTwoSplitting (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    (LoopCellAttachment.homologyTwoShortComplex X x P).Splitting := by
  let S := LoopCellAttachment.homologyTwoShortComplex X x P
  let h := LoopCellAttachment.homologyTwoShortExact X x P
  exact ShortComplex.Splitting.ofExactOfSection S h.exact
    (sphericalHomologyTwoSection X x P) (sphericalHomologyTwoSection_projection X x P) h.mono_f

/-- The constructed splitting retains the SAME sphere section as data. -/
theorem sphericalHomologyTwoSplitting_section (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    (sphericalHomologyTwoSplitting X x P).s = sphericalHomologyTwoSection X x P := by
  rfl

/-- The original-space coordinate calculated for this same sphere section. -/
def sphericalHomologyTwoRetraction (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
      (singularIntegralCoefficients : AddCommGrpCat.{u})).obj (LoopCellAttachment.space X x P)) ⟶
        (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
          (singularIntegralCoefficients : AddCommGrpCat.{u})).obj X) :=
  (sphericalHomologyTwoSplitting X x P).r

/-- The actual H2 splitting whose added classes are these SAME sphere classes. -/
def sphericalHomologyTwoSplitIso (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
      (singularIntegralCoefficients : AddCommGrpCat.{u})).obj (LoopCellAttachment.space X x P)) ≅
        (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
          (singularIntegralCoefficients : AddCommGrpCat.{u})).obj X) ⊞
            LoopCellAttachment.homologyTwoCells X x P :=
  (sphericalHomologyTwoSplitting X x P).isoBinaryBiproduct

/-- The actual sphere section has zero old-space coordinate in this splitting. -/
theorem sphericalHomologyTwoSection_retraction (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    sphericalHomologyTwoSection X x P ≫ sphericalHomologyTwoRetraction X x P = 0 := by
  change (sphericalHomologyTwoSplitting X x P).s ≫ (sphericalHomologyTwoSplitting X x P).r = 0
  exact (sphericalHomologyTwoSplitting X x P).s_r

/-- The original H2 inclusion is unchanged and is a strict inverse of the new coordinate
retraction. -/
theorem inclusion_sphericalHomologyTwoRetraction (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
      (singularIntegralCoefficients : AddCommGrpCat.{u})).map
          (LoopCellAttachment.inclusion X x P)) ≫
        sphericalHomologyTwoRetraction X x P = 𝟙 _ := by
  exact (sphericalHomologyTwoSplitting X x P).f_r

/-- These two coordinates reconstruct every original absolute class. -/
theorem sphericalHomologyTwo_decomposition (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    sphericalHomologyTwoRetraction X x P ≫
        (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
          (singularIntegralCoefficients : AddCommGrpCat.{u})).map
              (LoopCellAttachment.inclusion X x P)) +
      LoopCellAttachment.homologyTwoProjection X x P ≫ sphericalHomologyTwoSection X x P = 𝟙 _ := by
  exact (sphericalHomologyTwoSplitting X x P).id

/-- The forward map contains the computed same-sphere retraction and unchanged projection. -/
theorem sphericalHomologyTwoSplitIso_hom (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    (sphericalHomologyTwoSplitIso X x P).hom =
      biprod.lift (sphericalHomologyTwoRetraction X x P)
          (LoopCellAttachment.homologyTwoProjection X x P) := by
  rfl

/-- The inverse uses the literal original inclusion and SAME selected sphere classes. -/
theorem sphericalHomologyTwoSplitIso_inv (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    (sphericalHomologyTwoSplitIso X x P).inv =
      biprod.desc
        (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
          (singularIntegralCoefficients : AddCommGrpCat.{u})).map
              (LoopCellAttachment.inclusion X x P))
        (sphericalHomologyTwoSection X x P) := by
  rfl

/-- The same-sphere coordinate maps are inverse on every original absolute class. -/
theorem sphericalHomologyTwoSplitIso_hom_inv (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    (sphericalHomologyTwoSplitIso X x P).hom ≫ (sphericalHomologyTwoSplitIso X x P).inv = 𝟙 _ :=
  (sphericalHomologyTwoSplitIso X x P).hom_inv_id

/-- They are inverse on both complete original-space/free-cell coordinates. -/
theorem sphericalHomologyTwoSplitIso_inv_hom (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    (sphericalHomologyTwoSplitIso X x P).inv ≫ (sphericalHomologyTwoSplitIso X x P).hom = 𝟙 _ :=
  (sphericalHomologyTwoSplitIso X x P).inv_hom_id

/-- The original H2 inclusion remains exactly the first summand. -/
theorem sphericalHomologyTwoSplitIso_inclusion (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
      (singularIntegralCoefficients : AddCommGrpCat.{u})).map
          (LoopCellAttachment.inclusion X x P)) ≫
        (sphericalHomologyTwoSplitIso X x P).hom = biprod.inl := by
  apply biprod.hom_ext
  · simp only [Category.assoc, sphericalHomologyTwoSplitIso_hom, biprod.lift_fst,
      inclusion_sphericalHomologyTwoRetraction, biprod.inl_fst]
  · simp only [Category.assoc, sphericalHomologyTwoSplitIso_hom, biprod.lift_snd,
      LoopCellAttachment.inclusion_comp_homologyTwoProjection, biprod.inl_snd]

/-- The second coordinate is still the whole original relative projection in its cell basis. -/
theorem sphericalHomologyTwoSplitIso_projection (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    (sphericalHomologyTwoSplitIso X x P).hom ≫ biprod.snd =
      LoopCellAttachment.homologyTwoProjection X x P := by
  rw [sphericalHomologyTwoSplitIso_hom, biprod.lift_snd]

/-- The section of SAME sphere classes is the full second summand. -/
theorem sphericalHomologyTwoSection_splitIso (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    sphericalHomologyTwoSection X x P ≫ (sphericalHomologyTwoSplitIso X x P).hom = biprod.inr := by
  apply biprod.hom_ext
  · simp only [Category.assoc, sphericalHomologyTwoSplitIso_hom, biprod.lift_fst,
      sphericalHomologyTwoSection_retraction, biprod.inr_fst]
  · simp only [Category.assoc, sphericalHomologyTwoSplitIso_hom, biprod.lift_snd,
      sphericalHomologyTwoSection_projection, biprod.inr_snd]

/-- The SAME chosen sphere represents the full absolute added class `(0,e_p)`
in the coherently chosen direct-sum splitting. -/
theorem sphericalGenerator_homologyTwoCoordinate (X : TopCat.{u}) [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] (p : P) :
    classicalCellBoundaryHomologyTwoGenerator.{u} ≫
        (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
          (singularIntegralCoefficients : AddCommGrpCat.{u})).map (sphericalGenerator X x P p)) ≫
      (sphericalHomologyTwoSplitIso X x P).hom =
        Sigma.ι (fun _ : P => (singularIntegralCoefficients : AddCommGrpCat.{u})) p ≫
            biprod.inr := by
  let j := Sigma.ι (fun _ : P => (singularIntegralCoefficients : AddCommGrpCat.{u})) p
  let s := sphericalHomologyTwoSection X x P
  let e := sphericalHomologyTwoSplitIso X x P
  change sphericalHomologyTwoClass X x P p ≫ e.hom = j ≫ biprod.inr
  exact (congrArg (fun k => k ≫ e.hom) (sphericalHomologyTwoSection_ι X x P p).symm).trans
    ((Category.assoc j s e.hom).trans
      (congrArg (fun k => j ≫ k) (sphericalHomologyTwoSection_splitIso X x P)))

/-- Both coordinates of every integral multiple of the SAME sphere class
are retained by the coherent splitting. -/
theorem sphericalGenerator_homologyTwoCoordinate_value (X : TopCat.{u})
    [PathConnectedSpace X] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P]
    (p : P) (a : (singularIntegralCoefficients : AddCommGrpCat.{u})) :
    (classicalCellBoundaryHomologyTwoGenerator.{u} ≫
        (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
          (singularIntegralCoefficients : AddCommGrpCat.{u})).map (sphericalGenerator X x P p)) ≫
      (sphericalHomologyTwoSplitIso X x P).hom) a =
        (Sigma.ι (fun _ : P => (singularIntegralCoefficients : AddCommGrpCat.{u})) p ≫
            biprod.inr) a :=
  ConcreteCategory.congr_hom (sphericalGenerator_homologyTwoCoordinate X x P p) a

set_option linter.unusedVariables false in
/-- The SAME sphere family and a coherent absolute splitting exist in the
original connected Hausdorff classical CW scope, with both summands calibrated. -/
theorem exists_sphericalGenerators_with_homologyTwoSplit_of_connectedCW
    (X : TopCat.{u}) [T2Space X] [ConnectedSpace X] [CWComplex (Set.univ : Set X)] (x : X)
    (P : Subgroup (FundamentalGroup X x)) [P.Normal] [Group.IsPerfect P] :
    ∃ (h : ∀ p : P, (classicalCellDiskPair.{u} 3).snd ⟶ LoopCellAttachment.space X x P)
      (e : (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
        (singularIntegralCoefficients : AddCommGrpCat.{u})).obj (LoopCellAttachment.space X x P)) ≅
          (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
            (singularIntegralCoefficients : AddCommGrpCat.{u})).obj X) ⊞
              LoopCellAttachment.homologyTwoCells X x P),
      (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
        (singularIntegralCoefficients : AddCommGrpCat.{u})).map
            (LoopCellAttachment.inclusion X x P)) ≫
          e.hom = biprod.inl ∧
      e.hom ≫ biprod.snd = LoopCellAttachment.homologyTwoProjection X x P ∧
      ∀ p : P, classicalCellBoundaryHomologyTwoGenerator.{u} ≫
        (((singularHomologyFunctor AddCommGrpCat.{u} 2).obj
          (singularIntegralCoefficients : AddCommGrpCat.{u})).map (h p)) ≫ e.hom =
        Sigma.ι (fun _ : P => (singularIntegralCoefficients : AddCommGrpCat.{u})) p ≫
            biprod.inr := by
  let : PathConnectedSpace X :=
      OriginalSphericalNativePullback.connectedClassicalCW_pathConnected X x
  refine ⟨sphericalGenerator X x P, sphericalHomologyTwoSplitIso X x P, ?_, ?_, ?_⟩
  · exact sphericalHomologyTwoSplitIso_inclusion X x P
  · exact sphericalHomologyTwoSplitIso_projection X x P
  · exact sphericalGenerator_homologyTwoCoordinate X x P

end AlgebraicTopology.LoopCellSphericalGenerators


end
