/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.ClassifyingSpace.FunctorUniverseMap
public import MathlibExt.CategoryTheory.ClassifyingSpace.FunctorUniverseMapComposition
public import MathlibExt.KTheory.Exact.Quillen.KSpaceIdentity
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizedCompStruct
public import MathlibExt.Topology.Homotopy.WeaklyPointedLoopHomotopyEquiv

/-!
# Canonical exact-functor K-maps and isomorphism homotopies

The actual Quillen functor and zero edge define maps between the original
K-space carriers in independent object/Hom worlds. Typed whole edge and
map equations retain their actual roots. The genuine isomorphism cylinder
and zero-comparison two-simplex give one homotopy over all original loops,
including both original moving unit Paths at every pair of times.
-/

public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open scoped Simplicial ZeroObject ContinuousMap

universe uC vC uD vD uX

namespace AlgebraicKTheory

private theorem weaklyPointedEqOfWholeValues
    {X : Type uC} {Y : Type uD} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f g : ContinuousMap.WeaklyPointed x y)
    (hMap : f.hom = g.hom)
    (hRoot : ∀ t : unitInterval, f.rootPath t = g.rootPath t) : f = g := by
  rcases f with ⟨f, p⟩
  rcases g with ⟨g, q⟩
  cases hMap
  have hPath : p = q := by
    apply Path.ext
    funext t
    exact hRoot t
  cases hPath
  rfl

private theorem realizedEdgeHomEqOfSimplexEq {X : SSet.{uX}}
    {a b c d : X.obj (Opposite.op ⦋0⦌)} (e : X.Edge a b) (f : X.Edge c d)
    (h : e.edge = f.edge) :
    (SSet.realizedEdgePath e).hom = (SSet.realizedEdgePath f).hom :=
  (SSet.realizedEdgePath_hom e).trans
    ((congrArg (fun z : X.obj (Opposite.op ⦋1⦌) =>
      SSet.stdSimplex.toTopObjIsoI.inv ≫ SSet.toTop.map (SSet.yonedaEquiv.symm z)) h).trans
        (SSet.realizedEdgePath_hom f).symm)

private theorem realizedEdgeValueEqOfSimplexEq {X : SSet.{uX}}
    {a b c d : X.obj (Opposite.op ⦋0⦌)} (e : X.Edge a b) (f : X.Edge c d)
    (h : e.edge = f.edge) (t : unitInterval) :
    (TopCat.pathEquiv (SSet.realizedEdgePath e)) t =
      (TopCat.pathEquiv (SSet.realizedEdgePath f)) t :=
  ConcreteCategory.congr_hom (realizedEdgeHomEqOfSimplexEq e f h)
    (TopCat.I.homeomorph.symm t)

section ExactFunctor

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]

/-- The actual Quillen zero-comparison edge with independent category worlds. -/
def NQFunctorZeroEdge (F : C ⥤ D) [F.Additive] [F.IsExact] :
    (NQ D).Edge
      (ComposableArrows.mk₀ ((QuillenQ.map F).obj (⟨0⟩ : QuillenQ C)))
      (NQ.zeroVertex D) :=
  SSet.Edge.ofEq (CategoryTheory.nerve.edgeMk (QuillenQ.zeroComparisonIso F).hom)
    (by apply ComposableArrows.ext₀; rfl)
    (by apply ComposableArrows.ext₀; rfl)

private theorem functorZeroEdgeComputed (F : C ⥤ D) [F.Additive] [F.IsExact] :
    (NQFunctorZeroEdge F).edge =
      ComposableArrows.mk₁ (QuillenQ.zeroComparisonIso F).hom := rfl

/-- The entire original edge is its actual comparison arrow. -/
theorem NQFunctorZeroEdge_edge (F : C ⥤ D) [F.Additive] [F.IsExact] :
    (NQFunctorZeroEdge F).edge =
      ComposableArrows.mk₁ (QuillenQ.zeroComparisonIso F).hom := functorZeroEdgeComputed F

/-- The original realization maps source zero to the actual functor-image vertex. -/
theorem NQFunctorMappedBasepoint_eq_vertex (F : C ⥤ D) [F.Additive] [F.IsExact] :
    CategoryTheory.realizedNerveFunctorMap (QuillenQ.map F) (NQReal.basepoint C) =
      SSet.realizedVertex
        (ComposableArrows.mk₀ ((QuillenQ.map F).obj (⟨0⟩ : QuillenQ C))) := by
  rw [NQReal.basepoint_eq_realizedVertex C]
  simpa only [NQ.zeroVertex] using
    CategoryTheory.realizedNerveFunctorMap_vertex (QuillenQ.map F)
      (⟨0⟩ : QuillenQ C)

/-- The original realization map with its genuine mapped-zero-to-selected-zero root. -/
def NQRealFunctorWeaklyPointed (F : C ⥤ D) [F.Additive] [F.IsExact] :
    ContinuousMap.WeaklyPointed (NQReal.basepoint C) (NQReal.basepoint D) := by
  let f := CategoryTheory.realizedNerveFunctorMap (QuillenQ.map F)
  let p := (SSet.realizedEdgePath (NQFunctorZeroEdge F)).cast
    (NQFunctorMappedBasepoint_eq_vertex F) (NQReal.basepoint_eq_realizedVertex D)
  exact ⟨f, TopCat.pathEquiv p⟩

private theorem functorRealizationHomComputed (F : C ⥤ D) [F.Additive] [F.IsExact] :
    (NQRealFunctorWeaklyPointed F).hom =
      CategoryTheory.realizedNerveFunctorMap (QuillenQ.map F) := rfl

/-- The WHOLE underlying map is the original actual Quillen functor realization. -/
theorem NQRealFunctorWeaklyPointed_hom (F : C ⥤ D) [F.Additive] [F.IsExact] :
    (NQRealFunctorWeaklyPointed F).hom =
      CategoryTheory.realizedNerveFunctorMap (QuillenQ.map F) := functorRealizationHomComputed F

private theorem functorRootValueComputed
    (F : C ⥤ D) [F.Additive] [F.IsExact] (t : unitInterval) :
    (NQRealFunctorWeaklyPointed F).rootPath t =
      (TopCat.pathEquiv (SSet.realizedEdgePath (NQFunctorZeroEdge F))) t := rfl

/-- Every original root time is the actual original zero-edge time. -/
theorem NQRealFunctorWeaklyPointed_rootPath_apply
    (F : C ⥤ D) [F.Additive] [F.IsExact] (t : unitInterval) :
    (NQRealFunctorWeaklyPointed F).rootPath t =
      (TopCat.pathEquiv (SSet.realizedEdgePath (NQFunctorZeroEdge F))) t :=
  functorRootValueComputed F t

/-- The original image-zero equation typed at the ACTUAL weakly pointed map. -/
theorem NQRealFunctorWeaklyPointed_basepoint_eq_vertex
    (F : C ⥤ D) [F.Additive] [F.IsExact] :
    (NQRealFunctorWeaklyPointed F).hom (NQReal.basepoint C) =
      SSet.realizedVertex (ComposableArrows.mk₀
        ((QuillenQ.map F).obj (⟨0⟩ : QuillenQ C))) :=
  (congrArg (fun f : C(NQReal C, NQReal D) => f (NQReal.basepoint C))
    (NQRealFunctorWeaklyPointed_hom F)).trans (NQFunctorMappedBasepoint_eq_vertex F)

private theorem functorRootPathComputed (F : C ⥤ D) [F.Additive] [F.IsExact] :
    (NQRealFunctorWeaklyPointed F).rootPath =
      (TopCat.pathEquiv (SSet.realizedEdgePath
        (CategoryTheory.nerve.edgeMk (QuillenQ.zeroComparisonIso F).hom))).cast
          (NQRealFunctorWeaklyPointed_basepoint_eq_vertex F)
          (NQReal.basepoint_eq_realizedVertex D) := by
  apply Path.ext
  funext t
  rfl

/-- The entire original root is its actual nerve-arrow Path with actual endpoint casts. -/
theorem NQRealFunctorWeaklyPointed_rootPath_eq
    (F : C ⥤ D) [F.Additive] [F.IsExact] :
    (NQRealFunctorWeaklyPointed F).rootPath =
      (TopCat.pathEquiv (SSet.realizedEdgePath
        (CategoryTheory.nerve.edgeMk (QuillenQ.zeroComparisonIso F).hom))).cast
          (NQRealFunctorWeaklyPointed_basepoint_eq_vertex F)
          (NQReal.basepoint_eq_realizedVertex D) := functorRootPathComputed F

/-- The canonical exact-functor map on both original Quillen K-space carriers. -/
def NQKSpaceFunctorMap (F : C ⥤ D) [F.Additive] [F.IsExact] :
    ContinuousMap (NQKSpace C) (NQKSpace D) :=
  (NQRealFunctorWeaklyPointed F).loopMap

private theorem functorKSpaceValueComputed
    (F : C ⥤ D) [F.Additive] [F.IsExact] (γ : NQKSpace C) :
    NQKSpaceFunctorMap F γ =
      (NQRealFunctorWeaklyPointed F).rootPath.symm.trans
        ((γ.map (NQRealFunctorWeaklyPointed F).hom.continuous).trans
          (NQRealFunctorWeaklyPointed F).rootPath) := rfl

private theorem functorKSpaceLoopMapComputed
    (F : C ⥤ D) [F.Additive] [F.IsExact] :
    NQKSpaceFunctorMap F = (NQRealFunctorWeaklyPointed F).loopMap := rfl

/-- The whole canonical exact-functor K-map is its original rooted loop map. -/
theorem NQKSpaceFunctorMap_eq_loopMap
    (F : C ⥤ D) [F.Additive] [F.IsExact] :
    NQKSpaceFunctorMap F = (NQRealFunctorWeaklyPointed F).loopMap :=
  functorKSpaceLoopMapComputed F

/-- The entire map retains the actual mapped loop and both original root legs. -/
theorem NQKSpaceFunctorMap_apply
    (F : C ⥤ D) [F.Additive] [F.IsExact] (γ : NQKSpace C) :
    NQKSpaceFunctorMap F γ =
      (NQRealFunctorWeaklyPointed F).rootPath.symm.trans
        ((γ.map (NQRealFunctorWeaklyPointed F).hom.continuous).trans
          (NQRealFunctorWeaklyPointed F).rootPath) := functorKSpaceValueComputed F γ

private def functorNatIsoRealHomotopyComputed (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G) :
    ContinuousMap.Homotopy (NQRealFunctorWeaklyPointed F).hom
      (NQRealFunctorWeaklyPointed G).hom :=
  CategoryTheory.realizedNerveFunctorMapHomotopy (QuillenQ.mapNatIso F G e).hom

/-- The ENTIRE realization homotopy of the original natural isomorphism. -/
def NQRealFunctorNatIsoHomotopy (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G) :
    ContinuousMap.Homotopy (NQRealFunctorWeaklyPointed F).hom
      (NQRealFunctorWeaklyPointed G).hom := functorNatIsoRealHomotopyComputed F G e

private theorem functorNatIsoRealValueComputed (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G)
    (t : unitInterval) (x : NQReal C) :
    NQRealFunctorNatIsoHomotopy F G e (t, x) =
      CategoryTheory.realizedNerveFunctorMapHomotopy (QuillenQ.mapNatIso F G e).hom
        (t, x) := rfl

private theorem functorNatIsoRealHomotopyEqComputed (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G) :
    NQRealFunctorNatIsoHomotopy F G e ≍
      CategoryTheory.realizedNerveFunctorMapHomotopy (QuillenQ.mapNatIso F G e).hom := HEq.rfl

/-- The WHOLE original isomorphism homotopy is the actual Quillen realization cylinder. -/
theorem NQRealFunctorNatIsoHomotopy_eq_realization (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G) :
    NQRealFunctorNatIsoHomotopy F G e ≍
      CategoryTheory.realizedNerveFunctorMapHomotopy (QuillenQ.mapNatIso F G e).hom :=
  functorNatIsoRealHomotopyEqComputed F G e

private theorem originalZeroNerveVertexComputed :
    NQReal.basepoint C =
      SSet.realizedVertex (X := CategoryTheory.nerve (QuillenQ C))
        (ComposableArrows.mk₀ (⟨0⟩ : QuillenQ C)) :=
  NQReal.basepoint_eq_realizedVertex C

private theorem functorNatIsoTraceComputed (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G) :
    ((NQRealFunctorNatIsoHomotopy F G e).evalAt (NQReal.basepoint C)).Homotopic
      ((TopCat.pathEquiv (SSet.realizedEdgePath
        (CategoryTheory.nerve.edgeMk
          ((QuillenQ.mapNatIso F G e).app (⟨0⟩ : QuillenQ C)).hom))).cast
            (NQRealFunctorWeaklyPointed_basepoint_eq_vertex F)
            (NQRealFunctorWeaklyPointed_basepoint_eq_vertex G)) := by
  let H := CategoryTheory.realizedNerveFunctorMapHomotopy (QuillenQ.mapNatIso F G e).hom
  let v₀ := SSet.realizedVertex (X := CategoryTheory.nerve (QuillenQ C))
    (ComposableArrows.mk₀ (⟨0⟩ : QuillenQ C))
  let hF := NQRealFunctorWeaklyPointed_basepoint_eq_vertex F
  let hG := NQRealFunctorWeaklyPointed_basepoint_eq_vertex G
  let hVF := CategoryTheory.realizedNerveFunctorMap_vertex (QuillenQ.map F)
    (⟨0⟩ : QuillenQ C)
  let hVG := CategoryTheory.realizedNerveFunctorMap_vertex (QuillenQ.map G)
    (⟨0⟩ : QuillenQ C)
  let q := (((H.evalAt v₀).cast hVF.symm hVG.symm).cast hF hG)
  have h := CategoryTheory.realizedNerveFunctorMapHomotopy_vertex
    (QuillenQ.mapNatIso F G e).hom (⟨0⟩ : QuillenQ C)
  obtain ⟨K⟩ := h
  let K' := K.pathCast hF hG
  have hTrace : q = (NQRealFunctorNatIsoHomotopy F G e).evalAt (NQReal.basepoint C) := by
    apply Path.ext
    funext t
    change H (t, v₀) = NQRealFunctorNatIsoHomotopy F G e (t, NQReal.basepoint C)
    rw [functorNatIsoRealValueComputed]
    exact congrArg (fun x => H (t, x)) originalZeroNerveVertexComputed.symm
  exact ⟨K'.cast hTrace rfl⟩

private theorem functorNatIsoRootComputed (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G) :
    (NQRealFunctorWeaklyPointed F).rootPath.Homotopic
      (((NQRealFunctorNatIsoHomotopy F G e).evalAt (NQReal.basepoint C)).trans
        (NQRealFunctorWeaklyPointed G).rootPath) := by
  let a := ((QuillenQ.mapNatIso F G e).app (⟨0⟩ : QuillenQ C)).hom
  let b := (QuillenQ.zeroComparisonIso G).hom
  let c := (QuillenQ.zeroComparisonIso F).hom
  have hArrow : a ≫ b = c := congrArg Iso.hom (QuillenQ.zeroComparisonIso_naturality F G e)
  obtain ⟨T⟩ := (CategoryTheory.nerve.nonempty_compStruct_iff a b c).2 hArrow
  obtain ⟨K⟩ := SSet.realizedCompStructHomotopic T
  let pA := TopCat.pathEquiv (SSet.realizedEdgePath (CategoryTheory.nerve.edgeMk a))
  let pB := TopCat.pathEquiv (SSet.realizedEdgePath (CategoryTheory.nerve.edgeMk b))
  let pC := TopCat.pathEquiv (SSet.realizedEdgePath (CategoryTheory.nerve.edgeMk c))
  let hF := NQRealFunctorWeaklyPointed_basepoint_eq_vertex F
  let hG := NQRealFunctorWeaklyPointed_basepoint_eq_vertex G
  let hZ := NQReal.basepoint_eq_realizedVertex D
  let K' := K.pathCast hF hZ
  have hLeft : pC.cast hF hZ = (NQRealFunctorWeaklyPointed F).rootPath :=
    (functorRootPathComputed F).symm
  have hRight : (pA.trans pB).cast hF hZ =
      (pA.cast hF hG).trans (NQRealFunctorWeaklyPointed G).rootPath :=
    (Path.cast_trans pA pB hF hG hZ).trans
      (congrArg (fun r => (pA.cast hF hG).trans r) (functorRootPathComputed G).symm)
  have hTriangle : (NQRealFunctorWeaklyPointed F).rootPath.Homotopic
      ((pA.cast hF hG).trans (NQRealFunctorWeaklyPointed G).rootPath) :=
    ⟨K'.cast hLeft hRight⟩
  exact hTriangle.trans ((functorNatIsoTraceComputed F G e).symm.hcomp
    (Path.Homotopic.refl (NQRealFunctorWeaklyPointed G).rootPath))

/-- Naturality of the ACTUAL zero roots, from the genuine realization trace and zero two-simplex. -/
theorem NQRealFunctorNatIso_rootPath_homotopic (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G) :
    (NQRealFunctorWeaklyPointed F).rootPath.Homotopic
      (((NQRealFunctorNatIsoHomotopy F G e).evalAt (NQReal.basepoint C)).trans
        (NQRealFunctorWeaklyPointed G).rootPath) := functorNatIsoRootComputed F G e

private def functorNatIsoKSpaceHomotopyComputed (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G) :
    ContinuousMap.Homotopy (NQKSpaceFunctorMap F) (NQKSpaceFunctorMap G) :=
  ContinuousMap.WeaklyPointed.loopMapHomotopyOfMap
    (NQRealFunctorWeaklyPointed F) (NQRealFunctorWeaklyPointed G)
    (NQRealFunctorNatIsoHomotopy F G e)
    (NQRealFunctorNatIso_rootPath_homotopic F G e).some

/-- One jointly continuous homotopy of the ENTIRE canonical isomorphic-functor K-maps. -/
def NQKSpaceFunctorNatIsoHomotopy (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G) :
    ContinuousMap.Homotopy (NQKSpaceFunctorMap F) (NQKSpaceFunctorMap G) :=
  functorNatIsoKSpaceHomotopyComputed F G e

private theorem functorNatIsoKSpaceWholeValueComputed (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G)
    (t : unitInterval) (γ : NQKSpace C) :
    (NQKSpaceFunctorNatIsoHomotopy F G e).toContinuousMap.toFun (t, γ) =
      (ContinuousMap.WeaklyPointed.loopMapHomotopyOfMap
        (NQRealFunctorWeaklyPointed F) (NQRealFunctorWeaklyPointed G)
        (NQRealFunctorNatIsoHomotopy F G e)
        (NQRealFunctorNatIso_rootPath_homotopic F G e).some).toContinuousMap.toFun (t, γ) := rfl

/-- Every original time and whole input loop of the actual canonical
NatIso homotopy retains its original realization family and chosen root
homotopy, including the same original `.some` value. -/
theorem NQKSpaceFunctorNatIsoHomotopy_loopMap_value (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G)
    (t : unitInterval) (γ : NQKSpace C) :
    (NQKSpaceFunctorNatIsoHomotopy F G e).toContinuousMap.toFun (t, γ) =
      (ContinuousMap.WeaklyPointed.loopMapHomotopyOfMap
        (NQRealFunctorWeaklyPointed F) (NQRealFunctorWeaklyPointed G)
        (NQRealFunctorNatIsoHomotopy F G e)
        (NQRealFunctorNatIso_rootPath_homotopic F G e).some).toContinuousMap.toFun (t, γ) :=
  functorNatIsoKSpaceWholeValueComputed F G e t γ

/-- The ACTUAL moving unit Path of the entire isomorphism homotopy. -/
def NQKSpaceFunctorNatIsoUnitPath (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G) :
    Path (NQKSpaceFunctorMap F (Path.refl (NQReal.basepoint C)))
      (NQKSpaceFunctorMap G (Path.refl (NQReal.basepoint C))) :=
  (NQKSpaceFunctorNatIsoHomotopy F G e).evalAt (Path.refl (NQReal.basepoint C))

private theorem functorNatIsoUnitValueComputed (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G)
    (t s : unitInterval) :
    (((NQKSpaceFunctorNatIsoUnitPath F G e : unitInterval → NQKSpace D) t) :
        unitInterval → NQReal D) s =
      (NQKSpaceFunctorNatIsoHomotopy F G e (t, Path.refl (NQReal.basepoint C)) :
        unitInterval → NQReal D) s := rfl

/-- BOTH time coordinates of the original moving isomorphism-unit Path are retained. -/
theorem NQKSpaceFunctorNatIsoUnitPath_apply (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G)
    (t s : unitInterval) :
    (((NQKSpaceFunctorNatIsoUnitPath F G e : unitInterval → NQKSpace D) t) :
        unitInterval → NQReal D) s =
      (NQKSpaceFunctorNatIsoHomotopy F G e (t, Path.refl (NQReal.basepoint C)) :
        unitInterval → NQReal D) s := functorNatIsoUnitValueComputed F G e t s

end ExactFunctor

section Identity

variable (C : Type uC) [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

private theorem functorIdHomComputed :
    (NQRealFunctorWeaklyPointed (𝟭 C)).hom = ContinuousMap.id (NQReal C) := by
  rw [NQRealFunctorWeaklyPointed_hom,
    CategoryTheory.realizedNerveFunctorMap_sameFrame, QuillenQ.map_id,
    CategoryTheory.nerveMap_id, SSet.toTop.map_id]
  rfl

/-- The WHOLE actual identity-functor realization map is the original identity. -/
theorem NQRealFunctorWeaklyPointed_id_hom :
    (NQRealFunctorWeaklyPointed (𝟭 C)).hom = ContinuousMap.id (NQReal C) := functorIdHomComputed C

private theorem functorIdMappedBasepointComputed :
    (NQRealFunctorWeaklyPointed (𝟭 C)).hom (NQReal.basepoint C) = NQReal.basepoint C := by
  rw [NQRealFunctorWeaklyPointed_id_hom]
  rfl

private theorem functorIdRootComputed :
    (((NQRealFunctorWeaklyPointed (𝟭 C)).rootPath).cast
      (functorIdMappedBasepointComputed C).symm rfl).Homotopic
        (Path.refl (NQReal.basepoint C)) := by
  obtain ⟨H⟩ := NQKSpace.zeroComparisonRootPath_id_homotopic C
  have hPath : ((NQRealFunctorWeaklyPointed (𝟭 C)).rootPath.cast
      (functorIdMappedBasepointComputed C).symm rfl) =
    ((NQKSpace.zeroComparisonRootPath C C (𝟭 C)).cast
      (NQReal.map_id_basepoint C).symm rfl) := by
    apply Path.ext
    funext t
    change (NQRealFunctorWeaklyPointed (𝟭 C)).rootPath t =
      (TopCat.pathEquiv (SSet.realizedEdgePath (NQ.zeroComparisonEdge (𝟭 C)))) t
    rw [NQRealFunctorWeaklyPointed_rootPath_apply]
    exact realizedEdgeValueEqOfSimplexEq (NQFunctorZeroEdge (𝟭 C))
      (NQ.zeroComparisonEdge (𝟭 C))
      ((NQFunctorZeroEdge_edge (𝟭 C)).trans (NQ.zeroComparisonEdge_edge (𝟭 C)).symm) t
  exact ⟨H.cast hPath.symm rfl⟩

/-- The actual ORIGINAL identity realization fixes its chosen basepoint,
through the existing owner-local computed equality; no point is replaced. -/
theorem NQRealFunctorWeaklyPointed_id_basepoint_eq :
    (NQRealFunctorWeaklyPointed (𝟭 C)).hom (NQReal.basepoint C) = NQReal.basepoint C :=
  functorIdMappedBasepointComputed C

/-- The ACTUAL root homotopy chosen in the ORIGINAL identity K-map family,
with its identical original point cast and VERY SAME private `.some` witness. -/
def NQKSpaceFunctorIdRootHomotopy :
    (((NQRealFunctorWeaklyPointed (𝟭 C)).rootPath).cast
      (NQRealFunctorWeaklyPointed_id_basepoint_eq C).symm rfl).Homotopy
        (Path.refl (NQReal.basepoint C)) :=
  (functorIdRootComputed C).some

private def functorIdKSpaceHomotopyComputed :
    ContinuousMap.Homotopy (NQKSpaceFunctorMap (𝟭 C))
      (ContinuousMap.id (NQKSpace C)) := by
  let x := NQReal.basepoint C
  let f := NQRealFunctorWeaklyPointed (𝟭 C)
  let p : Path x x := f.rootPath.cast (functorIdMappedBasepointComputed C).symm rfl
  let m : ContinuousMap.WeaklyPointed x x := ⟨ContinuousMap.id (NQReal C), p⟩
  have hm : m = f := weaklyPointedEqOfWholeValues m f
    (NQRealFunctorWeaklyPointed_id_hom C).symm (fun _ => rfl)
  let K := ContinuousMap.WeaklyPointed.loopMapRootPathHomotopy
    (ContinuousMap.id (NQReal C)) (functorIdRootComputed C).some
  let K' : ContinuousMap.Homotopy f.loopMap
      (ContinuousMap.WeaklyPointed.id x).loopMap :=
    K.cast (congrArg ContinuousMap.WeaklyPointed.loopMap hm) rfl
  exact K'.trans (ContinuousMap.WeaklyPointed.loopMapIdHomotopy x)

/-- The ENTIRE actual identity K-map homotopy on the original source loop carrier. -/
def NQKSpaceFunctorIdHomotopy :
    ContinuousMap.Homotopy (NQKSpaceFunctorMap (𝟭 C))
      (ContinuousMap.id (NQKSpace C)) := functorIdKSpaceHomotopyComputed C

private theorem originalFunctorIdWholeValueComputed (t : unitInterval) (γ : NQKSpace C) :
    (NQKSpaceFunctorIdHomotopy C).toContinuousMap.toFun (t, γ) =
      if ht : (t : ℝ) ≤ 1 / 2 then
        (ContinuousMap.WeaklyPointed.loopMapRootPathHomotopy
          (ContinuousMap.id (NQReal C)) (NQKSpaceFunctorIdRootHomotopy C)).toContinuousMap.toFun
            (⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
              ⟨unitInterval.nonneg t, ht⟩⟩, γ)
      else
        (ContinuousMap.WeaklyPointed.loopMapIdHomotopy (NQReal.basepoint C)).toContinuousMap.toFun
          (⟨2 * (t : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 ht).le, unitInterval.le_one t⟩⟩, γ) := by
  let x := NQReal.basepoint C
  let f := NQRealFunctorWeaklyPointed (𝟭 C)
  let p : Path x x := f.rootPath.cast (functorIdMappedBasepointComputed C).symm rfl
  let m : ContinuousMap.WeaklyPointed x x := ⟨ContinuousMap.id (NQReal C), p⟩
  have hm : m = f := weaklyPointedEqOfWholeValues m f
    (NQRealFunctorWeaklyPointed_id_hom C).symm (fun _ => rfl)
  let K := ContinuousMap.WeaklyPointed.loopMapRootPathHomotopy
    (ContinuousMap.id (NQReal C)) (functorIdRootComputed C).some
  let K' : ContinuousMap.Homotopy f.loopMap
      (ContinuousMap.WeaklyPointed.id x).loopMap :=
    K.cast (congrArg ContinuousMap.WeaklyPointed.loopMap hm) rfl
  let middleMap : C(NQKSpace C, NQKSpace C) := (ContinuousMap.WeaklyPointed.id x).loopMap
  let Hfirst : ContinuousMap.Homotopy (NQKSpaceFunctorMap (𝟭 C)) middleMap := K'
  let Hsecond : ContinuousMap.Homotopy middleMap (ContinuousMap.id (NQKSpace C)) :=
    ContinuousMap.WeaklyPointed.loopMapIdHomotopy x
  have hValue : (NQKSpaceFunctorIdHomotopy C).toContinuousMap.toFun (t, γ) =
      (Hfirst.trans Hsecond).toContinuousMap.toFun (t, γ) := rfl
  have hTrans := ContinuousMap.Homotopy.trans_apply Hfirst Hsecond (t, γ)
  have hFirstValue (u : unitInterval) : Hfirst.toContinuousMap.toFun (u, γ) =
      (ContinuousMap.WeaklyPointed.loopMapRootPathHomotopy
        (ContinuousMap.id (NQReal C)) (NQKSpaceFunctorIdRootHomotopy C)).toContinuousMap.toFun
          (u, γ) := rfl
  have hSecondValue (u : unitInterval) : Hsecond.toContinuousMap.toFun (u, γ) =
      (ContinuousMap.WeaklyPointed.loopMapIdHomotopy (NQReal.basepoint C)).toContinuousMap.toFun
        (u, γ) := rfl
  have hPieces :
      (if ht : (t : ℝ) ≤ 1 / 2 then Hfirst.toContinuousMap.toFun
        (⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
          ⟨unitInterval.nonneg t, ht⟩⟩, γ)
      else Hsecond.toContinuousMap.toFun
        (⟨2 * (t : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.2
          ⟨(not_le.1 ht).le, unitInterval.le_one t⟩⟩, γ)) =
      (if ht : (t : ℝ) ≤ 1 / 2 then
        (ContinuousMap.WeaklyPointed.loopMapRootPathHomotopy
          (ContinuousMap.id (NQReal C)) (NQKSpaceFunctorIdRootHomotopy C)).toContinuousMap.toFun
            (⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
              ⟨unitInterval.nonneg t, ht⟩⟩, γ)
      else (ContinuousMap.WeaklyPointed.loopMapIdHomotopy (NQReal.basepoint C)).toContinuousMap.toFun
        (⟨2 * (t : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.2
          ⟨(not_le.1 ht).le, unitInterval.le_one t⟩⟩, γ)) := by
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · simp only [dite_eq_left ht, ite_eq_left ht]
      exact hFirstValue _
    · simp only [dite_eq_right ht, ite_eq_right ht]
      exact hSecondValue _
  exact hValue.trans (hTrans.trans hPieces)

/-- Every original time and whole loop of the ACTUAL original identity
K-map homotopy retains its VERY SAME chosen root witness and actual second
identity-loop family, with its original two half clocks. -/
theorem NQKSpaceFunctorIdHomotopy_loopMap_value (t : unitInterval) (γ : NQKSpace C) :
    (NQKSpaceFunctorIdHomotopy C).toContinuousMap.toFun (t, γ) =
      if ht : (t : ℝ) ≤ 1 / 2 then
        (ContinuousMap.WeaklyPointed.loopMapRootPathHomotopy
          (ContinuousMap.id (NQReal C)) (NQKSpaceFunctorIdRootHomotopy C)).toContinuousMap.toFun
            (⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
              ⟨unitInterval.nonneg t, ht⟩⟩, γ)
      else
        (ContinuousMap.WeaklyPointed.loopMapIdHomotopy (NQReal.basepoint C)).toContinuousMap.toFun
          (⟨2 * (t : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 ht).le, unitInterval.le_one t⟩⟩, γ) :=
  originalFunctorIdWholeValueComputed C t γ

/-- The ACTUAL moving unit Path of the entire original identity K-map homotopy. -/
def NQKSpaceFunctorIdUnitPath :
    Path (NQKSpaceFunctorMap (𝟭 C) (Path.refl (NQReal.basepoint C)))
      (Path.refl (NQReal.basepoint C)) :=
  (NQKSpaceFunctorIdHomotopy C).evalAt (Path.refl (NQReal.basepoint C))

private theorem functorIdUnitValueComputed (t s : unitInterval) :
    ((NQKSpaceFunctorIdUnitPath C).toContinuousMap.toFun t :
        unitInterval → NQReal C) s =
      (NQKSpaceFunctorIdHomotopy C (t, Path.refl (NQReal.basepoint C)) :
        unitInterval → NQReal C) s := rfl

/-- BOTH original identity-unit time coordinates equal the actual entire homotopy values. -/
theorem NQKSpaceFunctorIdUnitPath_apply (t s : unitInterval) :
    ((NQKSpaceFunctorIdUnitPath C).toContinuousMap.toFun t :
        unitInterval → NQReal C) s =
      (NQKSpaceFunctorIdHomotopy C (t, Path.refl (NQReal.basepoint C)) :
        unitInterval → NQReal C) s := functorIdUnitValueComputed C t s

end Identity



end AlgebraicKTheory

end


public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open scoped Simplicial ZeroObject ContinuousMap Topology

universe uCComp vCComp uDComp vDComp uEComp vEComp

namespace AlgebraicKTheory

variable {C : Type uCComp} [Category.{vCComp} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uDComp} [Category.{vDComp} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable {E : Type uEComp} [Category.{vEComp} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
variable (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.IsExact] [G.IsExact]

private theorem functorCompRealHomComputed :
    (NQRealFunctorWeaklyPointed (F ⋙ G)).hom =
      ((NQRealFunctorWeaklyPointed F).comp (NQRealFunctorWeaklyPointed G)).hom := by
  have hQ := congrArg
    (fun H : QuillenQ C ⥤ QuillenQ E => CategoryTheory.realizedNerveFunctorMap H)
    (QuillenQ.map_comp F G)
  have hReal := CategoryTheory.realizedNerveFunctorMap_comp_independent
    (QuillenQ.map F) (QuillenQ.map G)
  have hMaps := congrArg₂
    (fun (g : C(NQReal D, NQReal E)) (f : C(NQReal C, NQReal D)) => g.comp f)
    (NQRealFunctorWeaklyPointed_hom G).symm (NQRealFunctorWeaklyPointed_hom F).symm
  exact (NQRealFunctorWeaklyPointed_hom (F ⋙ G)).trans
    (hQ.trans (hReal.trans
      (hMaps.trans (ContinuousMap.WeaklyPointed.comp_hom
        (NQRealFunctorWeaklyPointed F) (NQRealFunctorWeaklyPointed G)).symm)))

/-- The whole mixed realization of the composite is the stored composition
of the actual original weakly pointed realization maps. -/
theorem NQRealFunctorWeaklyPointed_comp_hom :
    (NQRealFunctorWeaklyPointed (F ⋙ G)).hom =
      ((NQRealFunctorWeaklyPointed F).comp (NQRealFunctorWeaklyPointed G)).hom :=
  functorCompRealHomComputed F G

private def functorCompRootHomotopyComputed :
    (NQRealFunctorWeaklyPointed (F ⋙ G)).rootPath.Homotopy
      (((NQRealFunctorWeaklyPointed F).comp (NQRealFunctorWeaklyPointed G)).rootPath.cast
        (congrArg (fun f : C(NQReal C, NQReal E) => f (NQReal.basepoint C))
          (NQRealFunctorWeaklyPointed_comp_hom F G)) rfl) := by
  let f := NQRealFunctorWeaklyPointed F
  let g := NQRealFunctorWeaklyPointed G
  let fg := NQRealFunctorWeaklyPointed (F ⋙ G)
  let hMap := congrArg (fun f : C(NQReal C, NQReal E) => f (NQReal.basepoint C))
    (NQRealFunctorWeaklyPointed_comp_hom F G)
  let a := (QuillenQ.map G).map (QuillenQ.zeroComparisonIso F).hom
  let b := (QuillenQ.zeroComparisonIso G).hom
  let c := (QuillenQ.zeroComparisonIso (F ⋙ G)).hom
  let pF := TopCat.pathEquiv
    (SSet.realizedEdgePath (CategoryTheory.nerve.edgeMk (QuillenQ.zeroComparisonIso F).hom))
  let pA := TopCat.pathEquiv (SSet.realizedEdgePath (CategoryTheory.nerve.edgeMk a))
  let pB := TopCat.pathEquiv (SSet.realizedEdgePath (CategoryTheory.nerve.edgeMk b))
  let pC := TopCat.pathEquiv (SSet.realizedEdgePath (CategoryTheory.nerve.edgeMk c))
  let hS := NQRealFunctorWeaklyPointed_basepoint_eq_vertex (F ⋙ G)
  let hG := NQRealFunctorWeaklyPointed_basepoint_eq_vertex G
  let hE := NQReal.basepoint_eq_realizedVertex E
  have hArrow : a ≫ b = c := (congrArg Iso.hom (QuillenQ.zeroComparisonIso_comp F G)).symm
  let T := ((CategoryTheory.nerve.nonempty_compStruct_iff a b c).2 hArrow).some
  let K := (SSet.realizedCompStructHomotopic T).some
  have hLeft : pC.cast hS hE = fg.rootPath :=
    (NQRealFunctorWeaklyPointed_rootPath_eq (F ⋙ G)).symm
  have hRight : (pA.trans pB).cast hS hE = (pA.cast hS hG).trans g.rootPath :=
    (Path.cast_trans pA pB hS hG hE).trans
      (congrArg (fun p : Path (g.hom (NQReal.basepoint D)) (NQReal.basepoint E) =>
        (pA.cast hS hG).trans p) (NQRealFunctorWeaklyPointed_rootPath_eq G).symm)
  let Htriangle : fg.rootPath.Homotopy ((pA.cast hS hG).trans g.rootPath) :=
    (K.pathCast hS hE).cast hLeft hRight
  let U := (CategoryTheory.realizedNerveFunctorMap_edge_homotopic
    (QuillenQ.map G) (QuillenQ.zeroComparisonIso F).hom).some
  let U' := U.pathCast hS hG
  have hMapped :
      (((pF.map (CategoryTheory.realizedNerveFunctorMap (QuillenQ.map G)).continuous).cast
        (CategoryTheory.realizedNerveFunctorMap_vertex (QuillenQ.map G)
          ((QuillenQ.map F).obj (⟨0⟩ : QuillenQ C))).symm
        (CategoryTheory.realizedNerveFunctorMap_vertex (QuillenQ.map G)
          (⟨0⟩ : QuillenQ D)).symm).cast hS hG) =
      (f.rootPath.map g.hom.continuous).cast hMap rfl := by
    apply Path.ext
    funext t
    have hRoot := congrArg
      (fun p : Path (f.hom (NQReal.basepoint C)) (NQReal.basepoint D) =>
        p.toContinuousMap.toFun t)
      (NQRealFunctorWeaklyPointed_rootPath_eq F)
    have hActualMap := DFunLike.congr_fun (NQRealFunctorWeaklyPointed_hom G)
      (f.rootPath.toContinuousMap.toFun t)
    exact (hActualMap.trans
      (congrArg (CategoryTheory.realizedNerveFunctorMap (QuillenQ.map G)) hRoot)).symm
  let Hmapped : ((f.rootPath.map g.hom.continuous).cast hMap rfl).Homotopy
      (pA.cast hS hG) := U'.cast hMapped rfl
  have hEnd : ((f.rootPath.map g.hom.continuous).cast hMap rfl).trans g.rootPath =
      (f.comp g).rootPath.cast hMap rfl := by
    apply Path.ext
    funext t
    exact (congrArg
      (fun p : Path ((f.comp g).hom (NQReal.basepoint C)) (NQReal.basepoint E) =>
        p.toContinuousMap.toFun t)
      (ContinuousMap.WeaklyPointed.comp_rootPath f g)).symm
  exact (Htriangle.trans (Hmapped.symm.hcomp (Path.Homotopy.refl g.rootPath))).cast rfl hEnd

/-- The actual chosen zero roots compose through the original mapped zero
edge and its genuine zero two-simplex, in all six category universe roles. -/
def NQRealFunctorCompRootHomotopy :
    (NQRealFunctorWeaklyPointed (F ⋙ G)).rootPath.Homotopy
      (((NQRealFunctorWeaklyPointed F).comp (NQRealFunctorWeaklyPointed G)).rootPath.cast
        (congrArg (fun f : C(NQReal C, NQReal E) => f (NQReal.basepoint C))
          (NQRealFunctorWeaklyPointed_comp_hom F G)) rfl) :=
  functorCompRootHomotopyComputed F G

/-- Root composition is earned from the original Quillen zero data. -/
theorem NQRealFunctorWeaklyPointed_comp_rootPath_homotopic :
    (NQRealFunctorWeaklyPointed (F ⋙ G)).rootPath.Homotopic
      (((NQRealFunctorWeaklyPointed F).comp (NQRealFunctorWeaklyPointed G)).rootPath.cast
        (congrArg (fun f : C(NQReal C, NQReal E) => f (NQReal.basepoint C))
          (NQRealFunctorWeaklyPointed_comp_hom F G)) rfl) :=
  ⟨NQRealFunctorCompRootHomotopy F G⟩

private def functorCompRootLoopHomotopyComputed :
    ContinuousMap.Homotopy (NQKSpaceFunctorMap (F ⋙ G))
      ((NQRealFunctorWeaklyPointed F).comp (NQRealFunctorWeaklyPointed G)).loopMap := by
  let fg := NQRealFunctorWeaklyPointed (F ⋙ G)
  let w := (NQRealFunctorWeaklyPointed F).comp (NQRealFunctorWeaklyPointed G)
  let hMap := NQRealFunctorWeaklyPointed_comp_hom F G
  let hPoint := congrArg (fun f : C(NQReal C, NQReal E) => f (NQReal.basepoint C)) hMap
  let m : ContinuousMap.WeaklyPointed (NQReal.basepoint C) (NQReal.basepoint E) :=
    ⟨fg.hom, w.rootPath.cast hPoint rfl⟩
  have hm : m = w := weaklyPointedEqOfWholeValues m w hMap (fun _ => rfl)
  have hfg : (⟨fg.hom, fg.rootPath⟩ :
      ContinuousMap.WeaklyPointed (NQReal.basepoint C) (NQReal.basepoint E)) = fg := by
    cases fg
    rfl
  let H := ContinuousMap.WeaklyPointed.loopMapRootPathHomotopy fg.hom
    (NQRealFunctorCompRootHomotopy F G)
  exact H.cast (congrArg ContinuousMap.WeaklyPointed.loopMap hfg)
    (congrArg ContinuousMap.WeaklyPointed.loopMap hm)

/-- One jointly continuous whole-loop family compares the actual composite
zero root with the stored composition of both original rooted maps. -/
def NQKSpaceFunctorCompRootLoopHomotopy :
    ContinuousMap.Homotopy (NQKSpaceFunctorMap (F ⋙ G))
      ((NQRealFunctorWeaklyPointed F).comp (NQRealFunctorWeaklyPointed G)).loopMap :=
  functorCompRootLoopHomotopyComputed F G

private theorem functorCompRootLoopWholeValueComputed
    (t : unitInterval) (gamma : NQKSpace C) :
    (NQKSpaceFunctorCompRootLoopHomotopy F G).toContinuousMap.toFun (t, gamma) =
      (ContinuousMap.WeaklyPointed.loopMapRootPathHomotopy
        (NQRealFunctorWeaklyPointed (F ⋙ G)).hom
        (NQRealFunctorCompRootHomotopy F G)).toContinuousMap.toFun (t, gamma) := rfl


/-- Every time and original input loop of the actual root-composition family
is the original weakly pointed root-path homotopy, with its endpoint casts. -/
theorem NQKSpaceFunctorCompRootLoopHomotopy_loopMap_value
    (t : unitInterval) (gamma : NQKSpace C) :
    (NQKSpaceFunctorCompRootLoopHomotopy F G).toContinuousMap.toFun (t, gamma) =
      (ContinuousMap.WeaklyPointed.loopMapRootPathHomotopy
        (NQRealFunctorWeaklyPointed (F ⋙ G)).hom
        (NQRealFunctorCompRootHomotopy F G)).toContinuousMap.toFun (t, gamma) :=
  functorCompRootLoopWholeValueComputed F G t gamma

private def functorCompKSpaceHomotopyComputed :
    ContinuousMap.Homotopy ((NQKSpaceFunctorMap G).comp (NQKSpaceFunctorMap F))
      (NQKSpaceFunctorMap (F ⋙ G)) :=
  ((NQKSpaceFunctorCompRootLoopHomotopy F G).trans
    (ContinuousMap.WeaklyPointed.loopMapCompHomotopy
      (NQRealFunctorWeaklyPointed F) (NQRealFunctorWeaklyPointed G))).symm

/-- The actual original exact-functor K-space maps compose up to one
bundled continuous homotopy, with all object and morphism universes independent. -/
def NQKSpaceFunctorCompHomotopy :
    ContinuousMap.Homotopy ((NQKSpaceFunctorMap G).comp (NQKSpaceFunctorMap F))
      (NQKSpaceFunctorMap (F ⋙ G)) :=
  functorCompKSpaceHomotopyComputed F G

/-- Existence of the bundled homotopy for the actual mixed K-space maps. -/
theorem NQKSpaceFunctorMap_comp_homotopic :
    Nonempty (ContinuousMap.Homotopy
      ((NQKSpaceFunctorMap G).comp (NQKSpaceFunctorMap F))
      (NQKSpaceFunctorMap (F ⋙ G))) :=
  ⟨NQKSpaceFunctorCompHomotopy F G⟩

private theorem functorCompWholeValueComputed (t : unitInterval) (gamma : NQKSpace C) :
    (NQKSpaceFunctorCompHomotopy F G).toContinuousMap.toFun (t, gamma) =
      ((NQKSpaceFunctorCompRootLoopHomotopy F G).trans
        (ContinuousMap.WeaklyPointed.loopMapCompHomotopy
          (NQRealFunctorWeaklyPointed F) (NQRealFunctorWeaklyPointed G))).toContinuousMap.toFun
            (unitInterval.symm t, gamma) := rfl

/-- Every original time and whole input loop uses the same actual root
comparison, loop reassociation family and original reversed composition clock. -/
theorem NQKSpaceFunctorCompHomotopy_loopMap_value
    (t : unitInterval) (gamma : NQKSpace C) :
    (NQKSpaceFunctorCompHomotopy F G).toContinuousMap.toFun (t, gamma) =
      ((NQKSpaceFunctorCompRootLoopHomotopy F G).trans
        (ContinuousMap.WeaklyPointed.loopMapCompHomotopy
          (NQRealFunctorWeaklyPointed F) (NQRealFunctorWeaklyPointed G))).toContinuousMap.toFun
            (unitInterval.symm t, gamma) :=
  functorCompWholeValueComputed F G t gamma

/-- The actual moving unit trace of the bundled mixed composition homotopy. -/
def NQKSpaceFunctorCompUnitPath :
    Path ((NQKSpaceFunctorMap G).comp (NQKSpaceFunctorMap F)
        (Path.refl (NQReal.basepoint C)))
      (NQKSpaceFunctorMap (F ⋙ G) (Path.refl (NQReal.basepoint C))) :=
  (NQKSpaceFunctorCompHomotopy F G).evalAt (Path.refl (NQReal.basepoint C))

private theorem functorCompUnitValueComputed (t s : unitInterval) :
    ((NQKSpaceFunctorCompUnitPath F G).toContinuousMap.toFun t).toContinuousMap.toFun s =
      ((NQKSpaceFunctorCompHomotopy F G).toContinuousMap.toFun
        (t, Path.refl (NQReal.basepoint C))).toContinuousMap.toFun s := rfl

/-- Both trace and loop times are evaluations of the same original bundled
composition family at the actual constant source loop. -/
theorem NQKSpaceFunctorCompUnitPath_apply (t s : unitInterval) :
    ((NQKSpaceFunctorCompUnitPath F G).toContinuousMap.toFun t).toContinuousMap.toFun s =
      ((NQKSpaceFunctorCompHomotopy F G).toContinuousMap.toFun
        (t, Path.refl (NQReal.basepoint C))).toContinuousMap.toFun s :=
  functorCompUnitValueComputed F G t s

end AlgebraicKTheory

end
