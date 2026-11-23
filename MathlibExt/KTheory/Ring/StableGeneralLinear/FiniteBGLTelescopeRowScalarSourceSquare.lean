/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteBGLTelescopeRowScalarRootPath
public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteClassifyingSpaceTelescopeFundamentalGroup
public import MathlibExt.CategoryTheory.ClassifyingSpace.FunctorUniverseMap
public import MathlibExt.Topology.Homotopy.WeaklyPointedLoopHomotopyEquiv

/-!
# The actual mixed-ring row source square and original zero-root trace

The accepted scalar row natural isomorphism compares the two ORIGINAL
composite functors in the common projective target. Its realized homotopy
is a whole continuous family on the original telescope carrier. Its actual
component-edge trace and the original zero-root composition triangle retain
the chosen-zero routes. No source square, comparison or trace is an input.
-/

noncomputable section

open CategoryTheory
open scoped ContinuousMap Simplicial

universe uR uS

namespace AlgebraicKTheory.StableGL

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- The original telescope-to-row source followed by actual scalar extension
and proper zero restriction. -/
public abbrev finiteBGLTelescopeScalarRowSourceFunctor (f : R →+* S) :
    FiniteBGLTelescopeCategory R ⥤
      SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uR} S) :=
  finiteBGLTelescopeToRowZeroComponent R ⋙
    SInverseS.zeroComponentFunctor ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
      FGProjectiveCat.scalarExtension.{uR, uS, uR} f)

/-- The same coefficient telescope functor, original target row functor
and actual module-world transport. -/
public abbrev finiteBGLTelescopeScalarRowTargetFunctor (f : R →+* S) :
    FiniteBGLTelescopeCategory R ⥤
      SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uR} S) :=
  finiteBGLTelescopeScalarFunctor f ⋙ finiteBGLTelescopeToRowZeroComponent S ⋙
    SInverseS.zeroComponentFunctor ((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
      (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse)

/-- The actual source composite realized on the original ordinary telescope. -/
public def ordinaryFiniteBGLTelescopeRowScalarSourceMap (f : R →+* S) :
    C(ordinaryFiniteBGLTelescope R,
      SSet.toTop.obj (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uR} S)))) :=
  CategoryTheory.realizedNerveFunctorMap (finiteBGLTelescopeScalarRowSourceFunctor f)

/-- The actual target composite realized on that SAME original telescope. -/
public def ordinaryFiniteBGLTelescopeRowScalarTargetMap (f : R →+* S) :
    C(ordinaryFiniteBGLTelescope R,
      SSet.toTop.obj (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uR} S)))) :=
  CategoryTheory.realizedNerveFunctorMap (finiteBGLTelescopeScalarRowTargetFunctor f)

/-- The whole source square is derived from the actual scalar row natural isomorphism. -/
public def ordinaryFiniteBGLTelescopeRowScalarHomotopy (f : R →+* S) :
    ContinuousMap.Homotopy (ordinaryFiniteBGLTelescopeRowScalarSourceMap f)
      (ordinaryFiniteBGLTelescopeRowScalarTargetMap f) :=
  CategoryTheory.realizedNerveFunctorMapHomotopy (finiteBGLTelescopeRowScalarZeroIso f).hom

private theorem scalarRowSourceMapVertexComputed (f : R →+* S) :
    ordinaryFiniteBGLTelescopeRowScalarSourceMap f (ordinaryFiniteBGLTelescopeBasepoint R) =
      SSet.realizedVertex
        (X := nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uR} S)))
        ((nerveEquiv (C := SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uR} S))).symm
          ((finiteBGLTelescopeToRowZeroComponent R ⋙
            SInverseS.zeroComponentFunctor ((FGProjectiveCat.IdempotentModel.equivalence R).functor
                ⋙
              FGProjectiveCat.scalarExtension.{uR, uS, uR} f)).obj
            (finiteBGLTelescopeBaseObject R))) := by
  let Z := SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uR} S)
  let A := finiteBGLTelescopeScalarRowSourceFunctor f
  have hObject : A.obj (finiteBGLTelescopeBaseObject R) =
      (finiteBGLTelescopeToRowZeroComponent R ⋙
        SInverseS.zeroComponentFunctor ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
          FGProjectiveCat.scalarExtension.{uR, uS, uR} f)).obj
        (finiteBGLTelescopeBaseObject R) := by
    simp only [A, finiteBGLTelescopeScalarRowSourceFunctor, Functor.comp_obj]
  have hVertex : ordinaryFiniteBGLTelescopeRowScalarSourceMap f
      (ordinaryFiniteBGLTelescopeBasepoint R) =
        SSet.realizedVertex (X := nerve Z) (ComposableArrows.mk₀
          (A.obj (finiteBGLTelescopeBaseObject R))) := by
    change CategoryTheory.realizedNerveFunctorMap A
      (SSet.realizedVertex (X := nerve (FiniteBGLTelescopeCategory R))
        (ComposableArrows.mk₀ (finiteBGLTelescopeBaseObject R))) = _
    exact CategoryTheory.realizedNerveFunctorMap_vertex A (finiteBGLTelescopeBaseObject R)
  exact hVertex.trans (congrArg (fun x : Z =>
    SSet.realizedVertex (X := nerve Z) ((nerveEquiv (C := Z)).symm x)) hObject)

/-- The actual source map retains the original source-root vertex presentation. -/
public theorem ordinaryFiniteBGLTelescopeRowScalarSourceMap_original_vertex (f : R →+* S) :
    ordinaryFiniteBGLTelescopeRowScalarSourceMap f (ordinaryFiniteBGLTelescopeBasepoint R) =
      SSet.realizedVertex
        (X := nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uR} S)))
        ((nerveEquiv (C := SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uR} S))).symm
          ((finiteBGLTelescopeToRowZeroComponent R ⋙
            SInverseS.zeroComponentFunctor ((FGProjectiveCat.IdempotentModel.equivalence R).functor
                ⋙
              FGProjectiveCat.scalarExtension.{uR, uS, uR} f)).obj
            (finiteBGLTelescopeBaseObject R))) :=
  scalarRowSourceMapVertexComputed f

private theorem scalarRowTargetMapVertexComputed (f : R →+* S) :
    ordinaryFiniteBGLTelescopeRowScalarTargetMap f (ordinaryFiniteBGLTelescopeBasepoint R) =
      SSet.realizedVertex
        (X := nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uR} S)))
        ((nerveEquiv (C := SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uR} S))).symm
          (((finiteBGLTelescopeScalarFunctor f ⋙ finiteBGLTelescopeToRowZeroComponent S) ⋙
            SInverseS.zeroComponentFunctor ((FGProjectiveCat.IdempotentModel.equivalence S).functor
                ⋙
              (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse)).obj
            (finiteBGLTelescopeBaseObject R))) := by
  let Z := SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uR} S)
  let B := finiteBGLTelescopeScalarRowTargetFunctor f
  have hObject : B.obj (finiteBGLTelescopeBaseObject R) =
      ((finiteBGLTelescopeScalarFunctor f ⋙ finiteBGLTelescopeToRowZeroComponent S) ⋙
        SInverseS.zeroComponentFunctor ((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
          (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse)).obj
        (finiteBGLTelescopeBaseObject R) := by
    simp only [B, finiteBGLTelescopeScalarRowTargetFunctor, Functor.comp_obj]
  have hVertex : ordinaryFiniteBGLTelescopeRowScalarTargetMap f
      (ordinaryFiniteBGLTelescopeBasepoint R) =
        SSet.realizedVertex (X := nerve Z) (ComposableArrows.mk₀
          (B.obj (finiteBGLTelescopeBaseObject R))) := by
    change CategoryTheory.realizedNerveFunctorMap B
      (SSet.realizedVertex (X := nerve (FiniteBGLTelescopeCategory R))
        (ComposableArrows.mk₀ (finiteBGLTelescopeBaseObject R))) = _
    exact CategoryTheory.realizedNerveFunctorMap_vertex B (finiteBGLTelescopeBaseObject R)
  exact hVertex.trans (congrArg (fun x : Z =>
    SSet.realizedVertex (X := nerve Z) ((nerveEquiv (C := Z)).symm x)) hObject)

/-- The target map retains the actual associated target-root functor and its original vertex. -/
public theorem ordinaryFiniteBGLTelescopeRowScalarTargetMap_original_vertex (f : R →+* S) :
    ordinaryFiniteBGLTelescopeRowScalarTargetMap f (ordinaryFiniteBGLTelescopeBasepoint R) =
      SSet.realizedVertex
        (X := nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uR} S)))
        ((nerveEquiv (C := SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uR} S))).symm
          (((finiteBGLTelescopeScalarFunctor f ⋙ finiteBGLTelescopeToRowZeroComponent S) ⋙
            SInverseS.zeroComponentFunctor ((FGProjectiveCat.IdempotentModel.equivalence S).functor
                ⋙
              (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse)).obj
            (finiteBGLTelescopeBaseObject R))) :=
  scalarRowTargetMapVertexComputed f

/-- Its original vertex trace, followed by the actual target root, is the original source root
up to a path homotopy with endpoints fixed. -/
public theorem finiteBGLTelescopeRowScalarOriginalRootTrace (f : R →+* S) :
    (TopCat.pathEquiv (SSet.realizedEdgePath
      (nerve.edgeMk (finiteBGLTelescopeScalarSourceRootZeroIso f).hom))).Homotopic
      ((((ordinaryFiniteBGLTelescopeRowScalarHomotopy f).evalAt
          (ordinaryFiniteBGLTelescopeBasepoint R)).cast
        (ordinaryFiniteBGLTelescopeRowScalarSourceMap_original_vertex f).symm
        (ordinaryFiniteBGLTelescopeRowScalarTargetMap_original_vertex f).symm).trans
        (TopCat.pathEquiv (SSet.realizedEdgePath
          (nerve.edgeMk (finiteBGLTelescopeScalarTargetRootZeroIso f).hom)))) := by
  let A := finiteBGLTelescopeToRowZeroComponent R ⋙
    SInverseS.zeroComponentFunctor ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
      FGProjectiveCat.scalarExtension.{uR, uS, uR} f)
  let B := (finiteBGLTelescopeScalarFunctor f ⋙ finiteBGLTelescopeToRowZeroComponent S) ⋙
    SInverseS.zeroComponentFunctor ((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
      (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse)
  let alpha : A ⟶ B := (finiteBGLTelescopeRowScalarZeroIso f).hom
  let c := finiteBGLTelescopeBaseObject R
  let q := TopCat.pathEquiv (SSet.realizedEdgePath
    (nerve.edgeMk (finiteBGLTelescopeScalarTargetRootZeroIso f).hom))
  have hPath :
      (((ordinaryFiniteBGLTelescopeRowScalarHomotopy f).evalAt
          (ordinaryFiniteBGLTelescopeBasepoint R)).cast
        (ordinaryFiniteBGLTelescopeRowScalarSourceMap_original_vertex f).symm
        (ordinaryFiniteBGLTelescopeRowScalarTargetMap_original_vertex f).symm) =
      (((CategoryTheory.realizedNerveFunctorMapHomotopy alpha).evalAt
          (SSet.realizedVertex (X := nerve (FiniteBGLTelescopeCategory R))
            (ComposableArrows.mk₀ c))).cast
        (CategoryTheory.realizedNerveFunctorMap_vertex A c).symm
        (CategoryTheory.realizedNerveFunctorMap_vertex B c).symm) := by
    apply Path.ext
    funext t
    rfl
  have hTrace := CategoryTheory.realizedNerveFunctorMapHomotopy_vertex alpha c
  have hTrace' :
      (((ordinaryFiniteBGLTelescopeRowScalarHomotopy f).evalAt
          (ordinaryFiniteBGLTelescopeBasepoint R)).cast
        (ordinaryFiniteBGLTelescopeRowScalarSourceMap_original_vertex f).symm
        (ordinaryFiniteBGLTelescopeRowScalarTargetMap_original_vertex f).symm).Homotopic
        (TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk (alpha.app c)))) := by
    rw [hPath]
    exact hTrace
  have hConcat := hTrace'.hcomp (Path.Homotopic.refl q)
  have hRoot := finiteBGLTelescopeRowScalarZeroIso_original_root_path R S f
  exact hRoot.trans hConcat.symm

/-- The actual source composite with its original mapped rank-zero root. -/
public def ordinaryFiniteBGLTelescopeRowScalarSourceWeaklyPointed (f : R →+* S) :
    ContinuousMap.WeaklyPointed (ordinaryFiniteBGLTelescopeBasepoint R)
      (SSet.realizedVertex
        (X := nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uR} S)))
        (ComposableArrows.mk₀
          (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{max uS uR} S)))) where
  hom := ordinaryFiniteBGLTelescopeRowScalarSourceMap f
  rootPath := (TopCat.pathEquiv (SSet.realizedEdgePath
    (nerve.edgeMk (finiteBGLTelescopeScalarSourceRootZeroIso f).hom))).cast
      (ordinaryFiniteBGLTelescopeRowScalarSourceMap_original_vertex f) rfl

/-- The actual target composite with the same original target rank-zero root. -/
public def ordinaryFiniteBGLTelescopeRowScalarTargetWeaklyPointed (f : R →+* S) :
    ContinuousMap.WeaklyPointed (ordinaryFiniteBGLTelescopeBasepoint R)
      (SSet.realizedVertex
        (X := nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.{max uS uR} S)))
        (ComposableArrows.mk₀
          (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{max uS uR} S)))) where
  hom := ordinaryFiniteBGLTelescopeRowScalarTargetMap f
  rootPath := (TopCat.pathEquiv (SSet.realizedEdgePath
    (nerve.edgeMk (finiteBGLTelescopeScalarTargetRootZeroIso f).hom))).cast
      (ordinaryFiniteBGLTelescopeRowScalarTargetMap_original_vertex f) rfl

universe uPath

private theorem rowRootTraceEndpointCast
    {Y : Type uPath} [TopologicalSpace Y] {a a' b b' c : Y}
    (p : Path a b) (q : Path b' c) (ha : a = a') (hb : b = b') :
    ((p.cast ha.symm hb.symm).trans q).cast ha rfl = p.trans (q.cast hb rfl) := by
  cases ha
  cases hb
  rfl

private theorem rowScalarWeaklyPointedRootTrace (f : R →+* S) :
    (ordinaryFiniteBGLTelescopeRowScalarSourceWeaklyPointed f).rootPath.Homotopic
      (((ordinaryFiniteBGLTelescopeRowScalarHomotopy f).evalAt
          (ordinaryFiniteBGLTelescopeBasepoint R)).trans
        (ordinaryFiniteBGLTelescopeRowScalarTargetWeaklyPointed f).rootPath) := by
  let H := ordinaryFiniteBGLTelescopeRowScalarHomotopy f
  let c := ordinaryFiniteBGLTelescopeBasepoint R
  let p := TopCat.pathEquiv (SSet.realizedEdgePath
    (nerve.edgeMk (finiteBGLTelescopeScalarSourceRootZeroIso f).hom))
  let q := TopCat.pathEquiv (SSet.realizedEdgePath
    (nerve.edgeMk (finiteBGLTelescopeScalarTargetRootZeroIso f).hom))
  let ha := ordinaryFiniteBGLTelescopeRowScalarSourceMap_original_vertex f
  let hb := ordinaryFiniteBGLTelescopeRowScalarTargetMap_original_vertex f
  change (p.cast ha rfl).Homotopic ((H.evalAt c).trans (q.cast hb rfl))
  have h := (finiteBGLTelescopeRowScalarOriginalRootTrace f).pathCast ha rfl
  have he := rowRootTraceEndpointCast (H.evalAt c) q ha hb
  rw [he] at h
  exact h

/-- The original scalar row maps induce one whole continuous loop-map homotopy,
using their genuine original root trace and the existing ordinary-homotopy construction. -/
public def ordinaryFiniteBGLTelescopeRowScalarLoopHomotopy (f : R →+* S) :
    ContinuousMap.Homotopy
      (ordinaryFiniteBGLTelescopeRowScalarSourceWeaklyPointed f).loopMap
      (ordinaryFiniteBGLTelescopeRowScalarTargetWeaklyPointed f).loopMap :=
  ContinuousMap.WeaklyPointed.loopMapHomotopyOfMap
    (ordinaryFiniteBGLTelescopeRowScalarSourceWeaklyPointed f)
    (ordinaryFiniteBGLTelescopeRowScalarTargetWeaklyPointed f)
    (ordinaryFiniteBGLTelescopeRowScalarHomotopy f)
    (rowScalarWeaklyPointedRootTrace f).some

end AlgebraicKTheory.StableGL

end


noncomputable section

universe uR uS

namespace AlgebraicKTheory.StableGL

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

private theorem originalScalarRowSourceMapValueComputed (f : R →+* S) :
    ordinaryFiniteBGLTelescopeRowScalarSourceMap f =
      CategoryTheory.realizedNerveFunctorMap (finiteBGLTelescopeScalarRowSourceFunctor f) := by
  rfl

/-- The entire ORIGINAL scalar row source map realizes the same actual source functor. -/
public theorem ordinaryFiniteBGLTelescopeRowScalarSourceMap_eq_realizedFunctorMap
    (f : R →+* S) :
    ordinaryFiniteBGLTelescopeRowScalarSourceMap f =
      CategoryTheory.realizedNerveFunctorMap (finiteBGLTelescopeScalarRowSourceFunctor f) :=
  originalScalarRowSourceMapValueComputed f

private theorem originalScalarRowTargetMapValueComputed (f : R →+* S) :
    ordinaryFiniteBGLTelescopeRowScalarTargetMap f =
      CategoryTheory.realizedNerveFunctorMap (finiteBGLTelescopeScalarRowTargetFunctor f) := by
  rfl

/-- The entire ORIGINAL scalar row target map realizes the same actual target functor. -/
public theorem ordinaryFiniteBGLTelescopeRowScalarTargetMap_eq_realizedFunctorMap
    (f : R →+* S) :
    ordinaryFiniteBGLTelescopeRowScalarTargetMap f =
      CategoryTheory.realizedNerveFunctorMap (finiteBGLTelescopeScalarRowTargetFunctor f) :=
  originalScalarRowTargetMapValueComputed f

end AlgebraicKTheory.StableGL

end


noncomputable section

open CategoryTheory
open scoped ContinuousMap Simplicial

attribute [local instance] CategoryTheory.uliftCategory

universe uR uS uA vA uB vB uE vE

namespace AlgebraicKTheory.StableGL

private theorem scalarOriginalMixedFunctorCompositionComputed
    {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    {E : Type uE} [Category.{vE} E] (F : A ⥤ B) (G : B ⥤ E) :
    CategoryTheory.realizedNerveFunctorMap (F ⋙ G) =
      (CategoryTheory.realizedNerveFunctorMap G).comp
        (CategoryTheory.realizedNerveFunctorMap F) := by
  rw [CategoryTheory.realizedNerveFunctorMap_larger_recipe.{uA, vA, uE, vE, max uB vB}
      (F ⋙ G),
    CategoryTheory.realizedNerveFunctorMap_larger_recipe.{uB, vB, uE, vE, max uA vA} G,
    CategoryTheory.realizedNerveFunctorMap_larger_recipe.{uA, vA, uB, vB, max uE vE} F]
  apply ContinuousMap.ext
  intro x
  let HA := SSet.realizedNerveLiftHomeomorph.{uA, vA, max uA vA uB vB uE vE} A
  let HB := SSet.realizedNerveLiftHomeomorph.{uB, vB, max uA vA uB vB uE vE} B
  let HE := SSet.realizedNerveLiftHomeomorph.{uE, vE, max uA vA uB vB uE vE} E
  let LF :=
    (ULiftHomULiftCategory.equiv.{max uA vA uB vB uE vE,
      max uA vA uB vB uE vE, vA, uA} A).inverse ⋙ F ⋙
      (ULiftHomULiftCategory.equiv.{max uA vA uB vB uE vE,
        max uA vA uB vB uE vE, vB, uB} B).functor
  let LG :=
    (ULiftHomULiftCategory.equiv.{max uA vA uB vB uE vE,
      max uA vA uB vB uE vE, vB, uB} B).inverse ⋙ G ⋙
      (ULiftHomULiftCategory.equiv.{max uA vA uB vB uE vE,
        max uA vA uB vB uE vE, vE, uE} E).functor
  let LFG :=
    (ULiftHomULiftCategory.equiv.{max uA vA uB vB uE vE,
      max uA vA uB vB uE vE, vA, uA} A).inverse ⋙ (F ⋙ G) ⋙
      (ULiftHomULiftCategory.equiv.{max uA vA uB vB uE vE,
        max uA vA uB vB uE vE, vE, uE} E).functor
  let z := HA.symm x
  have hFunctor : LFG = LF ⋙ LG := by
    exact CategoryTheory.Functor.ext (fun i => rfl) (fun i j f => by
      change LFG.map f = eqToHom (rfl : LFG.obj i = LFG.obj i) ≫ LFG.map f ≫
        eqToHom (rfl : LFG.obj j = LFG.obj j)
      exact CategoryTheory.eq_conj_eqToHom (LFG.map f))
  have hNerve : nerveMap LFG = nerveMap LF ≫ nerveMap LG :=
    (congrArg nerveMap hFunctor).trans (nerveMap_comp LF LG).symm
  have hTop : SSet.toTop.map (nerveMap LFG) =
      SSet.toTop.map (nerveMap LF) ≫ SSet.toTop.map (nerveMap LG) :=
    (SSet.toTop.congr_map hNerve).trans (SSet.toTop.map_comp _ _)
  have hStep : HE (SSet.toTop.map (nerveMap LFG) z) =
      HE (SSet.toTop.map (nerveMap LG) (SSet.toTop.map (nerveMap LF) z)) :=
    congrArg HE ((ConcreteCategory.congr_hom hTop z).trans (TopCat.comp_app _ _ z))
  change HE (SSet.toTop.map (nerveMap LFG) z) =
    HE (SSet.toTop.map (nerveMap LG)
      (HB.symm (HB (SSet.toTop.map (nerveMap LF) z))))
  exact hStep.trans
    ((congrArg (fun y => HE (SSet.toTop.map (nerveMap LG) y))
      (HB.symm_apply_apply (SSet.toTop.map (nerveMap LF) z))).symm)

private theorem scalarOriginalRowMapComputed (A : Type uA) [Ring A] :
    (finiteBGLTelescopeToRowZeroComponentTop A).hom =
      CategoryTheory.realizedNerveFunctorMap (finiteBGLTelescopeToRowZeroComponent A) := by
  have hNerve : finiteBGLTelescopeToRowZeroComponentNerve A =
      nerveMapCommonHomUp.{0, uA, 0} (finiteBGLTelescopeToRowZeroComponent A) := by
    ext Δ σ
    exact (finiteBGLTelescopeToRowZeroComponentNerve_app A Δ σ).trans
      (nerveMapCommonHomUp_app.{0, uA, 0}
        (finiteBGLTelescopeToRowZeroComponent A) Δ σ).symm
  have hTop : (finiteBGLTelescopeToRowZeroComponentTop A).hom =
      (SSet.toTop.map (finiteBGLTelescopeToRowZeroComponentNerve A)).hom :=
    congrArg (fun f : SSet.toTop.obj (nerve (FiniteBGLTelescopeCategory A)) ⟶
        SSet.toTop.obj
          (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel A))) => f.hom)
      (finiteBGLTelescopeToRowZeroComponentTop_eq A)
  have hMap : (SSet.toTop.map (finiteBGLTelescopeToRowZeroComponentNerve A)).hom =
      (SSet.toTop.map
        (nerveMapCommonHomUp.{0, uA, 0} (finiteBGLTelescopeToRowZeroComponent A))).hom :=
    congrArg (fun f : nerve (FiniteBGLTelescopeCategory A) ⟶
        nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel A)) =>
      (SSet.toTop.map f).hom) hNerve
  exact hTop.trans (hMap.trans
    (CategoryTheory.realizedNerveFunctorMap_commonUpFrame.{0, uA}
      (finiteBGLTelescopeToRowZeroComponent A)).symm)

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

private theorem originalScalarRowSourceFactorComputed (f : R →+* S) :
    ordinaryFiniteBGLTelescopeRowScalarSourceMap f =
      (CategoryTheory.realizedNerveFunctorMap
        (SInverseS.zeroComponentFunctor ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
          FGProjectiveCat.scalarExtension.{uR, uS, uR} f))).comp
        (finiteBGLTelescopeToRowZeroComponentTop R).hom := by
  let F := finiteBGLTelescopeToRowZeroComponent R
  let G := SInverseS.zeroComponentFunctor
    ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
      FGProjectiveCat.scalarExtension.{uR, uS, uR} f)
  have hView : ordinaryFiniteBGLTelescopeRowScalarSourceMap f =
      CategoryTheory.realizedNerveFunctorMap (F ⋙ G) :=
    ordinaryFiniteBGLTelescopeRowScalarSourceMap_eq_realizedFunctorMap f
  have hRow : (finiteBGLTelescopeToRowZeroComponentTop R).hom =
      CategoryTheory.realizedNerveFunctorMap F := scalarOriginalRowMapComputed R
  exact hView.trans ((scalarOriginalMixedFunctorCompositionComputed F G).trans
    (congrArg (fun k => (CategoryTheory.realizedNerveFunctorMap G).comp k) hRow.symm))

private theorem originalScalarRowTargetFactorComputed (f : R →+* S) :
    ordinaryFiniteBGLTelescopeRowScalarTargetMap f =
      (CategoryTheory.realizedNerveFunctorMap
        (SInverseS.zeroComponentFunctor ((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
          (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse))).comp
        ((finiteBGLTelescopeToRowZeroComponentTop S).hom.comp
          (CategoryTheory.realizedNerveFunctorMap.{0, uR, 0, uS}
            (finiteBGLTelescopeScalarFunctor f))) := by
  let T := finiteBGLTelescopeScalarFunctor f
  let A := finiteBGLTelescopeToRowZeroComponent S
  let G := SInverseS.zeroComponentFunctor
    ((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
      (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse)
  have hView : ordinaryFiniteBGLTelescopeRowScalarTargetMap f =
      CategoryTheory.realizedNerveFunctorMap ((T ⋙ A) ⋙ G) :=
    ordinaryFiniteBGLTelescopeRowScalarTargetMap_eq_realizedFunctorMap f
  have hRow : (finiteBGLTelescopeToRowZeroComponentTop S).hom =
      CategoryTheory.realizedNerveFunctorMap A := scalarOriginalRowMapComputed S
  exact hView.trans
    ((scalarOriginalMixedFunctorCompositionComputed (T ⋙ A) G).trans
      ((congrArg (fun k => (CategoryTheory.realizedNerveFunctorMap G).comp k)
        (scalarOriginalMixedFunctorCompositionComputed T A)).trans
        (congrArg (fun k => (CategoryTheory.realizedNerveFunctorMap G).comp
          (k.comp (CategoryTheory.realizedNerveFunctorMap T))) hRow.symm)))

/-- The entire original source map factors through the SAME original row
projection and the actual scalar/model zero-component functor map. -/
public theorem ordinaryFiniteBGLTelescopeRowScalarSourceMap_factor (f : R →+* S) :
    ordinaryFiniteBGLTelescopeRowScalarSourceMap f =
      (CategoryTheory.realizedNerveFunctorMap
        (SInverseS.zeroComponentFunctor ((FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
          FGProjectiveCat.scalarExtension.{uR, uS, uR} f))).comp
        (finiteBGLTelescopeToRowZeroComponentTop R).hom :=
  originalScalarRowSourceFactorComputed f

/-- The entire original target map factors through the SAME coefficient
functor map, original target row projection and original universe/model functor. -/
public theorem ordinaryFiniteBGLTelescopeRowScalarTargetMap_factor (f : R →+* S) :
    ordinaryFiniteBGLTelescopeRowScalarTargetMap f =
      (CategoryTheory.realizedNerveFunctorMap
        (SInverseS.zeroComponentFunctor ((FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
          (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse))).comp
        ((finiteBGLTelescopeToRowZeroComponentTop S).hom.comp
          (CategoryTheory.realizedNerveFunctorMap.{0, uR, 0, uS}
            (finiteBGLTelescopeScalarFunctor f))) :=
  originalScalarRowTargetFactorComputed f

end AlgebraicKTheory.StableGL

end
