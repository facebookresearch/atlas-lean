/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralRamificationTensorModels

/-!
# All-base ramification frame and coroot tensor comparisons

Frame maps are fixed by the actual module isomorphism on every test
scheme. Root-torsor maps are fixed on every actual coroot pushout point.
The finite tensor comparison is then the native tensor-pullback map
followed by those root maps. Hidden nilpotent line automorphisms are
excluded by the full symbol and computed-dual comparisons.
Source: Donagi--Gaitsgory arXiv:math/0005132v3, Sections 5.2--5.5.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralRamificationTorsorReindexing

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open CameralFoundationPackages CameralRamificationReindexing CameralRootSL2Sources
open CameralRamificationTensorModels ExpansionParameterModels ContractedTorsorModels
open NormalizedTorsorOperations TorusLineFrameModels CoherentCurveLinearSeries

def frameBasis (Gm : TorusTheory ℂ 1) (Y : Over (Spec (.of ℂ))) (L : Y.left.Modules)
    (M : TorusLineFrameModels.LineFrames Gm Y L) :
    letI := Gm.group
    ∀ (U : Over (Spec (.of ℂ))) (f : U ⟶ Y) (p : U ⟶ M.bundle.torsor.total),
      p ≫ M.bundle.torsor.projection = f →
        (structureModule U.left ≅ (Scheme.Modules.pullback f.left).obj L) := by
  letI := Gm.group
  intro U f p h
  let q : testScheme Y (Over.mk f.left) ⟶ M.bundle.torsor.total :=
    Over.homMk p.left (p.w.trans f.w.symm)
  have hq : q ≫ M.bundle.torsor.projection = testMap Y (Over.mk f.left) := by
    apply Over.OverMorphism.ext
    change p.left ≫ M.bundle.torsor.projection.left = f.left
    exact congrArg (fun a : U ⟶ Y => a.left) h
  exact M.basis (Over.mk f.left) ⟨q, hq⟩

variable {G : Over (Spec (.of ℂ))} [GrpObj G] {tori : ∀ n : ℕ, TorusTheory ℂ n}
  (F : Foundation G tori) [GeneralLinearFrameSchemes.FrameTheory 2]
  [RankTwoMatrixGroupModels.GL2MatrixTheory] [RankTwoMatrixGroupModels.SL2MatrixTheory]
  (K : RootNormalizerGeometry G tori F) (D : RootTorsorInputs F K)

attribute [local instance] CameralRamificationTensorModels.torusGroup

structure RootPullback {X X' : Over (Spec (.of ℂ))} {C : Cover F X} {C' : Cover F X'}
    (m : CameralArrow F C C') (i : Fin F.roots.count)
    (h : ReflectionCompatible F m i i) (R : RamificationPullback F m i i h) where
  frames : letI := (tori 1).group
    (D.multiplicative.baseChange.change m.total).obj
      (CameralRamificationReindexing.frames F C' i).bundle ≅
      (CameralRamificationReindexing.frames F C i).bundle
  frames_normalized : letI := (tori 1).group
    ∀ (U : Over (Spec (.of ℂ))) (y : U ⟶ total F C)
      (p : U ⟶ ((D.multiplicative.baseChange.change m.total).obj
        (CameralRamificationReindexing.frames F C' i).bundle).torsor.total)
      (_hp : p ≫ ((D.multiplicative.baseChange.change m.total).obj
        (CameralRamificationReindexing.frames F C' i).bundle).torsor.projection = y)
      (hq : (p ≫ frames.hom.iso.hom) ≫
        (CameralRamificationReindexing.frames F C i).bundle.torsor.projection = y)
      (hs : (p ≫ original (D.multiplicative.baseChange.pullback m.total
        (CameralRamificationReindexing.frames F C' i).bundle)) ≫
        (CameralRamificationReindexing.frames F C' i).bundle.torsor.projection = y ≫ m.total),
    frameBasis (tori 1) (total F C) (line F C i) (CameralRamificationReindexing.frames F C i)
      U y (p ≫ frames.hom.iso.hom) hq =
    frameBasis (tori 1) (total F C') (line F C' i) (CameralRamificationReindexing.frames F C' i)
      U (y ≫ m.total) (p ≫ original (D.multiplicative.baseChange.pullback m.total
        (CameralRamificationReindexing.frames F C' i).bundle)) hs ≪≫
      (Scheme.Modules.pullbackComp y.left m.total.left).symm.app (line F C' i) ≪≫
      (Scheme.Modules.pullback y.left).mapIso R.line
  root : (D.torus.baseChange.change m.total).obj (rootTorsor F K D C' i) ≅ rootTorsor F K D C i
  root_normalized : letI := (tori 1).group; letI := K.corootHom i
    ∀ (U : Over (Spec (.of ℂ))) (y : U ⟶ total F C)
      (p : U ⟶ ((D.multiplicative.baseChange.change m.total).obj
        (CameralRamificationReindexing.frames F C' i).bundle).torsor.total)
      (_hy : p ≫ ((D.multiplicative.baseChange.change m.total).obj
        (CameralRamificationReindexing.frames F C' i).bundle).torsor.projection = y)
      (t : U ⟶ Torus F)
      (hp : (CartesianMonoidalCategory.lift
        (p ≫ original (D.multiplicative.baseChange.pullback m.total
          (CameralRamificationReindexing.frames F C' i).bundle)) t ≫
          (rootPushout F K D C' i).quotient) ≫
            (rootTorsor F K D C' i).torsor.projection = y ≫ m.total),
    (pullback.lift (CartesianMonoidalCategory.lift
      (p ≫ original (D.multiplicative.baseChange.pullback m.total
        (CameralRamificationReindexing.frames F C' i).bundle)) t ≫
        (rootPushout F K D C' i).quotient) y hp ≫
      (D.torus.baseChange.pullback m.total (rootTorsor F K D C' i)).comparison.inv) ≫
        root.hom.iso.hom =
    CartesianMonoidalCategory.lift (p ≫ frames.hom.iso.hom) t ≫ (rootPushout F K D C i).quotient

def productPullbackIso {X X' : Over (Spec (.of ℂ))} {C : Cover F X} {C' : Cover F X'}
    (m : CameralArrow F C C')
    (P : ∀ i, (D.torus.baseChange.change m.total).obj (rootTorsor F K D C' i) ≅
      rootTorsor F K D C i) :
    ∀ is : List (Fin F.roots.count),
      (D.torus.baseChange.change m.total).obj (ramificationProduct F K D C' is) ≅
        ramificationProduct F K D C is
  | [] => D.torus.baseUnit m.total
  | i :: is => D.torus.baseTensor m.total (rootTorsor F K D C' i)
      (ramificationProduct F K D C' is) ≪≫
      NormalizedTorsorOperations.tensorIso (G := Torus F) D.torus.tensor (P i)
        (productPullbackIso m P is)

structure TorsorReindexing (R : RamificationReindexing F) where
  roots : ∀ {X X' : Over (Spec (.of ℂ))} {C : Cover F X} {C' : Cover F X'}
      (m : CameralArrow F C C') (i : Fin F.roots.count) (h : ReflectionCompatible F m i i),
    RootPullback F K D m i h (R.map m i i h)

def ramificationPullbackIso (R : RamificationReindexing F) (P : TorsorReindexing F K D R)
    {X X' : Over (Spec (.of ℂ))} {C : Cover F X} {C' : Cover F X'}
    (m : CameralArrow F C C') (h : ∀ i, ReflectionCompatible F m i i) (w : F.Weyl) :
    (D.torus.baseChange.change m.total).obj (ramificationTorsor F K D C' w) ≅
      ramificationTorsor F K D C w :=
  productPullbackIso F K D m (fun i => (P.roots m i (h i)).root) (inversionRoots F K w)

end MathlibExt.AlgebraicGeometry.CameralRamificationTorsorReindexing
