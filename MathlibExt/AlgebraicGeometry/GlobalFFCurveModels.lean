/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeFFCurveFamilies
public import MathlibExt.AlgebraicGeometry.RelativePerfectoidBases
public import MathlibExt.AlgebraicGeometry.RelativeFFAtlasDiagrams
public import MathlibExt.AlgebraicGeometry.AnalyticBundlePrestackModels
public import Mathlib.CategoryTheory.Sites.Descent.IsStack

/-!
# Actual global Perf-indexed FF curve and bundle diagrams

The global curve is covered by the original affine relative curves
of the residue-linear perfectoid open atlas. The chart maps are open
with actual stalk isomorphisms and cover every point. Their overlap
maps are the prescribed affine FF base-change maps. Global morphisms
are fixed on every compatible affine test of the actual source and
target perfectoid spaces.

Bundling these maps gives the actual global curve functor. Its bundle
diagram is composition with the native source-normalized G-torsor
prestack, whose objects and pullbacks were fixed before any v-stack
assertion. Generic ringed gluing is source integration, not a new
geometry primitive.
Source: Fargues--Scholze, arXiv:2102.13459v4, Sections I.2 and III.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GlobalFFCurveModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite TopologicalSpace Topology
open _root_.AlgebraicGeometry
open LocalWittCoefficientFields LocalCoefficientScalarFrames RelativeFarguesFontaineRings
open RelativeFarguesFontaineMaps RelativeFFCurveFamilies RelativePerfectoidBases
open PerfectoidDiamondModels AnalyticGroupTorsorSites AnalyticBundlePrestackModels

variable (p : ℕ) [Fact p.Prime] {E : MixedField p} (C : CoefficientData p E)
  (I : IntegerPresentation p C) (A : RelativeFFCurveFamilies.Family p C I)

structure CurveAtlas (S : RelativePerfectoidBases.Space p C) where
  labels : LabelledAtlas p C S
  curve : ESpace p E.field
  chart : ∀ i, (A.frame (labels.base i)).object p C I ⟶ curve
  open_embedding : ∀ i, IsOpenEmbedding (chart i).left.hom.val.base
  stalk_iso : ∀ i x, IsIso ((chart i).left.hom.val.stalkMap x)
  covers : ∀ x : curve.left.obj.space, ∃ i, x ∈ Set.range (chart i).left.hom.val.base
  overlap : ∀ i j (R : Base p C) (f : R ⟶ labels.base i) (g : R ⟶ labels.base j),
    affineMap p f.val ≫ labels.chart p C i = affineMap p g.val ≫ labels.chart p C j →
      (A.change f).map ≫ chart i = (A.change g).map ≫ chart j
  gluing : IsColimit (RelativeFFAtlasDiagrams.cocone p C I A labels curve chart
    (fun o ↦ overlap o.left o.right o.base o.first o.second o.square))

structure Family where
  atlas : ∀ S : RelativePerfectoidBases.Space p C, CurveAtlas p C I A S
  map : ∀ {S T : RelativePerfectoidBases.Space p C} (_f : S ⟶ T),
    (atlas S).curve ⟶ (atlas T).curve
  identity : ∀ S, map (𝟙 S) = 𝟙 (atlas S).curve
  composition : ∀ {S T U : RelativePerfectoidBases.Space p C} (f : S ⟶ T) (g : T ⟶ U),
    map (f ≫ g) = map f ≫ map g
  local_normalized : ∀ {S T : RelativePerfectoidBases.Space p C} (f : S ⟶ T)
    (i : S.perfectoid.atlas.index) (j : T.perfectoid.atlas.index) (R : Base p C)
    (a : R ⟶ (atlas S).labels.base i) (b : R ⟶ (atlas T).labels.base j),
    affineMap p a.val ≫ (atlas S).labels.chart p C i ≫
        (RelativePerfectoidBases.forget p C).map f =
      affineMap p b.val ≫ (atlas T).labels.chart p C j →
        (A.change a).map ≫ (atlas S).chart i ≫ map f = (A.change b).map ≫ (atlas T).chart j

def Family.toFunctor (F : Family p C I A) :
    RelativePerfectoidBases.Space p C ⥤ ESpace p E.field where
  obj S := (F.atlas S).curve
  map f := F.map f
  map_id S := F.identity S
  map_comp f g := F.composition f g

variable (G : Over (Spec (.of E.field))) [GrpObj G]
  (H : ∀ X : ESpace p E.field, GroupDescent p E.field G X)
  (P : PullbackPreservation p E.field G H)
  (B : BundlePrestack p E.field G H P)

/-- The global bundle prestack has actual curve torsors at every original perfectoid base. -/
def Family.bunG (F : Family p C I A) :
    Pseudofunctor (LocallyDiscrete (RelativePerfectoidBases.Space p C)ᵒᵖ) Cat.{1, 1} :=
  ((F.toFunctor p C I A).op.toPseudofunctor).comp B.functor

theorem Family.bundle_groupoid (F : Family p C I A) (S : RelativePerfectoidBases.Space p C) :
    IsGroupoid ((F.bunG p C I A G H P B).obj (LocallyDiscrete.mk (op S))) := by
  change IsGroupoid (B.functor.obj (LocallyDiscrete.mk (op (F.atlas S).curve)))
  rw [B.object_normalized]
  change IsGroupoid (Bundles p E.field G H (F.atlas S).curve)
  infer_instance

/-- The two-fibre retains the actual native pullback comparison to the chosen source torsor. -/
abbrev Family.bundleFibre (F : Family p C I A)
    {S T : RelativePerfectoidBases.Space p C} (f : S ⟶ T)
    (Q : Bundles p E.field G H (F.atlas S).curve) :=
  CostructuredArrow (bundlePullback p E.field G H P (F.map f)) Q

/-- v-descent is a conclusion about this specified actual bundle diagram. -/
def Family.IsVStack (F : Family p C I A) : Prop :=
  (F.bunG p C I A G H P B).IsStack (RelativePerfectoidBases.topology p C)

end MathlibExt.AlgebraicGeometry.GlobalFFCurveModels
