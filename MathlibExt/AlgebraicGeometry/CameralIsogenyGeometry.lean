/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralUniversalRawLiftModels

/-!
# Actual pinned central isogenies and cross-root ramification maps

The cover is a finite flat surjective morphism of actual group schemes.
Its differential is fixed by every Lie jet, and both universal planes
are mapped through that differential. Torus, Borel, normalizer and
all pinned SL2 maps commute with the same group morphism. The lifted
coroots are monomorphisms. Cross-root line maps use the full symbol
pullback and its computed perfect dual pairing.
Source: DG math/0005132v3, Sections6.5/7.2/10/15.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralIsogenyGeometry

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open CameralFoundationPackages CameralRootSL2Sources CameralRamificationReindexing
open CameralRamificationTensorModels CameralRamificationSymbols CameralSymbolReindexModels
open CameralCoverDescentModels CameralBorelReductionModels CameralUnramifiedNormalizerModels
open CameralUniversalRegularizerModels ExpansionParameterModels SchemeLieJetFamilies
open CoherentCurveLinearSeries LineBundleTaskContracts RelativeLambdaReindexing
open AlgebraicLineBundleFamilies FiniteCoverLocalComparison
open scoped TensorProduct

variable {G G' : Over (Spec (.of ℂ))} [GrpObj G] [GrpObj G']
  {tori : ∀ n : ℕ, TorusTheory ℂ n} (F : Foundation G tori) (F' : Foundation G' tori)
  [GeneralLinearFrameSchemes.FrameTheory 2]
  [RankTwoMatrixGroupModels.GL2MatrixTheory] [RankTwoMatrixGroupModels.SL2MatrixTheory]
  (K : RootNormalizerGeometry G tori F) (K' : RootNormalizerGeometry G' tori F')
  (I : IncidenceAction F) (I' : IncidenceAction F')
  (B : BorelGeometry F) (B' : BorelGeometry F')

attribute [local instance] CameralRamificationTensorModels.torusGroup
attribute [local instance] CameralUnramifiedNormalizerModels.normalizerGroup
attribute [local instance] CameralBorelReductionModels.borelGroup
attribute [local instance] CameralBorelReductionModels.quotientHom
attribute [local instance] CameralRegularizedHiggsModels.centralizerGroupAction

structure PinnedIsogeny where
  group : G' ⟶ G
  [groupHom : IsMonHom group]
  [finite : IsFinite group.left]
  [flat : Flat group.left]
  [surjective : Surjective group.left]
  central : ∀ (U : Over (Spec (.of ℂ))) (z : U ⟶ G')
    (_hz : z ≫ group = toUnit U ≫ η[G]) (g : U ⟶ G'),
    SchemeLieJetFamilies.conjugate G' z g = g
  reductive : ReductiveGroupHypotheses.IsLinearlyReductive G'
  torus : Torus F' ⟶ Torus F
  [torusHom : IsMonHom torus]
  torus_group : torus ≫ F.source.torus = F'.source.torus ≫ group
  normalizer : F'.normalizer.scheme ⟶ F.normalizer.scheme
  [normalizerHom : IsMonHom normalizer]
  normalizer_group : normalizer ≫ F.normalizer.inclusion = F'.normalizer.inclusion ≫ group
  torus_normalizer : F'.normalizer.torus ≫ normalizer = torus ≫ F.normalizer.torus
  borel : B'.scheme ⟶ B.scheme
  [borelHom : IsMonHom borel]
  borel_group : borel ≫ B.inclusion = B'.inclusion ≫ group
  quotient : borel ≫ B.quotient = B'.quotient ≫ torus
  root : Fin F'.roots.count ≃ Fin F.roots.count
  weyl : F'.Weyl ≃* F.Weyl
  character : ∀ i, torus ≫ F.roots.character (root i) = F'.roots.character i
  coroot : ∀ i, F'.roots.coroot i ≫ torus = F.roots.coroot (root i)
  primitive : ∀ i : Fin F'.roots.count, Mono (F'.roots.coroot i)
  simple : ∀ i, SimpleRoot G' tori F' i ↔ SimpleRoot G tori F (root i)
  sl2 : ∀ i, (K'.sl2 i).map ≫ group = (K.sl2 (root i)).map
  lifted_normalizer : ∀ i,
    (K'.sl2 i).normalizer ≫ normalizer = (K.sl2 (root i)).normalizer
  normalizer_weyl : ∀ (U : Over (Spec (.of ℂ))) (n : U ⟶ F'.normalizer.scheme) (x : U.left),
    F.weyl.points U (n ≫ normalizer ≫ F.normalizer.quotient) x =
      weyl (F'.weyl.points U (n ≫ F'.normalizer.quotient) x)
  lie : ∀ A : CommAlgCat.{0} ℂ,
    (A ⊗[ℂ] F'.lie.carrier) ≃ₗ[A] (A ⊗[ℂ] F.lie.carrier)
  jets : ∀ (A : CommAlgCat.{0} ℂ) (x : A ⊗[ℂ] F'.lie.carrier),
    jetPoint G' F'.lie.carrier F'.lie.model F'.jets A x ≫ group =
      jetPoint G F.lie.carrier F.lie.model F.jets A (lie A x)
  base : F'.centralizers.scheme ≅ F.centralizers.scheme
  planes : ∀ (A : CommAlgCat.{0} ℂ) (c : affine A ⟶ F'.centralizers.scheme),
    (F.centralizers.points A (c ≫ base.hom)).plane.toSubmodule =
      (F'.centralizers.points A c).plane.toSubmodule.map (lie A).toLinearMap
  incidence : universalTotal F' I' ≅ universalTotal F I
  parameter : incidence.hom ≫ universalProjection F I = universalProjection F' I' ≫ base.hom
  incidence_planes : ∀ (A : CommAlgCat.{0} ℂ) (c : affine A ⟶ universalTotal F' I'),
    (I.incidence.points A (c ≫ incidence.hom)).val.snd.plane.toSubmodule =
      (I'.incidence.points A c).val.snd.plane.toSubmodule.map (lie A).toLinearMap
  reflection : ∀ i,
    (coverIso F' I'.incidence.cameral (F'.roots.reflection i)).hom ≫ incidence.hom =
      incidence.hom ≫ (coverIso F I.incidence.cameral (F.roots.reflection (root i))).hom

structure CrossChartArrow {X X' : Over (Spec (.of ℂ))}
    {C : Cover F X} {C' : Cover F' X'} (m : total F' C' ⟶ total F C)
    {i : Fin F'.roots.count} {j : Fin F.roots.count}
    (U : AffineReflection (total F' C') (reflection F' C' i))
    (V : AffineReflection (total F C) (reflection F C j)) where
  coefficients : V.algebra →ₐ[ℂ] U.algebra
  symbols : CoefficientMap (s := V.reflection) (s' := U.reflection) coefficients
  sheaf : SheafMap coefficients symbols
  geometric : Spec.map (CommRingCat.ofHom coefficients.toRingHom) ≫
    V.chart.hom ≫ V.neighborhood.val.ι = U.chart.hom ≫ U.neighborhood.val.ι ≫ m.left

structure CrossSymbols {X X' : Over (Spec (.of ℂ))}
    {C : Cover F X} {C' : Cover F' X'} (m : total F' C' ⟶ total F C)
    (i : Fin F'.roots.count) (j : Fin F.roots.count) where
  comparison : (Scheme.Modules.pullback m.left).obj (ideal F C j).module ≅ (ideal F' C' i).module
  chartCover : ∀ x : (total F' C').left,
    ∃ (U : AffineReflection (total F' C') (reflection F' C' i))
      (V : AffineReflection (total F C) (reflection F C j)),
      x ∈ U.neighborhood.val ∧ Nonempty (CrossChartArrow F F' m U V)
  coefficients : ∀ (U : AffineReflection (total F' C') (reflection F' C' i))
      (V : AffineReflection (total F C) (reflection F C j)) (a : CrossChartArrow F F' m U V),
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom a.coefficients.toRingHom))).map
        ((presentation F C j).presentation V).hom ≫ a.sheaf.map =
      (Scheme.Modules.pullbackComp (Spec.map (CommRingCat.ofHom a.coefficients.toRingHom))
        (V.chart.hom ≫ V.neighborhood.val.ι)).hom.app (ideal F C j).module ≫
      (Scheme.Modules.pullbackCongr (by simpa only [Category.assoc] using a.geometric)).hom.app _ ≫
      (Scheme.Modules.pullbackComp (U.chart.hom ≫ U.neighborhood.val.ι) m.left).inv.app _ ≫
      (Scheme.Modules.pullback (U.chart.hom ≫ U.neighborhood.val.ι)).map comparison.hom ≫
      ((presentation F' C' i).presentation U).hom
  evaluation : (Scheme.Modules.pullback m.left).map (ideal F C j).evaluation ≫
      (pullbackStructureIso m.left).hom = comparison.hom ≫ (ideal F' C' i).evaluation

structure CrossRamification {X X' : Over (Spec (.of ℂ))}
    {C : Cover F X} {C' : Cover F' X'} (m : total F' C' ⟶ total F C)
    (i : Fin F'.roots.count) (j : Fin F.roots.count) where
  symbols : CrossSymbols F F' m i j
  tensor : TensorPullbackComparison m.left
  line : (Scheme.Modules.pullback m.left).obj (CameralRamificationReindexing.line F C j) ≅
    CameralRamificationReindexing.line F' C' i
  pairing : (Scheme.Modules.pullback m.left).map (dualEvaluation F C j) ≫
      (pullbackStructureIso m.left).hom =
    (tensor.iso (ideal F C j).module (CameralRamificationReindexing.line F C j)).hom ≫
      tensorMap symbols.comparison.hom line.hom ≫ dualEvaluation F' C' i
  sectionMap : pullbackSection m.left (sectionData F C j).sectionMap ≫ line.hom =
    (sectionData F' C' i).sectionMap

end MathlibExt.AlgebraicGeometry.CameralIsogenyGeometry
