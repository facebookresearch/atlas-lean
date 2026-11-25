/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MeromorphicTorsorCompletion

/-!
# Original chart refinements of meromorphic completion

Refinements retain the original analytic, divisor and puncture maps.
Positive completion is the native lift of all actual finite-quotient
maps. Generic refinement is its actual parameter-localization lift.
No coefficient map is chosen independently of these source maps.

Local Hecke restriction uses native fpqc torsor pullback and the
original sheaf pullback-composition square. Global compatibility fixes
both torsor legs and every original integral frame. Source construction
and coherence proofs are direct Wanted outputs.
Source: Fargues--Scholze, arXiv:2102.13459v4, Sections III.3 and VI.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MeromorphicCompletionRefinements

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.GeneralStackGeometry
open AnalyticGroupTorsorSites AnalyticBundlePrestackModels AnalyticBundleModifications
open AnalyticMeromorphicCoordinates MeromorphicHeckeModels AffinoidTorsorAlgebraizationModels
open CompletedTorsorSourceFrames MeromorphicTorsorCompletion
open MathlibExt.CategoryTheory.SheafTorsorGroupoids

variable (p : ℕ) [Fact p.Prime] (E : Type) [Field E]
  {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
  (Q Q' : PoleChart p E d U)

/-- Every chart refinement retains the actual divisor and puncture squares. -/
structure PoleRefinement where
  map : Q'.space ⟶ Q.space
  square : map ≫ Q.map = Q'.map
  divisor : Q'.divisor ⟶ Q.divisor
  divisor_square : divisor ≫ Q.divisorMap = Q'.divisorMap ≫ map
  puncture : Q'.puncture.space ⟶ Q.puncture.space
  puncture_square : puncture ≫ Q.puncture.map = Q'.puncture.map ≫ map
  puncture_original : puncture ≫ Q.punctureToOriginal = Q'.punctureToOriginal
  parameterUnit : (SectionRing p E Q'.space)ˣ
  parameter : sectionMap p E map Q.parameter = parameterUnit.val * Q'.parameter

/-- The displayed original chart-kernel ideal. -/
abbrev chartIdeal (V : PoleChart p E d U) := divisorKernel p E V.divisorMap ⊤

variable (r : PoleRefinement p E d U Q Q')

/-- Power preservation concerns every actual finite source quotient. -/
def PreservesPowers : Prop := ∀ n : ℕ,
  chartIdeal p E d U Q ^ n ≤
    (chartIdeal p E d U Q' ^ n).comap (sectionMap p E r.map)

variable (hp : PreservesPowers p E d U Q Q' r)

/-- Every finite map is the original analytic coefficient map on its actual quotient. -/
def finiteMap (n : ℕ) : FormalRing p E d U Q →+*
    SectionRing p E Q'.space ⧸ chartIdeal p E d U Q' ^ n :=
  (Ideal.quotientMap (chartIdeal p E d U Q' ^ n) (sectionMap p E r.map) (hp n)).comp
    (AdicCompletion.evalₐ (chartIdeal p E d U Q) n).toRingHom

/-- Compatibility is a proof about those fixed finite maps. -/
def FiniteCoherence : Prop := ∀ {m n : ℕ} (h : m ≤ n),
  (Ideal.Quotient.factorPow (chartIdeal p E d U Q') h).comp
    (finiteMap p E d U Q Q' r hp n) = finiteMap p E d U Q Q' r hp m

variable (hc : FiniteCoherence p E d U Q Q' r hp)

/-- The positive map is computed by the native full inverse-limit universal map. -/
def positiveMap : FormalRing p E d U Q →+* FormalRing p E d U Q' :=
  AdicCompletion.liftRingHom (chartIdeal p E d U Q')
    (finiteMap p E d U Q Q' r hp) hc

omit [Fact p.Prime] in
/-- Every finite projection is the actual original quotient map. -/
theorem positiveMap_finite (n : ℕ) (a : FormalRing p E d U Q) :
    AdicCompletion.evalₐ (chartIdeal p E d U Q') n
      (positiveMap p E d U Q Q' r hp hc a) = finiteMap p E d U Q Q' r hp n a :=
  AdicCompletion.evalₐ_liftRingHom _ _ hc n a

omit [Fact p.Prime] in
/-- Every original analytic coefficient uses its original refinement map. -/
theorem positiveMap_coefficients (a : SectionRing p E Q.space) :
    positiveMap p E d U Q Q' r hp hc (completionMap p E d U Q a) =
      completionMap p E d U Q' (sectionMap p E r.map a) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [positiveMap_finite]
  simp [finiteMap, completionMap]

/-- Source coefficient data supplies proofs, never a freely chosen completed map. -/
structure CoefficientRefinement where
  powers : PreservesPowers p E d U Q Q' r
  finite : FiniteCoherence p E d U Q Q' r powers
  genericUnit : IsUnit
    (((algebraMap (FormalRing p E d U Q') (GenericRing p E d U Q')).comp
      (positiveMap p E d U Q Q' r powers finite)) (formalParameter p E d U Q))

variable (R : CoefficientRefinement p E d U Q Q' r)

/-- Generic refinement is the actual localization universal map of positive refinement. -/
def genericMap : GenericRing p E d U Q →+* GenericRing p E d U Q' :=
  Localization.awayLift
    ((algebraMap (FormalRing p E d U Q') (GenericRing p E d U Q')).comp
      (positiveMap p E d U Q Q' r R.powers R.finite))
    (formalParameter p E d U Q) R.genericUnit

omit [Fact p.Prime] in
theorem genericMap_coefficients (a : FormalRing p E d U Q) :
    genericMap p E d U Q Q' r R (algebraMap _ (GenericRing p E d U Q) a) =
      algebraMap _ (GenericRing p E d U Q')
        (positiveMap p E d U Q Q' r R.powers R.finite a) :=
  IsLocalization.Away.lift_eq (formalParameter p E d U Q) R.genericUnit a

omit [Fact p.Prime] in
theorem positiveMap_scalars (a : E) :
    positiveMap p E d U Q Q' r R.powers R.finite (positiveScalars p E d U Q a) =
      positiveScalars p E d U Q' a := by
  rw [positiveScalars, RingHom.comp_apply, positiveMap_coefficients]
  exact congrArg (completionMap p E d U Q')
    (DFunLike.congr_fun (MeromorphicCoefficientCompletion.sectionMap_coefficients p E r.map) a)

/-- The positive base change is the actual spectrum of that computed coefficient map. -/
def positiveSchemeMap : positiveScheme p E d U Q' ⟶ positiveScheme p E d U Q :=
  Over.homMk (Spec.map (CommRingCat.ofHom
    (positiveMap p E d U Q Q' r R.powers R.finite))) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext (positiveMap_scalars p E d U Q Q' r R))

/-- The generic base change uses that same actual coefficient-preserving map. -/
def genericSchemeMap : genericScheme p E d U Q' ⟶ genericScheme p E d U Q :=
  Over.homMk (Spec.map (CommRingCat.ofHom (genericMap p E d U Q Q' r R))) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change genericMap p E d U Q Q' r R
      (algebraMap _ (GenericRing p E d U Q) (positiveScalars p E d U Q a)) = _
    rw [genericMap_coefficients p E d U Q Q' r R,
      positiveMap_scalars p E d U Q Q' r R]
    rfl)

omit [Fact p.Prime] in
/-- The original two coefficient-localization paths commute. -/
theorem localization_square :
    genericSchemeMap p E d U Q Q' r R ≫ localization p E d U Q =
      localization p E d U Q' ≫ positiveSchemeMap p E d U Q Q' r R := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (genericMap_coefficients p E d U Q Q' r R)

variable (G : Over (Spec (.of E))) [GrpObj G]
  (H : ∀ V : ESpace p E, GroupDescent p E G V)
  (P : PullbackPreservation p E G H)

omit [Fact p.Prime] in
/-- Every original analytic refinement point uses the actual chart square. -/
theorem sourceTestEquality (T : Site p E Q'.space) :
    (Over.map Q.map).obj ((Over.map r.map).obj T) = (Over.map Q'.map).obj T := by
  change Over.mk ((T.hom ≫ r.map) ≫ Q.map) = Over.mk (T.hom ≫ Q'.map)
  apply congrArg Over.mk
  rw [Category.assoc, r.square]

/-- Pull an original integral frame through that exact test equality. -/
def refinedFrameValue (N : Bundles p E G H X) (f : IntegralFrame p E G H d U Q N)
    (T : Site p E Q'.space)
    (x : ((forgetBundles p E G H X).obj N).obj.obj (op ((Over.map Q'.map).obj T))) :
    (pointGroups p E G).obj (op T.left) :=
  f.hom.val.hom.app (op ((Over.map r.map).obj T))
    (((forgetBundles p E G H X).obj N).obj.map
      (eqToHom (sourceTestEquality p E d U Q Q' r T)).op x)

/-- The refined integral frame is fixed on every source test and every source point. -/
structure RefinedFrame (N : Bundles p E G H X) (f : IntegralFrame p E G H d U Q N) where
  frame : IntegralFrame p E G H d U Q' N
  normalized : ∀ (T : Site p E Q'.space)
    (x : ((forgetBundles p E G H X).obj N).obj.obj (op ((Over.map Q'.map).obj T))),
    frame.hom.val.hom.app (op T) x = refinedFrameValue p E d U Q Q' r G H N f T x

variable (V : FpqcPreservesTorsors E G (positiveSchemeMap p E d U Q Q' r R))

/-- Torsor reindexing is native fpqc restriction on the computed positive spectrum. -/
def torsorReindex : FormalTorsors p E G d U Q ⥤ FormalTorsors p E G d U Q' :=
  fpqcTorsorPullback E G (positiveSchemeMap p E d U Q Q' r R) V

/-- The original native sheaf composition/congruence square fixes every restriction section. -/
def restrictionSheafSquare (N : FormalTorsors p E G d U Q) :
    ((WittDiscTorsorModels.actionPullback G (genericSchemeMap p E d U Q Q' r R)).obj
      ((genericActions p E G d U Q).obj N)).sheaf ≅
        ((genericActions p E G d U Q').obj
          ((torsorReindex p E d U Q Q' r R G V).obj N)).sheaf :=
  ((WittDiscTorsorModels.baseTopology E).overMapPullbackComp (Type 1)
    (genericSchemeMap p E d U Q Q' r R) (localization p E d U Q)).app
      ((WittDiscTorsorModels.torsorActions E G (positiveScheme p E d U Q)).obj N).sheaf ≪≫
  ((WittDiscTorsorModels.baseTopology E).overMapPullbackCongr (Type 1)
    (localization_square p E d U Q Q' r R)).app
      ((WittDiscTorsorModels.torsorActions E G (positiveScheme p E d U Q)).obj N).sheaf ≪≫
  (((WittDiscTorsorModels.baseTopology E).overMapPullbackComp (Type 1)
    (localization p E d U Q') (positiveSchemeMap p E d U Q Q' r R)).app
      ((WittDiscTorsorModels.torsorActions E G (positiveScheme p E d U Q)).obj N).sheaf).symm

/-- The action square must have precisely that original native sheaf map. -/
structure RestrictionSquare where
  comparison : genericActions p E G d U Q ⋙
    WittDiscTorsorModels.actionPullback G (genericSchemeMap p E d U Q Q' r R) ≅
      torsorReindex p E d U Q Q' r R G V ⋙ genericActions p E G d U Q'
  underlying : ∀ N : FormalTorsors p E G d U Q,
    (comparison.app N).hom.val = (restrictionSheafSquare p E d U Q Q' r R G V N).hom

variable (S : RestrictionSquare p E d U Q Q' r R G V)

/-- Local punctured comparison uses the same native restriction square on both legs. -/
def reindexedComparison :
    (localLeftLeg p E G d U Q ⋙ torsorReindex p E d U Q Q' r R G V) ⋙
      genericActions p E G d U Q' ≅
        (localRightLeg p E G d U Q ⋙ torsorReindex p E d U Q Q' r R G V) ⋙
          genericActions p E G d U Q' :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ S.comparison.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (localComparison p E G d U Q) _ ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ S.comparison ≪≫
          (Functor.associator _ _ _).symm

/-- Actual local Hecke base change, with all arrows and both native completed torsor legs. -/
def localReindex : LocalHecke p E G d U Q ⥤ LocalHecke p E G d U Q' :=
  Core.functorToCore ((CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
    (genericActions p E G d U Q') (genericActions p E G d U Q') (LocalHecke p E G d U Q)).obj
    ⟨localLeftLeg p E G d U Q ⋙ torsorReindex p E d U Q Q' r R G V,
      localRightLeg p E G d U Q ⋙ torsorReindex p E d U Q Q' r R G V,
      reindexedComparison p E d U Q Q' r R G V S⟩)

variable (A : Algebraization p E G H Q.space)
  (B : FpqcPreservesTorsors E G (completionBaseMap p E d U Q))
  (A' : Algebraization p E G H Q'.space)
  (B' : FpqcPreservesTorsors E G (completionBaseMap p E d U Q'))
  (F : SourceFrames p E G H P d U Q A)
  (F' : SourceFrames p E G H P d U Q' A')


/-- Original analytic refinement induces the actual Gamma/Spec coefficient scheme map. -/
def coefficientSchemeMap : coefficientScheme p E Q'.space ⟶ coefficientScheme p E Q.space :=
  (affineTests p E).map r.map

omit [Fact p.Prime] in
/-- Every coefficient test uses exactly that original analytic refinement. -/
theorem coefficientTestEquality (T : Site p E Q'.space) :
    (Over.map (coefficientSchemeMap p E d U Q Q' r)).obj
      ((coefficientTests p E Q'.space).obj T) =
    (coefficientTests p E Q.space).obj ((Over.map r.map).obj T) := by
  change Over.mk ((affineTests p E).map T.hom ≫ (affineTests p E).map r.map) =
    Over.mk ((affineTests p E).map (T.hom ≫ r.map))
  exact congrArg Over.mk ((affineTests p E).map_comp T.hom r.map).symm

omit [Fact p.Prime] in
/-- The actual completion/Gamma square commutes on every original coefficient. -/
theorem coefficientCompletion_square :
    positiveSchemeMap p E d U Q Q' r R ≫ completionBaseMap p E d U Q =
      completionBaseMap p E d U Q' ≫ coefficientSchemeMap p E d U Q Q' r := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

/-- The unframed algebraized source action before native completion. -/
def algebraicRefinementLeft : Bundles p E G H X ⥤
    Action (WittDiscTorsorModels.topology E (coefficientScheme p E Q'.space))
      (WittDiscTorsorModels.groupSheaf E G (coefficientScheme p E Q'.space)) :=
  bundlePullback p E G H P Q.map ⋙ A.functor ⋙
    WittDiscTorsorModels.torsorActions E G (coefficientScheme p E Q.space) ⋙
      WittDiscTorsorModels.actionPullback G (coefficientSchemeMap p E d U Q Q' r)

/-- The target is the original source algebraization of the refined chart restriction. -/
def algebraicRefinementRight : Bundles p E G H X ⥤
    Action (WittDiscTorsorModels.topology E (coefficientScheme p E Q'.space))
      (WittDiscTorsorModels.groupSheaf E G (coefficientScheme p E Q'.space)) :=
  bundlePullback p E G H P Q'.map ⋙ A'.functor ⋙
    WittDiscTorsorModels.torsorActions E G (coefficientScheme p E Q'.space)

/-- All unframed source algebraization maps are fixed before completing them. -/
structure AlgebraizationRefinement where
  comparison : algebraicRefinementLeft p E d U Q Q' r G H P A ≅
    algebraicRefinementRight p E d U Q' G H P A'
  normalized : ∀ (N : Bundles p E G H X) (T : Site p E Q'.space)
    (x : (algebraicPresheaf p E G Q.space
      (A.functor.obj ((bundlePullback p E G H P Q.map).obj N))).obj
        (op ((Over.map r.map).obj T))),
    (A'.comparison ((bundlePullback p E G H P Q'.map).obj N)).hom.app (op T)
      ((comparison.app N).hom.val.hom.app (op ((coefficientTests p E Q'.space).obj T))
        (((algebraicForget p E G Q.space).obj
          (A.functor.obj ((bundlePullback p E G H P Q.map).obj N))).obj.map
            (eqToHom (coefficientTestEquality p E d U Q Q' r T)).op x)) =
      ULift.up (((forgetBundles p E G H X).obj N).obj.map
        (eqToHom (sourceTestEquality p E d U Q Q' r T).symm).op
          (((A.comparison ((bundlePullback p E G H P Q.map).obj N)).hom.app
            (op ((Over.map r.map).obj T)) x).down))

/-- The completion/refinement comparison uses the actual native sheaf coefficient square. -/
def algebraizationCompletionSheafSquare (N : Bundles p E G H X) :
    ((WittDiscTorsorModels.torsorActions E G (positiveScheme p E d U Q')).obj
      ((torsorReindex p E d U Q Q' r R G V).obj
        ((completedTorsors p E G H P d U Q A B).obj N))).sheaf ≅
    ((WittDiscTorsorModels.actionPullback G (completionBaseMap p E d U Q')).obj
      ((algebraicRefinementLeft p E d U Q Q' r G H P A).obj N)).sheaf :=
  ((WittDiscTorsorModels.baseTopology E).overMapPullbackComp (Type 1)
    (positiveSchemeMap p E d U Q Q' r R) (completionBaseMap p E d U Q)).app
      ((algebraicForget p E G Q.space).obj
        (A.functor.obj ((bundlePullback p E G H P Q.map).obj N))) ≪≫
  ((WittDiscTorsorModels.baseTopology E).overMapPullbackCongr (Type 1)
    (coefficientCompletion_square p E d U Q Q' r R)).app
      ((algebraicForget p E G Q.space).obj
        (A.functor.obj ((bundlePullback p E G H P Q.map).obj N))) ≪≫
  (((WittDiscTorsorModels.baseTopology E).overMapPullbackComp (Type 1)
    (completionBaseMap p E d U Q') (coefficientSchemeMap p E d U Q Q' r)).app
      ((algebraicForget p E G Q.space).obj
        (A.functor.obj ((bundlePullback p E G H P Q.map).obj N)))).symm

/-- The action square has precisely that original native sheaf map. -/
structure AlgebraizationCompletionSquare where
  comparison : completedTorsors p E G H P d U Q A B ⋙
    torsorReindex p E d U Q Q' r R G V ⋙
      WittDiscTorsorModels.torsorActions E G (positiveScheme p E d U Q') ≅
    algebraicRefinementLeft p E d U Q Q' r G H P A ⋙
      WittDiscTorsorModels.actionPullback G (completionBaseMap p E d U Q')
  underlying : ∀ N : Bundles p E G H X,
    (comparison.app N).hom.val =
      (algebraizationCompletionSheafSquare p E d U Q Q' r R G H P V A B N).hom

/-- Unframed base change fixes all original source points and every formal frame. -/
structure CompletionRefinement where
  source : AlgebraizationRefinement p E d U Q Q' r G H P A A'
  square : AlgebraizationCompletionSquare p E d U Q Q' r R G H P V A B
  comparison : completedTorsors p E G H P d U Q A B ⋙
    torsorReindex p E d U Q Q' r R G V ≅ completedTorsors p E G H P d U Q' A' B'
  underlying : ∀ N : Bundles p E G H X,
    (WittDiscTorsorModels.torsorActions E G (positiveScheme p E d U Q')).map
      (comparison.hom.app N) = square.comparison.hom.app N ≫
        (WittDiscTorsorModels.actionPullback G (completionBaseMap p E d U Q')).map
          (source.comparison.hom.app N)
  frames : ∀ (N : Bundles p E G H X) (f : IntegralFrame p E G H d U Q N)
    (f' : RefinedFrame p E d U Q Q' r G H N f),
    (WittDiscTorsorModels.torsorActions E G (positiveScheme p E d U Q')).map
      (comparison.hom.app N) ≫ (formalFrame p E G H P d U Q' A' B' (F' N f'.frame)).hom =
        (WittDiscTorsorModels.actionPullback G (positiveSchemeMap p E d U Q Q' r R)).map
          (formalFrame p E G H P d U Q A B (F N f)).hom ≫
            (regularPullback E G (positiveSchemeMap p E d U Q Q' r R)).hom

variable (T : CompletionRefinement p E d U Q Q' r R G H P V A B A' B' F F')
  (h : IsUnit (sectionMap p E Q.puncture.map Q.parameter))
  (h' : IsUnit (sectionMap p E Q'.puncture.map Q'.parameter))
  (C : MeromorphicTorsorCompletion.CompletionComparison p E G H P d U Q A B F h)
  (C' : MeromorphicTorsorCompletion.CompletionComparison p E G H P d U Q' A' B' F' h')

/-- The actual Hecke refinement has the same prescribed unframed base-change maps as legs. -/
structure HeckeRefinement where
  comparison : globalToLocal p E G H P d U Q A B F h C ⋙
    localReindex p E d U Q Q' r R G V S ≅ globalToLocal p E G H P d U Q' A' B' F' h' C'
  left : ∀ M : Hecke p E G H P d U,
    (localLeftLeg p E G d U Q').map (comparison.hom.app M) =
      T.comparison.hom.app ((MeromorphicHeckeModels.leftLeg p E G H P d U).obj M)
  right : ∀ M : Hecke p E G H P d U,
    (localRightLeg p E G d U Q').map (comparison.hom.app M) =
      T.comparison.hom.app ((MeromorphicHeckeModels.rightLeg p E G H P d U).obj M)

end MathlibExt.AlgebraicGeometry.MeromorphicCompletionRefinements
