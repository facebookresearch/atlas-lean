/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralUniversalRegularizerModels

/-!
# Universal raw Borel data and all-family G descent

The source data are over the actual universal regularizer.
Its Cartan-open restriction is fixed by inverse N multiplication and
the actual canonical ramification-section units. Every family lift is
compared, on the original G torsor, with that universal object through
sigma and the actual G action relation. Both comparisons fix every
B-to-T quotient point, gamma and beta. No arbitrary family is assumed
reduced, or to have a nonempty dense unramified locus. Canonical beta is
additionally fixed by CameralIsogenyBetaModels.NormalizedUniversal.
Source: DG math/0005132v3, Sections7.2/8.1/15/16.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralUniversalRawLiftModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open CameralFoundationPackages CameralRootSL2Sources CameralRamificationReindexing
open CameralRamificationTensorModels CameralRamificationTorsorReindexing
open CameralRamificationCocycles CameralCharacterRealizations CameralSimpleRootTrivializations
open CameralNormalizerShifts CameralLiftedNormalizerModels CameralLiftedRamificationData
open CameralCoverDescentModels CameralBorelReductionModels CameralBorelAbelianizationCore
open CameralRawAbelianizationData CameralBorelLiftModels
open CameralBorelUnramifiedNormalization CameralUnramifiedNormalizerModels
open CameralUniversalRegularizerModels CameralRawLiftPullbackModels
open CameralRegularizedHiggsModels GroupTorsorGeometry
open ContractedTorsorModels NormalizedTorsorOperations ExpansionParameterModels

variable {G : Over (Spec (.of ℂ))} [GrpObj G]
  {tori : ∀ n : ℕ, TorusTheory ℂ n} (F : Foundation G tori)
  [GeneralLinearFrameSchemes.FrameTheory 2]
  [RankTwoMatrixGroupModels.GL2MatrixTheory] [RankTwoMatrixGroupModels.SL2MatrixTheory]
  (K : RootNormalizerGeometry G tori F) (D : RootTorsorInputs F K)
  (R : CanonicalRamificationFamily F K D) (A : CharacterCalculus F K D)
  (Q : SimpleReflectionTorsors F K D R) (E : RootWeylGeometry F K)
  (T : CanonicalSimpleRootTrivializations F K D R A)
  (I : IncidenceAction F) (BB : BorelGeometry F)

attribute [local instance] CameralRamificationTensorModels.torusGroup
attribute [local instance] CameralRegularizedHiggsModels.centralizerGroupAction
attribute [local instance] CameralUnramifiedNormalizerModels.normalizerGroup
attribute [local instance] CameralBorelReductionModels.borelGroup
attribute [local instance] CameralBorelReductionModels.quotientHom

structure LiftInputs where
  parameter : ∀ {X : Over (Spec (.of ℂ))} (C : Cover F X), ParameterCovers F C
  reduction : ∀ {X : Over (Spec (.of ℂ))} (C : Cover F X), ReductionFamily F BB I C
  operation : BorelTorusOperations F BB

variable (V : LiftInputs F I BB)

abbrev ObjectData {X : Over (Spec (.of ℂ))} {C : Cover F X} (H : Marked F I C) :=
  RawObjectData F K D R A Q E T I BB (V.parameter C) (V.reduction C) V.operation H

abbrev FamilyData {X : Over (Spec (.of ℂ))} (C : Cover F X) :=
  RawLiftFamily F K D R A Q E T I BB (V.parameter C) (V.reduction C) V.operation

structure MarkedPullback {X Y : Over (Spec (.of ℂ))} {C : Cover F X}
    (H : Marked F I C) (f : Y ⟶ X) (r : Reindex G H.regularizer.torsor f)
    (P : CameralBaseChange F C f) where
  descent : CoverDescent F I (reindexObject G F.centralizers.scheme H.regularizer f r)
  marking : P.cover.cover.scheme ≅ descent.cameral.cover.scheme
  weyl : ∀ w, (P.cover.cover.action w).asIso.hom ≫ marking.hom =
    marking.hom ≫ (descent.cameral.cover.action w).asIso.hom

def MarkedPullback.object {X Y : Over (Spec (.of ℂ))} {C : Cover F X}
    {H : Marked F I C} {f : Y ⟶ X} {r : Reindex G H.regularizer.torsor f}
    {P : CameralBaseChange F C f} (M : MarkedPullback F I H f r P) :
    Marked F I P.cover where
  regularizer := reindexObject G F.centralizers.scheme H.regularizer f r
  descent := M.descent
  marking := M.marking
  weyl := M.weyl

def familyIncidence {X : Over (Spec (.of ℂ))} {C : Cover F X}
    (H : Marked F I C) (P : CameralBaseChange F C H.regularizer.torsor.projection) :
    total F P.cover ⟶ universalTotal F I :=
  CameralMarkedRegularizers.incidencePoint F I C H (total F P.cover)
    P.arrow.total (projection F P.cover) (by
      simpa only [P.base] using P.arrow.projection.symm)

structure OpenSource (U : UniversalRegularizer F I) where
  cartan : CartanPoint F
  isOpen : CartanOpen F cartan
  torsor : Reindex G (U.object F I).regularizer.torsor
    (cartanOpenInclusion F cartan isOpen)
  cover : CameralBaseChange F I.incidence.cameral (cartanOpenInclusion F cartan isOpen)
  marked : MarkedPullback F I (U.object F I)
    (cartanOpenInclusion F cartan isOpen) torsor cover
  along : RegularizerAlong F I cover.arrow (marked.object F I) (U.object F I)
  original : along.original = torsor.original G
  normalizer : NormalizerReduction F I cover.cover (marked.object F I) cartan
  quotient : TorusNormalizerCover F I cover.cover (marked.object F I) cartan normalizer
  comparison : BorelNormalizerComparison F BB I cover.cover (marked.object F I)
    cartan normalizer (V.reduction cover.cover) V.operation quotient

variable {X : Over (Spec (.of ℂ))} {C : Cover F X} (H : Marked F I C)
  (Z : CartanPoint F) (N : NormalizerReduction F I C H Z)
  (NC : TorusNormalizerCover F I C H Z N)
  (J : BorelNormalizerComparison F BB I C H Z N (V.reduction C) V.operation NC)
  (S : ObjectData F K D R A Q E T I BB V H)

/-- The open raw transport uses the original inverse-N action on every test. -/
structure OriginalUnramifiedGamma where
  frames : ∀ U : Over (Spec (.of ℂ)), SectionFrames F ((V.parameter C).pulled U).cover
  gamma : ∀ (U : Over (Spec (.of ℂ))) (n : U ⟶ F.normalizer.scheme)
      (w : F.Weyl) (hn : Label F n w) (W : Over (Spec (.of ℂ)))
      (y : W ⟶ total F ((V.parameter C).pulled U).cover)
      (q : W ⟶ (combined F K D ((V.parameter C).pulled U).cover w
        (parameterBundle F K D (V.parameter C) ((underlying F I BB
          (V.reduction C) V.operation).obj H) U)).torsor.total)
      (hq : q ≫ (combined F K D ((V.parameter C).pulled U).cover w
          (parameterBundle F K D (V.parameter C) ((underlying F I BB
            (V.reduction C) V.operation).obj H) U)).torsor.projection =
        (y ≫ (ramificationPoint F K D (frames U) w).val) ≫
          (ramificationTorsor F K D ((V.parameter C).pulled U).cover w).torsor.projection),
    tensorPoint (D.torus.tensor.model (total F ((V.parameter C).pulled U).cover)
      (combined F K D ((V.parameter C).pulled U).cover w
        (parameterBundle F K D (V.parameter C) ((underlying F I BB
          (V.reduction C) V.operation).obj H) U))
      (ramificationTorsor F K D ((V.parameter C).pulled U).cover w))
      q (y ≫ (ramificationPoint F K D (frames U) w).val) hq ≫
        (S.shift.gamma U n w hn).hom.iso.hom ≫
        parameterOriginalN F K D I BB (V.parameter C) (V.reduction C)
          V.operation H Z N NC J U =
    CartesianMonoidalCategory.lift
      (y ≫ parameterProjection F (V.parameter C) U ≫ n ≫ ι[F.normalizer.scheme])
      (q ≫ combinedOriginal F K D ((V.parameter C).pulled U).cover
        ((R.weyl ((V.parameter C).pulled U).cover).model w
          (parameterBundle F K D (V.parameter C) ((underlying F I BB
            (V.reduction C) V.operation).obj H) U)) ≫
        parameterOriginalN F K D I BB (V.parameter C) (V.reduction C)
          V.operation H Z N NC J U) ≫ N.torsor.action.smul

structure UniversalRawConstruction (U : UniversalRegularizer F I) where
  data : ObjectData F K D R A Q E T I BB V (U.object F I)
  openSource : OpenSource F I BB V U
  openData : ObjectData F K D R A Q E T I BB V (openSource.marked.object F I)
  quotient : BorelTorusPullback F K D I BB openSource.cover.arrow
    (openSource.marked.object F I) (U.object F I) openSource.along
    (V.reduction openSource.cover.cover) (V.reduction I.incidence.cameral) V.operation
  parameter : ParameterAlong F openSource.cover.arrow
    (V.parameter openSource.cover.cover) (V.parameter I.incidence.cameral)
  restriction : RawDataPullback F K D R A parameter quotient.comparison
    openData.shift data.shift openData.beta data.beta
  originalGamma : OriginalUnramifiedGamma F K D R A Q E T I BB V
    (openSource.marked.object F I) openSource.cartan openSource.normalizer
    openSource.quotient openSource.comparison openData

structure FamilySource (U : UniversalRegularizer F I) {X : Over (Spec (.of ℂ))}
    {C : Cover F X} (H : Marked F I C) where
  action : OriginalActionComparison F I U H
  cover : CameralBaseChange F C H.regularizer.torsor.projection
  marked : MarkedPullback F I H H.regularizer.torsor.projection action.original cover
  original : RegularizerAlong F I cover.arrow (marked.object F I) H
  original_normalized : original.original = action.original.original G
  sigmaArrow : CameralArrow F cover.cover I.incidence.cameral
  sigma_base : sigmaArrow.base = H.regularizer.map
  sigma_incidence : sigmaArrow.total = familyIncidence F I H cover
  universal : RegularizerAlong F I sigmaArrow (marked.object F I) (U.object F I)
  universal_normalized : universal.original = action.iso.inv.iso.hom ≫
    action.universal.original G

/-- The family lift descends the specified universal raw data through the original G torsor. -/
structure AllFamilyRawConstruction (U : UniversalRegularizer F I)
    (W : UniversalRawConstruction F K D R A Q E T I BB V U) where
  family : ∀ {X : Over (Spec (.of ℂ))} (C : Cover F X), FamilyData F K D R A Q E T I BB V C
  universal : (family I.incidence.cameral).object (U.object F I) = W.data
  source : ∀ {X : Over (Spec (.of ℂ))} {C : Cover F X} (H : Marked F I C),
    FamilySource F I U H
  originalQuotient : ∀ {X : Over (Spec (.of ℂ))} {C : Cover F X} (H : Marked F I C),
    BorelTorusPullback F K D I BB (source H).cover.arrow
      ((source H).marked.object F I) H (source H).original
      (V.reduction (source H).cover.cover) (V.reduction C) V.operation
  originalParameter : ∀ {X : Over (Spec (.of ℂ))} {C : Cover F X} (H : Marked F I C),
    ParameterAlong F (source H).cover.arrow
      (V.parameter (source H).cover.cover) (V.parameter C)
  originalData : ∀ {X : Over (Spec (.of ℂ))} {C : Cover F X} (H : Marked F I C),
    RawDataPullback F K D R A (originalParameter H) (originalQuotient H).comparison
      ((family (source H).cover.cover).object ((source H).marked.object F I)).shift
      ((family C).object H).shift
      ((family (source H).cover.cover).object ((source H).marked.object F I)).beta
      ((family C).object H).beta
  universalQuotient : ∀ {X : Over (Spec (.of ℂ))} {C : Cover F X} (H : Marked F I C),
    BorelTorusPullback F K D I BB (source H).sigmaArrow
      ((source H).marked.object F I) (U.object F I) (source H).universal
      (V.reduction (source H).cover.cover) (V.reduction I.incidence.cameral) V.operation
  universalParameter : ∀ {X : Over (Spec (.of ℂ))} {C : Cover F X} (H : Marked F I C),
    ParameterAlong F (source H).sigmaArrow
      (V.parameter (source H).cover.cover) (V.parameter I.incidence.cameral)
  universalData : ∀ {X : Over (Spec (.of ℂ))} {C : Cover F X} (H : Marked F I C),
    RawDataPullback F K D R A (universalParameter H) (universalQuotient H).comparison
      ((family (source H).cover.cover).object ((source H).marked.object F I)).shift
      W.data.shift
      ((family (source H).cover.cover).object ((source H).marked.object F I)).beta
      W.data.beta
  baseQuotient : ∀ {X Y : Over (Spec (.of ℂ))} {C : Cover F X} {C' : Cover F Y}
      (m : CameralArrow F C C') (H : Marked F I C) (H' : Marked F I C')
      (a : RegularizerAlong F I m H H'),
    BorelTorusPullback F K D I BB m H H' a (V.reduction C) (V.reduction C') V.operation
  baseParameter : ∀ {X Y : Over (Spec (.of ℂ))} {C : Cover F X} {C' : Cover F Y}
      (m : CameralArrow F C C'), ParameterAlong F m (V.parameter C) (V.parameter C')
  baseData : ∀ {X Y : Over (Spec (.of ℂ))} {C : Cover F X} {C' : Cover F Y}
      (m : CameralArrow F C C') (H : Marked F I C) (H' : Marked F I C')
      (a : RegularizerAlong F I m H H'),
    RawDataPullback F K D R A (baseParameter m) (baseQuotient m H H' a).comparison
      ((family C).object H).shift ((family C').object H').shift
      ((family C).object H).beta ((family C').object H').beta
  base_unit : ∀ {X : Over (Spec (.of ℂ))} {C : Cover F X}
      (m : CameralArrow F C C) (H : Marked F I C) (a : RegularizerAlong F I m H H)
      (_hm : m.total = 𝟙 (total F C)) (_ha : a.original = 𝟙 H.regularizer.torsor.total),
    (baseQuotient m H H a).borelOriginal = 𝟙 ((V.reduction C).object H).torsor.total
  base_composition : ∀ {X₀ X₁ X₂ : Over (Spec (.of ℂ))}
      {C₀ : Cover F X₀} {C₁ : Cover F X₁} {C₂ : Cover F X₂}
      (m : CameralArrow F C₀ C₁) (n : CameralArrow F C₁ C₂) (p : CameralArrow F C₀ C₂)
      (H₀ : Marked F I C₀) (H₁ : Marked F I C₁) (H₂ : Marked F I C₂)
      (a : RegularizerAlong F I m H₀ H₁) (b : RegularizerAlong F I n H₁ H₂)
      (c : RegularizerAlong F I p H₀ H₂)
      (_hm : p.total = m.total ≫ n.total) (_ha : c.original = a.original ≫ b.original),
    (baseQuotient p H₀ H₂ c).borelOriginal =
      (baseQuotient m H₀ H₁ a).borelOriginal ≫ (baseQuotient n H₁ H₂ b).borelOriginal
  parameter_unit : ∀ {X : Over (Spec (.of ℂ))} {C : Cover F X}
      (m : CameralArrow F C C) (_hm : m.total = 𝟙 (total F C)) (Z : Over (Spec (.of ℂ))),
    ((baseParameter m).arrow Z).total = 𝟙 (total F ((V.parameter C).pulled Z).cover)
  parameter_composition : ∀ {X₀ X₁ X₂ : Over (Spec (.of ℂ))}
      {C₀ : Cover F X₀} {C₁ : Cover F X₁} {C₂ : Cover F X₂}
      (m : CameralArrow F C₀ C₁) (n : CameralArrow F C₁ C₂) (p : CameralArrow F C₀ C₂)
      (_hm : p.total = m.total ≫ n.total) (Z : Over (Spec (.of ℂ))),
    ((baseParameter p).arrow Z).total =
      ((baseParameter m).arrow Z).total ≫ ((baseParameter n).arrow Z).total

end MathlibExt.AlgebraicGeometry.CameralUniversalRawLiftModels
