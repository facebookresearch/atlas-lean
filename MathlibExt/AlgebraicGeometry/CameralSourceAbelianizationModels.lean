/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralIsogenyBetaModels
public import MathlibExt.AlgebraicGeometry.CameralHitchinFunctorModels

/-!
# The source-normalized Borel and regularized Hitchin fibre functors

The universal raw source has the actual central-isogeny beta port.
All families use its native sigma pullback and all B-to-T quotients,
with every base change and parameter arrow retained. The pinned
Chevalley adapter keeps that same bundle and the same R data.
The functors below are computed from those source maps. Source
equivalence theorems target these functors; no independent equivalence
or unrelated Cartan vector-bundle isomorphism is an input.
Source: DG math/0005132v3, Theorems6.4/17.5 and Corollary17.8.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralSourceAbelianizationModels

open _root_.CategoryTheory _root_.AlgebraicGeometry
open CameralFoundationPackages CameralRootSL2Sources CameralRamificationReindexing
open CameralRamificationTensorModels CameralRamificationCocycles CameralCharacterRealizations
open CameralSimpleRootTrivializations CameralLiftedNormalizerModels CameralNormalizerShifts
open CameralCoverDescentModels CameralBorelReductionModels CameralBorelAbelianizationCore
open CameralBorelLiftModels CameralIsogenyBetaModels CameralUniversalRawLiftModels
open CameralUniversalRegularizerModels CameralChevalleyConventionModels
open CameralRegularizedHiggsModels CameralHiggsCategoryModels CameralCartanValueModels
open CameralHitchinFunctorModels ExpansionParameterModels ContractedTorsorModels

variable {G : Over (Spec (.of ℂ))} [GrpObj G]
  {tori : ∀ n : ℕ, TorusTheory ℂ n} (F : Foundation G tori)
  [GeneralLinearFrameSchemes.FrameTheory 2]
  [RankTwoMatrixGroupModels.GL2MatrixTheory] [RankTwoMatrixGroupModels.SL2MatrixTheory]
  (K : RootNormalizerGeometry G tori F) (D : RootTorsorInputs F K)
  (R : CanonicalRamificationFamily F K D) (A : CharacterCalculus F K D)
  (Q : SimpleReflectionTorsors F K D R) (E : RootWeylGeometry F K)
  (T : CanonicalSimpleRootTrivializations F K D R A)
  (I : IncidenceAction F) (B : BorelGeometry F) (V : LiftInputs F I B)
  (U : UniversalRegularizer F I)
  (W : NormalizedUniversal F K D R A Q E T I B V U)

attribute [local instance] CameralRegularizedHiggsModels.centralizerGroupAction

structure SourceConstruction where
  raw : AllFamilyRawConstruction F K D R A Q E T I B V U W.raw
  chevalley : ChevalleyComparison F K
  adapted : ∀ {X : Over (Spec (.of ℂ))} (C : Cover F X),
    AdaptedLiftFamily F K D R A Q E T I B (V.parameter C) (V.reduction C) V.operation
      (raw.family C) chevalley

variable (S : SourceConstruction F K D R A Q E T I B V U W)

/-- Every object and arrow is the actual marked Borel quotient with the pinned adapter. -/
def borelFunctor {X : Over (Spec (.of ℂ))} (C : Cover F X) : Marked F I C ⥤
    CameralAdmissibleTorusBundles.Object F K D R A (V.parameter C) Q E T :=
  admissibleFunctor F K D R A Q E T I B (V.parameter C) (V.reduction C) V.operation
    (S.raw.family C) S.chevalley (S.adapted C)

theorem borelFunctor_underlying {X : Over (Spec (.of ℂ))} (C : Cover F X) :
    borelFunctor F K D R A Q E T I B V U W S C ⋙
      CameralAdmissibleTorusBundles.forget F K D R A (V.parameter C) Q E T =
    rawBorelFunctor F B I C (V.reduction C) V.operation := rfl

variable {X : Over (Spec (.of ℂ))} (L : TwistLine X)
  (Space : SectionSpace X (cartanKModule F X L)) (Action : CartanWeylAction F X L Space)
  (Coherence : CategoryCoherence F (X := X) (K := L)) (b : ValueObject F L Space Action)

/-- The actual marked value fibre uses precisely the same source Borel functor. -/
def regularizedFibreFunctor (P : FibreArrowCoherence F I L Space Action b) :
    letI := fibreCategory F I L Space Action Coherence b
    FibreObject F I L Space Action b ⥤
      CameralAdmissibleTorusBundles.Object F K D R A (V.parameter b.cover) Q E T :=
  admissibleFibreFunctor F I L Space Action Coherence K D R A Q E T B b
    (V.parameter b.cover) (V.reduction b.cover) V.operation (S.raw.family b.cover)
    S.chevalley (S.adapted b.cover) P

end MathlibExt.AlgebraicGeometry.CameralSourceAbelianizationModels
