/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralBorelLiftModels
public import MathlibExt.AlgebraicGeometry.CameralUnramifiedNormalizerModels

/-!
# Original unramified normalizer action on the raw Borel lift

The ramification unit is computed from the actual canonical divisor
sections and their root-coroot pushouts. Normalizer transport is fixed
on every scheme-valued torsor point by the original inverse N action.
The Borel/N comparison is the original quotient-point comparison.
No density assertion is imposed on an arbitrary family.
Source: Donagi--Gaitsgory math/0005132v3, Sections7.2/8.1/16.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralBorelUnramifiedNormalization

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj
open CameralFoundationPackages CameralRootSL2Sources CameralRamificationReindexing
open CameralRamificationTensorModels CameralRamificationTorsorReindexing
open CameralRamificationCocycles CameralCharacterRealizations CameralSimpleRootTrivializations
open CameralNormalizerShifts CameralLiftedNormalizerModels CameralLiftedRamificationData
open CameralCoverDescentModels CameralBorelReductionModels CameralBorelAbelianizationCore
open CameralBorelLiftModels CameralRawAbelianizationData CameralUnramifiedNormalizerModels
open ExpansionParameterModels ContractedTorsorModels TorusLineFrameModels
open CoherentCurveLinearSeries LineBundleTaskContracts

variable {G : Over (Spec (.of ℂ))} [GrpObj G] {tori : ∀ n : ℕ, TorusTheory ℂ n}
  (F : Foundation G tori) [GeneralLinearFrameSchemes.FrameTheory 2]
  [RankTwoMatrixGroupModels.GL2MatrixTheory] [RankTwoMatrixGroupModels.SL2MatrixTheory]
  (K : RootNormalizerGeometry G tori F) (D : RootTorsorInputs F K)

attribute [local instance] CameralRamificationTensorModels.torusGroup
attribute [local instance] CameralUnramifiedNormalizerModels.normalizerGroup

/-- The frame is the actual canonical ramification section on the whole unramified cover. -/
structure SectionFrames {X : Over (Spec (.of ℂ))} (C : Cover F X) where
  point : letI := (tori 1).group
    ∀ i : Fin F.roots.count, total F C ⟶ (frames F C i).bundle.torsor.total
  over : letI := (tori 1).group
    ∀ i, point i ≫ (frames F C i).bundle.torsor.projection = 𝟙 (total F C)
  section_normalized : letI := (tori 1).group
    ∀ i, (frameBasis (tori 1) (total F C) (line F C i) (frames F C i)
      (total F C) (𝟙 _) (point i) (over i)).hom =
      pullbackSection (𝟙 (total F C).left) (sectionData F C i).sectionMap

set_option maxHeartbeats 1000000 in
-- Building the root-coroot quotient point from the section frames needs extra budget.
/-- The original root-coroot quotient point associated with that section. -/
def rootPoint {X : Over (Spec (.of ℂ))} {C : Cover F X} (S : SectionFrames F C)
    (i : Fin F.roots.count) : TorsorPoint F (rootTorsor F K D C i) (𝟙 (total F C)) := by
  letI := (tori 1).group
  letI := K.corootHom i
  refine ⟨CartesianMonoidalCategory.lift (S.point i)
    (toUnit (total F C) ≫ η[Torus F]) ≫ (rootPushout F K D C i).quotient, ?_⟩
  rw [Category.assoc, (rootPushout F K D C i).projection, ← Category.assoc,
    CartesianMonoidalCategory.lift_fst, S.over i]

/-- Every product uses the native tensor quotient point, in its actual order. -/
def productPoint {X : Over (Spec (.of ℂ))} {C : Cover F X} (S : SectionFrames F C) :
    ∀ is : List (Fin F.roots.count),
      TorsorPoint F (ramificationProduct F K D C is) (𝟙 (total F C))
  | [] => ⟨NormalizedTorsorOperations.unitPoint (Torus F) (D.torus.unit (total F C)) (𝟙 _),
      NormalizedTorsorOperations.unitPoint_over _ _ _⟩
  | i :: is => by
    let p := rootPoint F K D S i
    let q := productPoint S is
    refine ⟨tensorPoint (D.torus.tensor.model (total F C)
      (rootTorsor F K D C i) (ramificationProduct F K D C is)) p.val q.val
        (p.property.trans q.property.symm), ?_⟩
    exact (tensorPoint_over _ _ _ _).trans p.property

/-- The actual R_w unit on this unramified cover. -/
def ramificationPoint {X : Over (Spec (.of ℂ))} {C : Cover F X}
    (S : SectionFrames F C) (w : F.Weyl) :
    TorsorPoint F (ramificationTorsor F K D C w) (𝟙 (total F C)) :=
  productPoint F K D S (inversionRoots F K w)

variable (R : CanonicalRamificationFamily F K D) (A : CharacterCalculus F K D)
  (Q : SimpleReflectionTorsors F K D R) (E : RootWeylGeometry F K)
  (T : CanonicalSimpleRootTrivializations F K D R A)
  (I : IncidenceAction F) (BB : BorelGeometry F)
  {X : Over (Spec (.of ℂ))} {C : Cover F X} (B : ParameterCovers F C)
  (NR : ReductionFamily F BB I C) (O : BorelTorusOperations F BB)
  (L : RawLiftFamily F K D R A Q E T I BB B NR O)
  (H : CameralBorelAbelianizationCore.Marked F I C) (Z : CartanPoint F)
  (N : NormalizerReduction F I C H Z) (NC : TorusNormalizerCover F I C H Z N)
  (J : BorelNormalizerComparison F BB I C H Z N NR O NC)

/-- Every parameter bundle uses its actual native original-to-Borel-to-N point map. -/
def parameterOriginalN (U : Over (Spec (.of ℂ))) :
    (parameterBundle F K D B ((underlying F I BB NR O).obj H) U).torsor.total ⟶ N.torsor.total :=
  original (D.torus.baseChange.pullback (B.pulled U).arrow.total
    ((underlying F I BB NR O).obj H)) ≫ J.comparison.hom.iso.hom ≫ NC.identification.hom

/-- Raw transport is exactly inverse N multiplication after the canonical R_w unit. -/
structure UnramifiedNormalization where
  frames : ∀ U : Over (Spec (.of ℂ)), SectionFrames F (B.pulled U).cover
  gamma : ∀ (U : Over (Spec (.of ℂ))) (n : U ⟶ F.normalizer.scheme)
      (w : F.Weyl) (hn : Label F n w) (V : Over (Spec (.of ℂ)))
      (y : V ⟶ total F (B.pulled U).cover)
      (q : V ⟶ (combined F K D (B.pulled U).cover w
        (parameterBundle F K D B ((underlying F I BB NR O).obj H) U)).torsor.total)
      (hqr : q ≫ (combined F K D (B.pulled U).cover w
        (parameterBundle F K D B ((underlying F I BB NR O).obj H) U)).torsor.projection =
        (y ≫ (ramificationPoint F K D (frames U) w).val) ≫
          (ramificationTorsor F K D (B.pulled U).cover w).torsor.projection),
    tensorPoint (D.torus.tensor.model (total F (B.pulled U).cover)
      (combined F K D (B.pulled U).cover w
        (parameterBundle F K D B ((underlying F I BB NR O).obj H) U))
      (ramificationTorsor F K D (B.pulled U).cover w))
      q (y ≫ (ramificationPoint F K D (frames U) w).val) hqr ≫
      ((L.object H).shift.gamma U n w hn).hom.iso.hom ≫
        parameterOriginalN F K D I BB B NR O H Z N NC J U =
    CartesianMonoidalCategory.lift
      (y ≫ parameterProjection F B U ≫ n ≫ ι[F.normalizer.scheme])
      (q ≫ combinedOriginal F K D (B.pulled U).cover
        ((R.weyl (B.pulled U).cover).model w
          (parameterBundle F K D B ((underlying F I BB NR O).obj H) U)) ≫
          parameterOriginalN F K D I BB B NR O H Z N NC J U) ≫
      N.torsor.action.smul

end MathlibExt.AlgebraicGeometry.CameralBorelUnramifiedNormalization
