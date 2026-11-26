/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralBorelAbelianizationCore
public import MathlibExt.AlgebraicGeometry.CameralRawAbelianizationData
public import MathlibExt.AlgebraicGeometry.CameralAdmissibleTorusBundles

/-!
# Raw Borel ramification lift on the actual fibre functor

Objects and arrows below use the original marked Borel reduction and its
native B-to-T pushout. The lift retains all coefficient-scheme gamma and
beta maps and the two native ramification diagrams. Arrows preserve them
through the actual underlying functor. The pinned adapter supplies the
standard admissible object while keeping that same torus bundle.

Source: Donagi--Gaitsgory, arXiv:math/0005132v3, Sections6.2/16.1.
Geometric construction and universal pullback normalization are separate
source contracts; the equivalence theorem is not an input to this lift.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralBorelLiftModels

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonObj
open CameralFoundationPackages CameralRootSL2Sources CameralRamificationReindexing
open CameralRamificationTensorModels CameralRamificationTorsorReindexing
open CameralRamificationCocycles CameralCharacterRealizations CameralSimpleRootTrivializations
open CameralNormalizerShifts CameralLiftedNormalizerModels CameralLiftedRamificationData
open CameralCoverDescentModels CameralBorelReductionModels CameralBorelAbelianizationCore
open CameralRawAbelianizationData CameralChevalleyConventionModels ExpansionParameterModels
open ContractedTorsorModels

variable {G : Over (Spec (.of ℂ))} [GrpObj G] {tori : ∀ n : ℕ, TorusTheory ℂ n}
  (F : Foundation G tori) [GeneralLinearFrameSchemes.FrameTheory 2]
  [RankTwoMatrixGroupModels.GL2MatrixTheory] [RankTwoMatrixGroupModels.SL2MatrixTheory]
  (K : RootNormalizerGeometry G tori F) (D : RootTorsorInputs F K)
  (R : CanonicalRamificationFamily F K D) (A : CharacterCalculus F K D)
  (Q : SimpleReflectionTorsors F K D R) (E : RootWeylGeometry F K)
  (T : CanonicalSimpleRootTrivializations F K D R A)
  (I : IncidenceAction F) (BB : BorelGeometry F)
  {X : Over (Spec (.of ℂ))} {C : Cover F X} (B : ParameterCovers F C)
  (N : ReductionFamily F BB I C) (O : BorelTorusOperations F BB)

attribute [local instance] CameralRamificationTensorModels.torusGroup

/-- The underlying functor is the actual marked Borel quotient and its maps. -/
abbrev underlying : CameralBorelAbelianizationCore.Marked F I C ⥤
    Bundle (Torus F) (total F C) := rawBorelFunctor F BB I C N O

/-- The raw data live on precisely the actual Borel functor value. -/
structure RawObjectData (H : CameralBorelAbelianizationCore.Marked F I C) where
  shift : RawNormalizerShift F K D R B ((underlying F I BB N O).obj H)
  beta : RawBetaMaps F K D R A B ((underlying F I BB N O).obj H)
  compatibility : RawBetaCompatibility F K D R A B ((underlying F I BB N O).obj H)
    beta shift Q E T

/-- Every marked-regularizer arrow preserves the same actual raw family maps. -/
structure RawLiftFamily where
  object : ∀ H : CameralBorelAbelianizationCore.Marked F I C,
    RawObjectData F K D R A Q E T I BB B N O H
  gamma : ∀ {H H' : CameralBorelAbelianizationCore.Marked F I C} (f : H ⟶ H')
      (U : Over (Spec (.of ℂ))) (n : U ⟶ F.normalizer.scheme) (w : F.Weyl)
      (hn : Label F n w),
    (shiftFunctor F K D (B.pulled U).cover w).map
      (CameralAdmissibleTorusBundles.parameterMap F K D B
        ((underlying F I BB N O).map f) U) ≫ ((object H').shift.gamma U n w hn).hom =
    ((object H).shift.gamma U n w hn).hom ≫
      CameralAdmissibleTorusBundles.parameterMap F K D B ((underlying F I BB N O).map f) U
  beta : ∀ {H H' : CameralBorelAbelianizationCore.Marked F I C} (f : H ⟶ H')
      (U : Over (Spec (.of ℂ))) (i : Fin F.roots.count) (hi : SimpleRoot G tori F i)
      (c : U ⟶ torusScheme ℂ 1),
    ((object H).beta.beta U i hi c).hom =
      (Scheme.Modules.pullback (fixedInclusion F (B.pulled U).cover i).left).map
        ((A.line (total F (B.pulled U).cover) i).map
          (CameralAdmissibleTorusBundles.parameterMap F K D B
            ((underlying F I BB N O).map f) U)) ≫ ((object H').beta.beta U i hi c).hom

variable (L : RawLiftFamily F K D R A Q E T I BB B N O)
  (Θ : ChevalleyComparison F K)

/-- The adapted data retain the same source bundle and the exact pinned formulas. -/
structure AdaptedLiftFamily where
  object : ∀ H : CameralBorelAbelianizationCore.Marked F I C,
    AdaptedRamificationData F K D R A B ((underlying F I BB N O).obj H)
      (L.object H).beta (L.object H).shift Q E T Θ (L.object H).compatibility

variable (V : AdaptedLiftFamily F K D R A Q E T I BB B N O L Θ)

/-- The concrete output object has the same native raw Borel torus bundle. -/
def admissibleObject (H : CameralBorelAbelianizationCore.Marked F I C) :
    CameralAdmissibleTorusBundles.Object F K D R A B Q E T where
  bundle := (underlying F I BB N O).obj H
  shift := (V.object H).shift
  full := (V.object H).full
  beta := (V.object H).beta
  compatibility := (V.object H).compatibility

/-- Adapted arrow preservation follows by the actual normalizer and Gm precompositions. -/
def admissibleArrow {H H' : CameralBorelAbelianizationCore.Marked F I C} (f : H ⟶ H') :
    CameralAdmissibleTorusBundles.Hom F K D R A B Q E T
      (admissibleObject F K D R A Q E T I BB B N O L Θ V H)
      (admissibleObject F K D R A Q E T I BB B N O L Θ V H') where
  map := (underlying F I BB N O).map f
  gamma U n w hn := by
    change _ ≫ ((V.object H').shift.gamma U n w hn).hom =
      ((V.object H).shift.gamma U n w hn).hom ≫ _
    rw [(V.object H').gamma_normalized, (V.object H).gamma_normalized]
    exact L.gamma f U (n ≫ Θ.normalizer.hom) w (thetaLabel F K Θ n w hn)
  beta U i hi c := by
    change ((V.object H).beta.beta U i hi c).hom = _ ≫
      ((V.object H').beta.beta U i hi c).hom
    rw [(V.object H).beta_normalized, (V.object H').beta_normalized]
    let := (tori 1).group
    exact L.beta f U i hi (c ≫ ι[torusScheme ℂ 1])

/-- The source-normalized fibre functor is the actual Borel functor on objects and arrows. -/
def admissibleFunctor : CameralBorelAbelianizationCore.Marked F I C ⥤
    CameralAdmissibleTorusBundles.Object F K D R A B Q E T where
  obj := admissibleObject F K D R A Q E T I BB B N O L Θ V
  map := admissibleArrow F K D R A Q E T I BB B N O L Θ V
  map_id H := by
    apply CameralAdmissibleTorusBundles.Hom.ext
    exact (underlying F I BB N O).map_id H
  map_comp f g := by
    apply CameralAdmissibleTorusBundles.Hom.ext
    exact (underlying F I BB N O).map_comp f g

/-- Its whole underlying object and arrow functor is literal native Borel abelianization. -/
theorem admissibleFunctor_underlying :
    admissibleFunctor F K D R A Q E T I BB B N O L Θ V ⋙
      CameralAdmissibleTorusBundles.forget F K D R A B Q E T = underlying F I BB N O := rfl

end MathlibExt.AlgebraicGeometry.CameralBorelLiftModels
