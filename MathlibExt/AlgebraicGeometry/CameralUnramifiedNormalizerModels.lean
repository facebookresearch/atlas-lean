/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralBorelAbelianizationCore
public import MathlibExt.AlgebraicGeometry.CameralRawAbelianizationData

/-!
# Actual unramified N reductions and Borel comparisons

The N reduction is the actual fibre of sigma at the embedded Cartan
centralizer. Its T quotient is the marked cameral cover, with its native
normalizer deck action. The comparison to the raw Borel torus bundle is
fixed on every actual B-to-T quotient point. This supplies the concrete
unramified normalization for inverse raw gamma on all test schemes.
Source: DG arXiv:math/0005132v3, Sections 7.2 and 8.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralUnramifiedNormalizerModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj
open CameralFoundationPackages CameralRootSL2Sources CameralRamificationReindexing
open CameralIncidenceModels
open CameralRamificationTensorModels CameralRamificationTorsorReindexing
open CameralRegularizedHiggsModels CameralCoverDescentModels CameralBorelReductionModels
open CameralBorelAbelianizationCore CameralNormalizerShifts CameralMarkedRegularizers
open GroupTorsorGeometry SchemeLieJetFamilies ExpansionParameterModels
open ContractedTorsorModels CoherentCurveLinearSeries LineBundleTaskContracts TorusLineFrameModels

variable {G : Over (Spec (.of ℂ))} [GrpObj G] {tori : ∀ n : ℕ, TorusTheory ℂ n}
  (F : Foundation G tori)

attribute [local instance] CameralRegularizedHiggsModels.centralizerGroupAction
attribute [local instance] CameralRamificationTensorModels.torusGroup

@[instance_reducible] def normalizerGroup : GrpObj F.normalizer.scheme := F.normalizer.group
attribute [local instance] normalizerGroup

structure CartanPoint where
  point : 𝟙_ (Over (Spec (.of ℂ))) ⟶ F.centralizers.scheme
  coefficients : ∀ A : CommAlgCat.{0} ℂ,
    (F.centralizers.points A (toUnit (affine A) ≫ point)).plane.toSubmodule =
      (LinearMap.range F.source.cartan).baseChange A

variable (B : BorelGeometry F) (I : IncidenceAction F) {X : Over (Spec (.of ℂ))}
  (C : Cover F X) (H : CameralMarkedRegularizers.Object F I C) (Z : CartanPoint F)

attribute [local instance] CameralBorelReductionModels.borelGroup
attribute [local instance] CameralBorelReductionModels.quotientHom

structure NormalizerReduction where
  torsor : GroupTorsorGeometry.Torsor F.normalizer.scheme X
  fibre : torsor.total ≅ pullback H.regularizer.map Z.point
  toTorsor : torsor.total ⟶ H.regularizer.torsor.total
  toTorsor_normalized : toTorsor = fibre.hom ≫ pullback.fst H.regularizer.map Z.point
  projection_normalized : toTorsor ≫ H.regularizer.torsor.projection = torsor.projection
  equivariant : torsor.action.smul ≫ toTorsor =
    tensorHom F.normalizer.inclusion toTorsor ≫ H.regularizer.torsor.action.smul

variable (N : NormalizerReduction F I C H Z)

structure TorusNormalizerCover where
  torsor : GroupTorsorGeometry.Torsor (Torus F) (total F C)
  identification : torsor.total ≅ N.torsor.total
  projection : N.torsor.total ⟶ total F C
  torsor_projection : identification.hom ≫ projection = torsor.projection
  base : projection ≫ CameralRamificationReindexing.projection F C = N.torsor.projection
  action : torsor.action.smul ≫ identification.hom =
    tensorHom F.normalizer.torus identification.hom ≫ N.torsor.action.smul
  standard_borel : ∀ (A : CommAlgCat.{0} ℂ) (p : affine A ⟶ N.torsor.total)
      (hp : (p ≫ N.toTorsor) ≫ H.regularizer.torsor.projection =
        (p ≫ projection) ≫ CameralRamificationReindexing.projection F C),
    (I.incidence.points A
      (CameralMarkedRegularizers.incidencePoint F I C H (affine A) (p ≫ projection)
        (p ≫ N.toTorsor) hp)).val.snd.plane.toSubmodule = borelAt F.borel A
  deck : ∀ (U : Over (Spec (.of ℂ))) (n : U ⟶ F.normalizer.scheme) (w : F.Weyl)
      (_hw : Label F n w) (p : U ⟶ N.torsor.total),
    CartesianMonoidalCategory.lift n p ≫ N.torsor.action.smul ≫ projection =
      p ≫ projection ≫ (CameralRamificationTensorModels.coverIso F C w).hom

def normalizerBundle (T : TorusNormalizerCover F I C H Z N) : Bundle (Torus F) (total F C) where
  torsor := T.torsor
  map := toUnit T.torsor.total
  equivariant := Subsingleton.elim _ _

variable (R : ReductionFamily F B I C) (O : BorelTorusOperations F B)

structure BorelNormalizerComparison (T : TorusNormalizerCover F I C H Z N) where
  toBorel : N.torsor.total ⟶ (R.object H).torsor.total
  toTorsor : toBorel ≫ (R.object H).toTorsor = N.toTorsor
  over : toBorel ≫ (R.object H).torsor.projection = T.projection
  comparison : (rawBorelFunctor F B I C R O).obj H ≅ normalizerBundle F I C H Z N T
  quotient_normalized : ∀ (U : Over (Spec (.of ℂ))) (p : U ⟶ N.torsor.total),
    CartesianMonoidalCategory.lift (p ≫ toBorel) (toUnit U ≫ η[Torus F]) ≫
      (O.pushout.diagram (total F C) (markedBundle F B I C (R.object H))).quotient ≫
      comparison.hom.iso.hom ≫ T.identification.hom = p

end MathlibExt.AlgebraicGeometry.CameralUnramifiedNormalizerModels
