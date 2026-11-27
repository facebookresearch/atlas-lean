/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralIsogenyGeometry

/-!
# Canonical universal beta through the actual central cover

For nonprimitive coroots the Cartan-open gamma condition does not fix
beta. The source construction uses an actual central group isogeny
with primitive lifted coroots. The Borel map is fixed by the original
map of trivial G torsors. Its torus map is fixed on every B-to-T
quotient point, with every parameter pullback retained. Beta is then
compared on every source torus frame through the full computed-dual
ramification map. The torus point map is fppf, so these tests cover the
target frames, including nonreduced coefficients.
Source: DG math/0005132v3, Section7.2 and Sections6.5/15/16.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralIsogenyBetaModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open CameralFoundationPackages CameralRootSL2Sources CameralRamificationReindexing
open CameralRamificationTensorModels CameralRamificationCocycles CameralCharacterRealizations
open CameralSimpleRootTrivializations CameralLiftedNormalizerModels CameralNormalizerShifts
open CameralCoverDescentModels CameralBorelReductionModels CameralBorelAbelianizationCore
open CameralRawAbelianizationData CameralUniversalRegularizerModels
open CameralUniversalRawLiftModels CameralIsogenyGeometry
open ContractedTorsorModels ExpansionParameterModels GroupTorsorGeometry
open LineBundleTaskContracts

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

attribute [local instance] CameralRamificationTensorModels.torusGroup
attribute [local instance] CameralBorelReductionModels.borelGroup
attribute [local instance] CameralBorelReductionModels.quotientHom
attribute [local instance] CameralRegularizedHiggsModels.centralizerGroupAction

structure PrimitiveSource where
  scheme : Over (Spec (.of ℂ))
  [group : GrpObj scheme]
  foundation : Foundation scheme tori
  root : RootNormalizerGeometry scheme tori foundation
  torsors : RootTorsorInputs foundation root
  ramification : CanonicalRamificationFamily foundation root torsors
  characters : CharacterCalculus foundation root torsors
  reflection : SimpleReflectionTorsors foundation root torsors ramification
  weyl : RootWeylGeometry foundation root
  trivialization : CanonicalSimpleRootTrivializations foundation root torsors ramification
    characters
  incidence : IncidenceAction foundation
  borel : BorelGeometry foundation
  inputs : LiftInputs foundation incidence borel
  universal : UniversalRegularizer foundation incidence
  raw : UniversalRawConstruction foundation root torsors ramification characters
    reflection weyl trivialization incidence borel inputs universal
  isogeny : PinnedIsogeny F foundation K root I incidence B borel

attribute [instance] PrimitiveSource.group

variable (P : PrimitiveSource F K I B)

abbrev primeCover := P.incidence.incidence.cameral
abbrev primeObject := P.universal.object P.foundation P.incidence
abbrev primeBundle := (CameralBorelLiftModels.underlying P.foundation P.incidence P.borel
  (P.inputs.reduction (primeCover F K I B P)) P.inputs.operation).obj (primeObject F K I B P)
abbrev targetBundle := (CameralBorelLiftModels.underlying F I B
  (V.reduction I.incidence.cameral) V.operation).obj (U.object F I)

def originalTorsorMap : (primeObject F K I B P).regularizer.torsor.total ⟶
    (U.object F I).regularizer.torsor.total :=
  P.universal.unit.total.hom ≫ tensorHom P.isogeny.group P.isogeny.base.hom ≫ U.unit.total.inv

abbrev primeParameter (Z : Over (Spec (.of ℂ))) :=
  (P.inputs.parameter (primeCover F K I B P)).pulled Z

abbrev primeParameterBundle (Z : Over (Spec (.of ℂ))) :=
  parameterBundle P.foundation P.root P.torsors
    (P.inputs.parameter (primeCover F K I B P)) (primeBundle F K I B P) Z

abbrev targetParameterBundle (Z : Over (Spec (.of ℂ))) :=
  parameterBundle F K D (V.parameter I.incidence.cameral) (targetBundle F I B V U) Z

structure IsogenyTransport where
  borelOriginal : ((P.inputs.reduction (primeCover F K I B P)).object
      (primeObject F K I B P)).torsor.total ⟶
    ((V.reduction I.incidence.cameral).object (U.object F I)).torsor.total
  cover : borelOriginal ≫
      ((V.reduction I.incidence.cameral).object (U.object F I)).torsor.projection =
    ((P.inputs.reduction (primeCover F K I B P)).object (primeObject F K I B P)).torsor.projection ≫
      P.isogeny.incidence.hom
  original : borelOriginal ≫ ((V.reduction I.incidence.cameral).object (U.object F I)).toTorsor =
    ((P.inputs.reduction (primeCover F K I B P)).object (primeObject F K I B P)).toTorsor ≫
      originalTorsorMap F K I B U P
  group : ((P.inputs.reduction (primeCover F K I B P)).object
      (primeObject F K I B P)).torsor.action.smul ≫ borelOriginal =
    tensorHom P.isogeny.borel borelOriginal ≫
      ((V.reduction I.incidence.cameral).object (U.object F I)).torsor.action.smul
  parameter : ∀ Z : Over (Spec (.of ℂ)),
    total P.foundation (primeParameter F K I B P Z).cover ≅
      total F ((V.parameter I.incidence.cameral).pulled Z).cover
  parameter_original : ∀ Z,
    (parameter Z).hom ≫ ((V.parameter I.incidence.cameral).pulled Z).arrow.total =
      (primeParameter F K I B P Z).arrow.total ≫ P.isogeny.incidence.hom
  parameter_base : ∀ Z,
    (parameter Z).hom ≫ projection F ((V.parameter I.incidence.cameral).pulled Z).cover =
      projection P.foundation (primeParameter F K I B P Z).cover ≫
        tensorHom P.isogeny.base.hom (𝟙 Z)
  parameter_naturality : ∀ {Z H : Over (Spec (.of ℂ))} (f : H ⟶ Z),
    ((P.inputs.parameter (primeCover F K I B P)).arrow f).total ≫ (parameter Z).hom =
      (parameter H).hom ≫ ((V.parameter I.incidence.cameral).arrow f).total
  fixed : ∀ (Z : Over (Spec (.of ℂ))) (i : Fin P.foundation.roots.count),
    fixedScheme P.foundation (primeParameter F K I B P Z).cover i ⟶
      fixedScheme F ((V.parameter I.incidence.cameral).pulled Z).cover (P.isogeny.root i)
  fixed_normalized : ∀ Z i,
    fixed Z i ≫ fixedInclusion F ((V.parameter I.incidence.cameral).pulled Z).cover
        (P.isogeny.root i) =
      fixedInclusion P.foundation (primeParameter F K I B P Z).cover i ≫ (parameter Z).hom
  ramification : ∀ Z i, CrossRamification F P.foundation (parameter Z).hom i (P.isogeny.root i)
  torus : ∀ Z : Over (Spec (.of ℂ)), (primeParameterBundle F K I B P Z).torsor.total ⟶
    (targetParameterBundle F K D I B V U Z).torsor.total
  projection : ∀ Z,
    torus Z ≫ (targetParameterBundle F K D I B V U Z).torsor.projection =
      (primeParameterBundle F K I B P Z).torsor.projection ≫ (parameter Z).hom
  flat : ∀ Z, Flat (torus Z).left
  presentation : ∀ Z, LocallyOfFinitePresentation (torus Z).left
  surjective : ∀ Z, Surjective (torus Z).left
  quotient : ∀ (Z H : Over (Spec (.of ℂ)))
      (z : H ⟶ total P.foundation (primeParameter F K I B P Z).cover)
      (b : H ⟶ ((P.inputs.reduction (primeCover F K I B P)).object
        (primeObject F K I B P)).torsor.total) (t : H ⟶ Torus P.foundation)
      (hp : (CartesianMonoidalCategory.lift b t ≫
        (P.inputs.operation.pushout.diagram (total P.foundation (primeCover F K I B P))
          (markedBundle P.foundation P.borel P.incidence (primeCover F K I B P)
            ((P.inputs.reduction (primeCover F K I B P)).object
              (primeObject F K I B P)))).quotient) ≫
              (primeBundle F K I B P).torsor.projection =
                z ≫ (primeParameter F K I B P Z).arrow.total)
      (hq : (CartesianMonoidalCategory.lift (b ≫ borelOriginal) (t ≫ P.isogeny.torus) ≫
        (V.operation.pushout.diagram (total F I.incidence.cameral)
          (markedBundle F B I I.incidence.cameral
            ((V.reduction I.incidence.cameral).object (U.object F I)))).quotient) ≫
              (targetBundle F I B V U).torsor.projection =
                (z ≫ (parameter Z).hom) ≫ ((V.parameter I.incidence.cameral).pulled Z).arrow.total),
    pullback.lift (CartesianMonoidalCategory.lift b t ≫
      (P.inputs.operation.pushout.diagram (total P.foundation (primeCover F K I B P))
        (markedBundle P.foundation P.borel P.incidence (primeCover F K I B P)
          ((P.inputs.reduction (primeCover F K I B P)).object (primeObject F K I B P)))).quotient)
      z hp ≫
      (P.torsors.torus.baseChange.pullback (primeParameter F K I B P Z).arrow.total
        (primeBundle F K I B P)).comparison.inv ≫ torus Z =
    pullback.lift (CartesianMonoidalCategory.lift (b ≫ borelOriginal) (t ≫ P.isogeny.torus) ≫
      (V.operation.pushout.diagram (total F I.incidence.cameral)
        (markedBundle F B I I.incidence.cameral
          ((V.reduction I.incidence.cameral).object (U.object F I)))).quotient)
      (z ≫ (parameter Z).hom) hq ≫
      (D.torus.baseChange.pullback ((V.parameter I.incidence.cameral).pulled Z).arrow.total
        (targetBundle F I B V U)).comparison.inv

variable (C : IsogenyTransport F K D I B V U P)

set_option maxHeartbeats 1000000 in
-- The pulled-back line comparison along the fixed-scheme maps needs extra budget.
def betaLineComparison (Z : Over (Spec (.of ℂ))) (i : Fin P.foundation.roots.count)
    (H : Over (Spec (.of ℂ)))
    (y : H ⟶ fixedScheme P.foundation (primeParameter F K I B P Z).cover i) :
    (Scheme.Modules.pullback ((y ≫ C.fixed Z i) ≫
        fixedInclusion F ((V.parameter I.incidence.cameral).pulled Z).cover
          (P.isogeny.root i)).left).obj
      (CameralRamificationReindexing.line F ((V.parameter I.incidence.cameral).pulled Z).cover
        (P.isogeny.root i)) ≅
    (Scheme.Modules.pullback (y ≫ fixedInclusion P.foundation
      (primeParameter F K I B P Z).cover i).left).obj
      (CameralRamificationReindexing.line P.foundation (primeParameter F K I B P Z).cover i) := by
  have he : (y ≫ C.fixed Z i) ≫
      fixedInclusion F ((V.parameter I.incidence.cameral).pulled Z).cover (P.isogeny.root i) =
    (y ≫ fixedInclusion P.foundation (primeParameter F K I B P Z).cover i) ≫
      (C.parameter Z).hom := by
    rw [Category.assoc, C.fixed_normalized, ← Category.assoc]
  exact (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left he)).app _ ≪≫
    (Scheme.Modules.pullbackComp (y ≫ fixedInclusion P.foundation
      (primeParameter F K I B P Z).cover i).left (C.parameter Z).hom.left).symm.app _ ≪≫
    (Scheme.Modules.pullback (y ≫ fixedInclusion P.foundation
      (primeParameter F K I B P Z).cover i).left).mapIso (C.ramification Z i).line

variable (W : UniversalRawConstruction F K D R A Q E T I B V U)

structure BetaNormalization : Prop where
  beta : ∀ (Z : Over (Spec (.of ℂ))) (i : Fin P.foundation.roots.count)
      (hi : SimpleRoot P.scheme tori P.foundation i) (c : Z ⟶ torusScheme ℂ 1)
      (H : Over (Spec (.of ℂ)))
      (y : H ⟶ fixedScheme P.foundation (primeParameter F K I B P Z).cover i)
      (p : H ⟶ (primeParameterBundle F K I B P Z).torsor.total)
      (hp : p ≫ (primeParameterBundle F K I B P Z).torsor.projection =
        y ≫ fixedInclusion P.foundation (primeParameter F K I B P Z).cover i)
      (hq : (p ≫ C.torus Z) ≫ (targetParameterBundle F K D I B V U Z).torsor.projection =
        (y ≫ C.fixed Z i) ≫ fixedInclusion F ((V.parameter I.incidence.cameral).pulled Z).cover
          (P.isogeny.root i)),
    rawBetaValue F K D R A (V.parameter I.incidence.cameral) (targetBundle F I B V U)
      W.data.beta Z (P.isogeny.root i) ((P.isogeny.simple i).mp hi) c H
      (y ≫ C.fixed Z i) (p ≫ C.torus Z) hq ≫
        (betaLineComparison F K D I B V U P C Z i H y).hom =
    rawBetaValue P.foundation P.root P.torsors P.ramification P.characters
      (P.inputs.parameter (primeCover F K I B P)) (primeBundle F K I B P) P.raw.data.beta
      Z i hi c H y p hp

/-- The universal lift has both the original gamma and the actual isogeny beta normalization. -/
structure NormalizedUniversal where
  raw : UniversalRawConstruction F K D R A Q E T I B V U
  prime : PrimitiveSource F K I B
  transport : IsogenyTransport F K D I B V U prime
  beta : BetaNormalization F K D R A Q E T I B V U prime transport raw

end MathlibExt.AlgebraicGeometry.CameralIsogenyBetaModels
