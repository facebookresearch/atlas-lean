/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CompletedTorsorSourceFrames

/-!
# The actual global-to-local meromorphic Hecke map

Both legs are the computed source restriction, all-test algebraization
and native fpqc completion pullback. The punctured comparison is an
equivariant natural isomorphism of their actual generic action sheaves.
Its normalization holds on every fpqc test, in every original integral
frame, for the same finite-pole G-point and its actual completion.

The Hecke functor is computed by the native isomorphism-comma lift and
core. No equivalence, v-stack assertion or classification is an input.
All coefficient fields are retained, including equal characteristic.
Source: Fargues--Scholze, arXiv:2102.13459v4, Sections III.3 and VI.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MeromorphicTorsorCompletion

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.GeneralStackGeometry
open AnalyticGroupTorsorSites AnalyticBundlePrestackModels AnalyticBundleModifications
open AnalyticMeromorphicCoordinates MeromorphicHeckeModels AffinoidTorsorAlgebraizationModels
open FramedMeromorphicGroupModels CompletedTorsorSourceFrames
open MathlibExt.CategoryTheory.SheafTorsorGroupoids

variable (p : ℕ) [Fact p.Prime] (E : Type) [Field E]
  (G : Over (Spec (.of E))) [GrpObj G]
  (H : ∀ V : ESpace p E, GroupDescent p E G V)
  (P : PullbackPreservation p E G H)
  {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
  (Q : PoleChart p E d U)
  (A : Algebraization p E G H Q.space)
  (B : FpqcPreservesTorsors E G (completionBaseMap p E d U Q))

/-- The original modification, with its actual punctured isomorphism. -/
abbrev originalModification (M : Hecke p E G H P d U) := M.of.obj

/-- A source frame system retains every original integral trivialization. -/
abbrev SourceFrames := ∀ (N : Bundles p E G H X)
  (f : IntegralFrame p E G H d U Q N), AlgebraizedFrame p E G H P d U Q A N f

variable (F : SourceFrames p E G H P d U Q A)

/-- The computed left torsor, including every original equivariant arrow. -/
def completedLeft : Hecke p E G H P d U ⥤ FormalTorsors p E G d U Q :=
  MeromorphicHeckeModels.leftLeg p E G H P d U ⋙ completedTorsors p E G H P d U Q A B

/-- The computed right torsor. -/
def completedRight : Hecke p E G H P d U ⥤ FormalTorsors p E G d U Q :=
  MeromorphicHeckeModels.rightLeg p E G H P d U ⋙ completedTorsors p E G H P d U Q A B

/-- Evaluate an actual punctured action comparison in the source-completed frames. -/
def framedValue (M : Hecke p E G H P d U)
    (e : (genericActions p E G d U Q).obj
      ((completedLeft p E G H P d U Q A B).obj M) ≅
        (genericActions p E G d U Q).obj
          ((completedRight p E G H P d U Q A B).obj M))
    (left : IntegralFrame p E G H d U Q (originalModification p E G H P d U M).left)
    (right : IntegralFrame p E G H d U Q (originalModification p E G H P d U M).right)
    (T : WittDiscTorsorModels.Site E (genericScheme p E d U Q))
    (a : (WittDiscTorsorModels.groupSheaf E G (genericScheme p E d U Q)).obj.obj (op T)) :
    (WittDiscTorsorModels.groupSheaf E G (genericScheme p E d U Q)).obj.obj (op T) :=
  (genericFrame p E G H P d U Q A B
      (F (originalModification p E G H P d U M).right right)).hom.val.hom.app (op T)
    (e.hom.val.hom.app (op T)
      ((genericFrame p E G H P d U Q A B
        (F (originalModification p E G H P d U M).left left)).inv.val.hom.app (op T) a))

variable (h : IsUnit (sectionMap p E Q.puncture.map Q.parameter))

/-- Every test restricts the same completed G-point by the actual represented group map. -/
def completedPointAt (M : Hecke p E G H P d U)
    (left : IntegralFrame p E G H d U Q (originalModification p E G H P d U M).left)
    (right : IntegralFrame p E G H d U Q (originalModification p E G H P d U M).right)
    (g : GroupFactorization p E G H P d U Q h
      (originalModification p E G H P d U M) left right)
    (T : WittDiscTorsorModels.Site E (genericScheme p E d U Q)) :
    (WittDiscTorsorModels.groupSheaf E G (genericScheme p E d U Q)).obj.obj (op T) :=
  ((WittDiscTorsorModels.baseGroupPresheaf E G).map T.hom.op).hom
    (ULift.up (completedElement p E G H P d U Q h
      (originalModification p E G H P d U M) left right g))

/-- The finite-pole spectrum is the actual E-algebra test Spec(A[1/t]). -/
def finitePoleScheme : Over (Spec (.of E)) :=
  (AlgebraicGroupPointRepresentations.testSchemes E).obj
    (op (MeromorphicCoefficientCompletion.meromorphicTest p E d U Q))

/-- Its map to the original affinoid spectrum uses the actual localization unit. -/
def finitePoleBaseMap : finitePoleScheme p E d U Q ⟶ coefficientScheme p E Q.space :=
  Over.homMk (Spec.map (CommRingCat.ofHom
    (algebraMap (SectionRing p E Q.space)
      (MeromorphicCoefficientCompletion.MeromorphicRing p E d U Q))))
    (by
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp]
      rfl)

/-- Completion of finite-pole coefficients is the original native algebra-test map. -/
def completedFinitePoleMap : genericScheme p E d U Q ⟶ finitePoleScheme p E d U Q :=
  (AlgebraicGroupPointRepresentations.testSchemes E).map
    (MeromorphicCoefficientCompletion.completionTestMap p E d U Q).op

omit [Fact p.Prime] in
/-- The two original paths to the affinoid spectrum commute on every coefficient. -/
theorem finitePoleCompletion_square :
    localization p E d U Q ≫ completionBaseMap p E d U Q =
      completedFinitePoleMap p E d U Q ≫ finitePoleBaseMap p E d U Q := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun a ↦ (MeromorphicCoefficientCompletion.completedMap_coefficients
    p E d U Q a).symm)

/-- Unframed finite-pole actions use the same restricted, all-test algebraized torsors. -/
def finitePoleActions : Bundles p E G H X ⥤
    Action (WittDiscTorsorModels.topology E (finitePoleScheme p E d U Q))
      (WittDiscTorsorModels.groupSheaf E G (finitePoleScheme p E d U Q)) :=
  bundlePullback p E G H P Q.map ⋙ A.functor ⋙
    WittDiscTorsorModels.torsorActions E G (coefficientScheme p E Q.space) ⋙
      WittDiscTorsorModels.actionPullback G (finitePoleBaseMap p E d U Q)

/-- Each punctured test has its original Gamma spectrum and finite-pole localization lift. -/
structure FinitePoleTest (T : Site p E Q.puncture.space) where
  test : WittDiscTorsorModels.Site E (finitePoleScheme p E d U Q)
  coefficients : (Over.map (finitePoleBaseMap p E d U Q)).obj test =
    (coefficientTests p E Q.space).obj (Over.mk (T.hom ≫ Q.puncture.map))

/-- The original punctured torsor map acts on all source points without selecting frames. -/
def originalComparisonValue (M : Hecke p E G H P d U)
    (T : Site p E Q.puncture.space)
    (x : ((forgetBundles p E G H X).obj
      (originalModification p E G H P d U M).left).obj.obj
        (op (Over.mk ((T.hom ≫ Q.puncture.map) ≫ Q.map)))) :
    ((forgetBundles p E G H X).obj
      (originalModification p E G H P d U M).right).obj.obj
        (op (Over.mk ((T.hom ≫ Q.puncture.map) ≫ Q.map))) := by
  let M' := originalModification p E G H P d U M
  let e := refined_puncture_test_equality p E d U Q T
  let before := ((forgetBundles p E G H X).obj M'.left).obj.map (eqToHom e.symm).op x
  let compared := ((forgetBundles p E G H U.space).map M'.punctured.hom).hom.app
    (op (Over.mk (T.hom ≫ Q.punctureToOriginal))) before
  exact ((forgetBundles p E G H X).obj M'.right).obj.map (eqToHom e).op compared

/-- The actual finite-pole isomorphism is evaluated through the same original coefficient test. -/
def finitePoleComparisonValue
    (e : MeromorphicHeckeModels.leftLeg p E G H P d U ⋙
      finitePoleActions p E G H P d U Q A ≅
        MeromorphicHeckeModels.rightLeg p E G H P d U ⋙
          finitePoleActions p E G H P d U Q A)
    (M : Hecke p E G H P d U) (T : Site p E Q.puncture.space)
    (W : FinitePoleTest p E d U Q T)
    (x : (algebraicPresheaf p E G Q.space
      (A.functor.obj ((bundlePullback p E G H P Q.map).obj
        (originalModification p E G H P d U M).left))).obj
          (op (Over.mk (T.hom ≫ Q.puncture.map)))) :
    (algebraicPresheaf p E G Q.space
      (A.functor.obj ((bundlePullback p E G H P Q.map).obj
        (originalModification p E G H P d U M).right))).obj
          (op (Over.mk (T.hom ≫ Q.puncture.map))) := by
  let NL := A.functor.obj ((bundlePullback p E G H P Q.map).obj
    (originalModification p E G H P d U M).left)
  let NR := A.functor.obj ((bundlePullback p E G H P Q.map).obj
    (originalModification p E G H P d U M).right)
  let before := ((algebraicForget p E G Q.space).obj NL).obj.map
    (eqToHom W.coefficients).op x
  let compared := (e.app M).hom.val.hom.app (op W.test) before
  exact ((algebraicForget p E G Q.space).obj NR).obj.map
    (eqToHom W.coefficients.symm).op compared

/-- Completion uses the original native sheaf composition square, on all points. -/
def originSheafSquare (N : Bundles p E G H X) :
    ((genericActions p E G d U Q).obj
      ((completedTorsors p E G H P d U Q A B).obj N)).sheaf ≅
      ((WittDiscTorsorModels.actionPullback G (completedFinitePoleMap p E d U Q)).obj
        ((finitePoleActions p E G H P d U Q A).obj N)).sheaf :=
  ((WittDiscTorsorModels.baseTopology E).overMapPullbackComp (Type 1)
    (localization p E d U Q) (completionBaseMap p E d U Q)).app
      ((algebraicForget p E G Q.space).obj
        (A.functor.obj ((bundlePullback p E G H P Q.map).obj N))) ≪≫
  ((WittDiscTorsorModels.baseTopology E).overMapPullbackCongr (Type 1)
    (finitePoleCompletion_square p E d U Q)).app
      ((algebraicForget p E G Q.space).obj
        (A.functor.obj ((bundlePullback p E G H P Q.map).obj N))) ≪≫
  (((WittDiscTorsorModels.baseTopology E).overMapPullbackComp (Type 1)
    (completedFinitePoleMap p E d U Q) (finitePoleBaseMap p E d U Q)).app
      ((algebraicForget p E G Q.space).obj
        (A.functor.obj ((bundlePullback p E G H P Q.map).obj N)))).symm

/-- The action completion square must have exactly that original native underlying sheaf map. -/
structure OriginSquare where
  comparison : completedTorsors p E G H P d U Q A B ⋙ genericActions p E G d U Q ≅
    finitePoleActions p E G H P d U Q A ⋙
      WittDiscTorsorModels.actionPullback G (completedFinitePoleMap p E d U Q)
  underlying : ∀ N : Bundles p E G H X,
    (comparison.app N).hom.val = (originSheafSquare p E G H P d U Q A B N).hom

/-- The unframed origin is fixed by the original map on every analytic test and every point. -/
structure SourceOrigin where
  comparison : MeromorphicHeckeModels.leftLeg p E G H P d U ⋙
    finitePoleActions p E G H P d U Q A ≅
      MeromorphicHeckeModels.rightLeg p E G H P d U ⋙
        finitePoleActions p E G H P d U Q A
  tests : ∀ T : Site p E Q.puncture.space, FinitePoleTest p E d U Q T
  normalized : ∀ (M : Hecke p E G H P d U) (T : Site p E Q.puncture.space)
    (x : (algebraicPresheaf p E G Q.space
      (A.functor.obj ((bundlePullback p E G H P Q.map).obj
        (originalModification p E G H P d U M).left))).obj
          (op (Over.mk (T.hom ≫ Q.puncture.map)))),
    (A.comparison ((bundlePullback p E G H P Q.map).obj
      (originalModification p E G H P d U M).right)).hom.app
        (op (Over.mk (T.hom ≫ Q.puncture.map)))
      (finitePoleComparisonValue p E G H P d U Q A comparison M T (tests T) x) =
      ULift.up (originalComparisonValue p E G H P d U Q M T
        (((A.comparison ((bundlePullback p E G H P Q.map).obj
          (originalModification p E G H P d U M).left)).hom.app
            (op (Over.mk (T.hom ≫ Q.puncture.map))) x).down))
  square : OriginSquare p E G H P d U Q A B

/-- The completed comparison is computed from that unframed original finite-pole map. -/
def completedSourceComparison (O : SourceOrigin p E G H P d U Q A B) :
    completedLeft p E G H P d U Q A B ⋙ genericActions p E G d U Q ≅
      completedRight p E G H P d U Q A B ⋙ genericActions p E G d U Q :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ O.square.comparison ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight O.comparison _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ O.square.comparison.symm ≪≫
        (Functor.associator _ _ _).symm

/-- Source comparison data fixes all original frames, tests, points and arrows. -/
structure CompletionComparison where
  origin : SourceOrigin p E G H P d U Q A B
  normalized : ∀ (M : Hecke p E G H P d U)
    (left : IntegralFrame p E G H d U Q (originalModification p E G H P d U M).left)
    (right : IntegralFrame p E G H d U Q (originalModification p E G H P d U M).right)
    (g : GroupFactorization p E G H P d U Q h
      (originalModification p E G H P d U M) left right)
    (T : WittDiscTorsorModels.Site E (genericScheme p E d U Q))
    (a : (WittDiscTorsorModels.groupSheaf E G (genericScheme p E d U Q)).obj.obj (op T)),
    framedValue p E G H P d U Q A B F M
      ((completedSourceComparison p E G H P d U Q A B origin).app M) left right T a =
      completedPointAt p E G H P d U Q h M left right g T * a

variable (C : CompletionComparison p E G H P d U Q A B F h)

/-- Its comparison is the computed source completion, with no independently selected endpoint. -/
def CompletionComparison.comparison :
    completedLeft p E G H P d U Q A B ⋙ genericActions p E G d U Q ≅
      completedRight p E G H P d U Q A B ⋙ genericActions p E G d U Q :=
  completedSourceComparison p E G H P d U Q A B C.origin

/-- The actual native comma lift, followed by its native core. -/
def globalToLocal : Hecke p E G H P d U ⥤ LocalHecke p E G d U Q :=
  Core.functorToCore ((CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
    (genericActions p E G d U Q) (genericActions p E G d U Q) (Hecke p E G H P d U)).obj
    ⟨completedLeft p E G H P d U Q A B, completedRight p E G H P d U Q A B, C.comparison⟩)

omit [Fact p.Prime] in
/-- The first leg is exactly the computed completion functor. -/
theorem globalToLocal_left :
    globalToLocal p E G H P d U Q A B F h C ⋙ localLeftLeg p E G d U Q =
      MeromorphicHeckeModels.leftLeg p E G H P d U ⋙
        completedTorsors p E G H P d U Q A B := rfl

omit [Fact p.Prime] in
/-- The second leg is exactly the same completion applied to the right torsor. -/
theorem globalToLocal_right :
    globalToLocal p E G H P d U Q A B F h C ⋙ localRightLeg p E G d U Q =
      MeromorphicHeckeModels.rightLeg p E G H P d U ⋙
        completedTorsors p E G H P d U Q A B := rfl

omit [Fact p.Prime] in
/-- Its actual punctured map is the original source-normalized comparison. -/
theorem globalToLocal_comparison (M : Hecke p E G H P d U) :
    ((globalToLocal p E G H P d U Q A B F h C).obj M).of.iso.hom =
      C.comparison.hom.app M := rfl

omit [Fact p.Prime] in
/-- Every original equivariant Hecke arrow commutes with the same punctured map. -/
theorem comparison_naturality {M N : Hecke p E G H P d U} (f : M ⟶ N) :
    (completedLeft p E G H P d U Q A B ⋙ genericActions p E G d U Q).map f ≫
      C.comparison.hom.app N = C.comparison.hom.app M ≫
        (completedRight p E G H P d U Q A B ⋙ genericActions p E G d U Q).map f :=
  C.comparison.hom.naturality f

omit [Fact p.Prime] in
/-- The normalization applies to every original fpqc test point. -/
theorem framedValue_normalized (M : Hecke p E G H P d U)
    (left : IntegralFrame p E G H d U Q (originalModification p E G H P d U M).left)
    (right : IntegralFrame p E G H d U Q (originalModification p E G H P d U M).right)
    (g : GroupFactorization p E G H P d U Q h
      (originalModification p E G H P d U M) left right)
    (T : WittDiscTorsorModels.Site E (genericScheme p E d U Q))
    (a : (WittDiscTorsorModels.groupSheaf E G (genericScheme p E d U Q)).obj.obj (op T)) :
    framedValue p E G H P d U Q A B F M (C.comparison.app M) left right T a =
      completedPointAt p E G H P d U Q h M left right g T * a :=
  C.normalized M left right g T a

/-- The G-point is extracted from the actual local comparison in the original source frames. -/
def framedElement (M : Hecke p E G H P d U)
    (left : IntegralFrame p E G H d U Q (originalModification p E G H P d U M).left)
    (right : IntegralFrame p E G H d U Q (originalModification p E G H P d U M).right) :
    (AlgebraicGroupPointRepresentations.groups E G).obj
      (MeromorphicCoefficientCompletion.completedTest p E d U Q) :=
  (framedValue p E G H P d U Q A B F M (C.comparison.app M) left right
    (Over.mk (𝟙 (genericScheme p E d U Q))) 1).down

omit [Fact p.Prime] in
/-- Extraction returns the same actual finite-pole completion for every source witness. -/
theorem framedElement_normalized (M : Hecke p E G H P d U)
    (left : IntegralFrame p E G H d U Q (originalModification p E G H P d U M).left)
    (right : IntegralFrame p E G H d U Q (originalModification p E G H P d U M).right)
    (g : GroupFactorization p E G H P d U Q h
      (originalModification p E G H P d U M) left right) :
    framedElement p E G H P d U Q A B F h C M left right =
      completedElement p E G H P d U Q h
        (originalModification p E G H P d U M) left right g := by
  have hn := C.normalized M left right g (Over.mk (𝟙 (genericScheme p E d U Q))) 1
  change _ = _ at hn
  simpa [framedElement, completedPointAt, CompletionComparison.comparison]
    using congrArg ULift.down hn

/-- Every representation is evaluated on that actual extracted comparison. -/
def framedMatrix (M : Hecke p E G H P d U)
    (left : IntegralFrame p E G H d U Q (originalModification p E G H P d U M).left)
    (right : IntegralFrame p E G H d U Q (originalModification p E G H P d U M).right)
    (n : ℕ) (ρ : AlgebraicGroupPointRepresentations.Representation E G n) :
    Matrix (Fin n) (Fin n) (GenericRing p E d U Q) :=
  AlgebraicGroupPointRepresentations.actionMatrix E G n ρ
    (MeromorphicCoefficientCompletion.completedTest p E d U Q)
      (framedElement p E G H P d U Q A B F h C M left right)

omit [Fact p.Prime] in
/-- Every entry is the original representation coefficient under the same completion map. -/
theorem framedMatrix_entries (M : Hecke p E G H P d U)
    (left : IntegralFrame p E G H d U Q (originalModification p E G H P d U M).left)
    (right : IntegralFrame p E G H d U Q (originalModification p E G H P d U M).right)
    (g : GroupFactorization p E G H P d U Q h
      (originalModification p E G H P d U M) left right)
    (n : ℕ) (ρ : AlgebraicGroupPointRepresentations.Representation E G n) (i j : Fin n) :
    framedMatrix p E G H P d U Q A B F h C M left right n ρ i j =
      MeromorphicCoefficientCompletion.completedMap p E d U Q
        (meromorphicMatrix p E G H P d U Q h
          (originalModification p E G H P d U M) left right g n ρ i j) := by
  rw [framedMatrix, framedElement_normalized p E G H P d U Q A B F h C M left right g]
  exact completedMatrix_entries p E G H P d U Q h
    (originalModification p E G H P d U M) left right g n ρ i j

omit [Fact p.Prime] in
/-- Native functor units retain the actual source identity arrows. -/
theorem globalToLocal_id (M : Hecke p E G H P d U) :
    (globalToLocal p E G H P d U Q A B F h C).map (𝟙 M) =
      𝟙 ((globalToLocal p E G H P d U Q A B F h C).obj M) :=
  (globalToLocal p E G H P d U Q A B F h C).map_id M

omit [Fact p.Prime] in
/-- Native compositions retain both actual source torsor arrows. -/
theorem globalToLocal_comp {M N K : Hecke p E G H P d U} (f : M ⟶ N) (g : N ⟶ K) :
    (globalToLocal p E G H P d U Q A B F h C).map (f ≫ g) =
      (globalToLocal p E G H P d U Q A B F h C).map f ≫
        (globalToLocal p E G H P d U Q A B F h C).map g :=
  (globalToLocal p E G H P d U Q A B F h C).map_comp f g

end MathlibExt.AlgebraicGeometry.MeromorphicTorsorCompletion
