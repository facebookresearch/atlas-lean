/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FramedMeromorphicGroupModels

/-!
# Actual unframed affinoid G-torsor algebraization and completion

The algebraic source is Spec of the original affinoid Gamma ring. Each
analytic test is sent by its actual Gamma coefficient map to a scheme
over that source. Algebraization must identify the whole original
torsor presheaf on every such test, every equivariant arrow, and every
G-action component. A choice only on globally trivialized objects does
not provide this comparison.

Positive completion is then computed: restrict the original analytic
torsor to its actual Cartier chart, apply that source algebraization,
and pull the resulting fpqc action sheaf along the actual completion
Spec map. All carriers are native torsor action sheaves.

Source: Fargues--Scholze arXiv:2102.13459v4, Sections III.3 and VI.1;
affinoid algebraization and Beauville--Laszlo descent. Native Gamma,
Spec, over-site restriction, fpqc group sheaves and cores are reused.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AffinoidTorsorAlgebraizationModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open AnalyticGroupTorsorSites AnalyticBundlePrestackModels AnalyticBundleModifications
open AnalyticMeromorphicCoordinates MeromorphicHeckeModels
open MathlibExt.CategoryTheory.SheafTorsorGroupoids

variable (p : ℕ) [Fact p.Prime] (E : Type) [Field E]
  (G : Over (Spec (.of E))) [GrpObj G]
  (H : ∀ V : ESpace p E, GroupDescent p E G V)

/-- The source is the actual original Gamma spectrum over E. -/
abbrev coefficientScheme (X : ESpace p E) : Over (Spec (.of E)) :=
  (affineTests p E).obj X

/-- Every analytic refinement uses its actual Gamma/Spec coefficient map. -/
def coefficientTests (X : ESpace p E) :
    Site p E X ⥤ WittDiscTorsorModels.Site E (coefficientScheme p E X) where
  obj T := Over.mk ((affineTests p E).map T.hom)
  map {T U} f := Over.homMk ((affineTests p E).map f.left) (by
    change (affineTests p E).map f.left ≫ (affineTests p E).map U.hom =
      (affineTests p E).map T.hom
    rw [← (affineTests p E).map_comp, f.w])
  map_id T := by
    apply Over.OverMorphism.ext
    exact (affineTests p E).map_id T.left
  map_comp {T U V} f g := by
    apply Over.OverMorphism.ext
    change (affineTests p E).map (f.left ≫ g.left) =
      (affineTests p E).map f.left ≫ (affineTests p E).map g.left
    exact (affineTests p E).map_comp f.left g.left

/-- Original analytic group points enter the algebraic test group by the native universe lift. -/
def coefficientPoint (X : ESpace p E) (T : Site p E X)
    (g : (pointGroups p E G).obj (op T.left)) :
    (WittDiscTorsorModels.groupSheaf E G (coefficientScheme p E X)).obj.obj
      (op ((coefficientTests p E X).obj T)) := by
  change ULift.{1} ((yonedaGrpObj G).obj (op ((affineTests p E).obj T.left)))
  change (yonedaGrpObj G).obj (op ((affineTests p E).obj T.left)) at g
  exact ULift.up g

/-- The algebraic torsor forgets to its original fpqc action sheaf. -/
def algebraicForget (X : ESpace p E) :
    WittDiscTorsorModels.Torsors E G (coefficientScheme p E X) ⥤
      Sheaf (WittDiscTorsorModels.topology E (coefficientScheme p E X)) (Type 1) :=
  WittDiscTorsorModels.torsorActions E G (coefficientScheme p E X) ⋙
    forgetAction (WittDiscTorsorModels.topology E (coefficientScheme p E X))
      (WittDiscTorsorModels.groupSheaf E G (coefficientScheme p E X))

/-- Its test values use the same original Gamma coefficients. -/
def algebraicPresheaf (X : ESpace p E)
    (N : WittDiscTorsorModels.Torsors E G (coefficientScheme p E X)) :
    (Site p E X)ᵒᵖ ⥤ Type 1 :=
  (coefficientTests p E X).op ⋙ ((algebraicForget p E G X).obj N).obj

/-- Only the original analytic torsor's value universe is lifted. -/
def analyticPresheaf (X : ESpace p E) (N : Bundles p E G H X) :
    (Site p E X)ᵒᵖ ⥤ Type 1 :=
  ((forgetBundles p E G H X).obj N).obj ⋙ uliftFunctor.{1, 0}

/-- The source functor retains every actual test, equivariant map, and action component. -/
structure Algebraization (X : ESpace p E) where
  functor : Bundles p E G H X ⥤ WittDiscTorsorModels.Torsors E G (coefficientScheme p E X)
  comparison : ∀ N : Bundles p E G H X,
    algebraicPresheaf p E G X (functor.obj N) ≅ analyticPresheaf p E G H X N
  maps : ∀ {N M : Bundles p E G H X} (f : N ⟶ M),
    Functor.whiskerLeft (coefficientTests p E X).op
      ((algebraicForget p E G X).map (functor.map f)).hom ≫ (comparison M).hom =
      (comparison N).hom ≫ Functor.whiskerRight
        ((forgetBundles p E G H X).map f).hom uliftFunctor.{1, 0}
  action : ∀ (N : Bundles p E G H X) (T : Site p E X)
    (x : (algebraicPresheaf p E G X (functor.obj N)).obj (op T))
    (g : (pointGroups p E G).obj (op T.left)),
    (comparison N).hom.app (op T)
      (((WittDiscTorsorModels.torsorActions E G (coefficientScheme p E X)).obj
        (functor.obj N)).action.app (op ((coefficientTests p E X).obj T))
          (x, coefficientPoint p E G X T g)) =
      ULift.up (((bundleActions p E G H X).obj N).action.app (op T)
        (((comparison N).hom.app (op T) x).down, g))

variable {B C : Over (Spec (.of E))} (f : B ⟶ C)

/-- Preservation is a proposition about the actual native fpqc action restriction. -/
def FpqcPreservesTorsors : Prop :=
  ∀ N : Action (WittDiscTorsorModels.topology E C) (WittDiscTorsorModels.groupSheaf E G C),
    IsTorsor (WittDiscTorsorModels.topology E C) (WittDiscTorsorModels.groupSheaf E G C) N →
      IsTorsor (WittDiscTorsorModels.topology E B) (WittDiscTorsorModels.groupSheaf E G B)
        ((WittDiscTorsorModels.actionPullback G f).obj N)

/-- The groupoid pullback is the native full-subcategory lift/core of that same action functor. -/
def fpqcTorsorPullback (P : FpqcPreservesTorsors E G f) :
    WittDiscTorsorModels.Torsors E G C ⥤ WittDiscTorsorModels.Torsors E G B :=
  (ObjectProperty.lift
    (show ObjectProperty (Action (WittDiscTorsorModels.topology E B)
      (WittDiscTorsorModels.groupSheaf E G B)) from
      IsTorsor (WittDiscTorsorModels.topology E B) (WittDiscTorsorModels.groupSheaf E G B))
    ((show ObjectProperty (Action (WittDiscTorsorModels.topology E C)
      (WittDiscTorsorModels.groupSheaf E G C)) from
        IsTorsor (WittDiscTorsorModels.topology E C) (WittDiscTorsorModels.groupSheaf E G C)).ι ⋙
      WittDiscTorsorModels.actionPullback G f)
    (fun N => P N.obj N.property)).core

variable (P : PullbackPreservation p E G H)
  {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d) (Q : PoleChart p E d U)

/-- The original affinoid completion unit induces this literal spectrum map over E. -/
def completionBaseMap : positiveScheme p E d U Q ⟶ coefficientScheme p E Q.space :=
  Over.homMk (Spec.map (CommRingCat.ofHom (MeromorphicHeckeModels.completionMap p E d U Q))) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl)

/-- Unframed completion is computed from source restriction, all-test algebraization and native Spec pullback. -/
def completedTorsors (A : Algebraization p E G H Q.space)
    (B : FpqcPreservesTorsors E G (completionBaseMap p E d U Q)) :
    Bundles p E G H X ⥤ FormalTorsors p E G d U Q :=
  bundlePullback p E G H P Q.map ⋙ A.functor ⋙
    fpqcTorsorPullback E G (completionBaseMap p E d U Q) B

end MathlibExt.AlgebraicGeometry.AffinoidTorsorAlgebraizationModels
