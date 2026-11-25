/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AnalyticTorsorPullbacks
public import Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-!
# The native bundle prestack and its source-normalized coherence

Each fibre is literally the groupoid of actual G-torsor action sheaves.
Every pullback is the computed native full-subcategory lift/core of
restriction. The forgetful strong transformation lands in Mathlib's
actual sheaf-over pseudofunctor. Its component functors and naturality
cells are fixed by native sheaf restriction, so coherence cannot be
changed by arbitrary automorphisms of the bundle groupoids.

Existence of the bundled coherent prestack is a construction request.
Being a v-stack or having a B(G) stratification is not an input here.
Source: Fargues--Scholze, arXiv:2102.13459v4, Definition I.2.4 and Section III.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AnalyticBundlePrestackModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.AlgebraicGeometry
open AnalyticGroupTorsorSites AnalyticTorsorPullbacks
open MathlibExt.CategoryTheory.SheafTorsorGroupoids

variable (p : ℕ) [Fact p.Prime] (E : Type) [CommRing E]
  (G : Over (Spec (.of E))) [GrpObj G]
  (H : ∀ X : ESpace p E, GroupDescent p E G X)

abbrev Bundles (X : ESpace p E) := Torsors p E G X (H X)

def bundleObject (X : ESpace p E) : Cat.{1, 1} := Cat.of (Bundles p E G H X)

def forgetBundles (X : ESpace p E) : Bundles p E G H X ⥤
    Sheaf (topology p E X) (Type 0) :=
  Core.inclusion _ ⋙
    (show ObjectProperty (Action (topology p E X) (groupSheaf p E G X (H X))) from
      IsTorsor (topology p E X) (groupSheaf p E G X (H X))).ι ⋙
    forgetAction (topology p E X) (groupSheaf p E G X (H X))

def PullbackPreservation : Prop :=
  ∀ {X Y : ESpace p E} (f : X ⟶ Y), PreservesTorsors p E G f (H Y) (H X)

variable (P : PullbackPreservation p E G H)

def bundlePullback {X Y : ESpace p E} (f : X ⟶ Y) :
    Bundles p E G H Y ⥤ Bundles p E G H X :=
  torsorPullback p E G f (H Y) (H X) (P f)

/-- Forgetting the actual pulled-back torsor is exactly native restriction of its sheaf. -/
def underlyingPullback {X Y : ESpace p E} (f : X ⟶ Y) :
    bundlePullback p E G H P f ⋙ forgetBundles p E G H X ≅
      forgetBundles p E G H Y ⋙ pullbackSetSheaves p E f := Iso.refl _

/-- The pseudofunctor sending an analytic adic space $X$ over $E$ to the category of sheaves of
sets on the slice site over $X$, for the étale topology `ambientTopology`, and a morphism
$f : X \to Y$ to pullback of sheaves along $f$ (`pseudofunctorOver`). -/
def sheafDiagram : Pseudofunctor (LocallyDiscrete (ESpace p E)ᵒᵖ) Cat.{1, 1} :=
  (ambientTopology p E).pseudofunctorOver (Type 0)

/-- All categories, pullbacks and forgetting cells are fixed before requesting coherence. -/
structure BundlePrestack where
  functor : Pseudofunctor (LocallyDiscrete (ESpace p E)ᵒᵖ) Cat.{1, 1}
  object_normalized : ∀ X : ESpace p E,
    functor.obj (LocallyDiscrete.mk (op X)) = bundleObject p E G H X
  map_normalized : ∀ {X Y : ESpace p E} (f : X ⟶ Y),
    HEq (functor.map f.op.toLoc) (bundlePullback p E G H P f).toCatHom
  forget : Pseudofunctor.StrongTrans functor (sheafDiagram p E)
  forget_normalized : ∀ X : ESpace p E,
    HEq (forget.app (LocallyDiscrete.mk (op X))) (forgetBundles p E G H X).toCatHom
  naturality_normalized : ∀ {X Y : ESpace p E} (f : X ⟶ Y),
    HEq (forget.naturality f.op.toLoc) (Cat.Hom.isoMk (underlyingPullback p E G H P f))

end MathlibExt.AlgebraicGeometry.AnalyticBundlePrestackModels
