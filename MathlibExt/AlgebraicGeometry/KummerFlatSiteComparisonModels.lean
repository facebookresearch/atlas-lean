/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CanonicalKummerFlatSiteModels
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# Local root-site refinements and the native sheaf comparison

An arbitrary representable fppf root chart admits source representatives
only locally. These contracts record actual covering refinements, local
lifts of arrows and local equality of arrows. They do not choose a global
inverse functor on chart objects.

The sheaf pushforward is native restriction along the canonical Kfl
functor, and inverse image is its native sheafified left adjoint. The
equivalence of that adjunction remains a theorem conclusion.

Source: Talpo--Vistoli1410.1164v2, Theorem6.16 and Corollary6.17.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.KummerFlatSiteComparisonModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open EtaleLogSchemes EtaleLogDiagrams EtaleLogNativeCategory
open DenominatorRootStacks FiniteRootTowers KatoChartCoefficientModels LogRootSourceModels
open InfiniteRootPreservationModels RepresentableStackFppfModels RepresentableStackFppfSites
open CanonicalKummerFlatSiteModels NativeKummerFlatModels

variable [InverseImageTheory.{0}] [N : NativeCategoryModel.{0}]
  (I : NativeDFImages.{0}) (D : RegularSectionComparisons)
  (X : LogScheme.{0}) (RX : RootRealization X D I)
  [HasBaseChanges RX.infinite.stack] [∀ n : Exponent, HasBaseChanges (RX.finite n).stack]
  (S : NativeSiteCategory RX.infinite.stack) (F : FunctorModel I D X RX S)

/-- The source topos comparison hypotheses are actual local cover data. -/
structure LocalRefinements where
  objects : letI := S.category
    ∀ A : Chart RX.infinite.stack, ∃ (ι : Type 3)
      (U : ι → NativeKummerFlatModels.Site D X) (a : ∀ i, F.functor.obj (U i) ⟶ A),
      IsCover S A (fun i => F.functor.obj (U i)) a
  arrows : letI := S.category
    ∀ (U V : NativeKummerFlatModels.Site D X) (a : F.functor.obj U ⟶ F.functor.obj V),
      ∃ (ι : Type) (W : ι → NativeKummerFlatModels.Site D X)
        (g : ∀ i, W i ⟶ U) (h : ∀ i, W i ⟶ V),
        Sieve.ofArrows W g ∈ NativeKummerFlatModels.topology D X U ∧
          ∀ i, F.functor.map (g i) ≫ a = F.functor.map (h i)
  equality : letI := S.category
    ∀ {U V : NativeKummerFlatModels.Site D X} (a b : U ⟶ V),
      F.functor.map a = F.functor.map b →
        ∃ (ι : Type) (W : ι → NativeKummerFlatModels.Site D X) (g : ∀ i, W i ⟶ U),
          Sieve.ofArrows W g ∈ NativeKummerFlatModels.topology D X U ∧
            ∀ i, g i ≫ a = g i ≫ b

abbrev sourceTopology := NativeKummerFlatModels.topology D X

def targetTopology : letI := S.category; GrothendieckTopology (Chart RX.infinite.stack) :=
  RepresentableStackFppfSites.topology S

/-- Continuity only concerns the preceding fixed source functor. -/
def IsContinuous : Prop :=
  letI := S.category
  F.functor.IsContinuous (sourceTopology D X) (targetTopology I D X RX S)

/-- Target covers lift to actual source covers; this is the source's
cocontinuity condition, independently of local arrow density. -/
def IsCocontinuous : Prop :=
  letI := S.category
  F.functor.IsCocontinuous (sourceTopology D X) (targetTopology I D X RX S)

section Sheaves

variable {A : Type 3} [Category A]
  [HasSheafify (sourceTopology D X) A]
  (h : IsContinuous I D X RX S F)

/-- Native restriction is the displayed source sheaf pushforward. -/
def sheafPushforward : letI := S.category
    Sheaf (targetTopology I D X RX S) A ⥤ Sheaf (sourceTopology D X) A := by
  letI := S.category
  letI : F.functor.IsContinuous (sourceTopology D X) (targetTopology I D X RX S) := h
  exact F.functor.sheafPushforwardContinuous A (sourceTopology D X) (targetTopology I D X RX S)

variable [((sheafPushforward I D X RX S F h) :
  (letI := S.category; Sheaf (targetTopology I D X RX S) A ⥤ Sheaf (sourceTopology D X) A)).IsRightAdjoint]

def sheafPullback : letI := S.category
    Sheaf (sourceTopology D X) A ⥤ Sheaf (targetTopology I D X RX S) A := by
  letI := S.category
  exact (sheafPushforward I D X RX S F h).leftAdjoint

def sheafAdjunction : letI := S.category
    sheafPullback I D X RX S F (A := A) h ⊣ sheafPushforward I D X RX S F (A := A) h := by
  letI := S.category
  exact Adjunction.ofIsRightAdjoint (sheafPushforward I D X RX S F (A := A) h)

variable [targetSheafify : letI := S.category; HasSheafify (targetTopology I D X RX S) A]
  [leftKan : letI := S.category
    ∀ P : (NativeKummerFlatModels.Site D X)ᵒᵖ ⥤ A, F.functor.op.HasLeftKanExtension P]

/-- Literal native left-Kan extension followed by target sheafification. -/
def sheafifiedLan : letI := S.category
    Sheaf (sourceTopology D X) A ⥤ Sheaf (targetTopology I D X RX S) A := by
  letI := S.category
  letI := targetSheafify
  letI := leftKan
  letI : F.functor.IsContinuous (sourceTopology D X) (targetTopology I D X RX S) := h
  exact Functor.sheafPullbackConstruction.sheafPullback F.functor A
    (sourceTopology D X) (targetTopology I D X RX S)

def sheafifiedLanAdjunction : letI := S.category
    sheafifiedLan I D X RX S F (A := A) ⊣ sheafPushforward I D X RX S F (A := A) h := by
  letI := S.category
  letI := targetSheafify
  letI := leftKan
  letI : F.functor.IsContinuous (sourceTopology D X) (targetTopology I D X RX S) := h
  exact Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F.functor A
    (sourceTopology D X) (targetTopology I D X RX S)

/-- The inverse-image comparison is native uniqueness of these actual adjoints. -/
def sheafPullbackLanIso : letI := S.category
    sheafPullback I D X RX S F (A := A) h ≅ sheafifiedLan I D X RX S F (A := A) := by
  letI := S.category
  exact Adjunction.leftAdjointUniq (sheafAdjunction I D X RX S F (A := A) h)
    (sheafifiedLanAdjunction I D X RX S F (A := A) h)

end Sheaves

end MathlibExt.AlgebraicGeometry.KummerFlatSiteComparisonModels
