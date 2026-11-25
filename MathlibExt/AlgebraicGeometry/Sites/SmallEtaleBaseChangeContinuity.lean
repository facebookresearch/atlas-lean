/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleBaseChange
public import Mathlib.Algebra.Category.Grp.Basic

/-! # Covers and continuity under actual small étale base change -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u v w

namespace AlgebraicGeometry.Scheme.DerivedSections

set_option backward.isDefEq.respectTransparency.types false in
/-- Base change preserves every covering sieve on the actual small étale site. -/
theorem smallEtaleBaseChange_coverPreserving {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CoverPreserving Y.smallEtaleTopology X.smallEtaleTopology (smallEtaleBaseChange f) := by
  let J := Scheme.etaleTopology.{u}
  let F := Scheme.Etale.forget Y
  let G := Scheme.Etale.forget X
  let : G.LocallyCoverDense (J.over X) :=
    Scheme.locallyCoverDense_of_le X
      (P := @AlgebraicGeometry.Etale.{u}) (Q := @AlgebraicGeometry.Etale.{u}) le_rfl
  let : F.LocallyCoverDense (J.over Y) :=
    Scheme.locallyCoverDense_of_le Y
      (P := @AlgebraicGeometry.Etale.{u}) (Q := @AlgebraicGeometry.Etale.{u}) le_rfl
  let : G.IsCocontinuous X.smallEtaleTopology (J.over X) := by
    change G.IsCocontinuous (G.restrictedTopology (J.over X)) (J.over X)
    infer_instance
  have hF : CoverPreserving Y.smallEtaleTopology (J.over Y) F := by
    change CoverPreserving (F.restrictedTopology (J.over Y)) (J.over Y) F
    exact F.coverPreserving_restrictedTopology (J.over Y)
  have hComposite :
      CoverPreserving Y.smallEtaleTopology (J.over X) (smallEtaleBaseChange f ⋙ G) := by
    change CoverPreserving Y.smallEtaleTopology (J.over X) (F ⋙ CategoryTheory.Over.pullback f)
    exact CoverPreserving.comp (J := Y.smallEtaleTopology) (K := J.over Y)
      hF (J.coverPreserving_overPullback f)
  exact CoverPreserving.of_comp_of_isCocontinuous
    (J := Y.smallEtaleTopology) (K := X.smallEtaleTopology) G hComposite

/-- The very same indexed covering family remains étale and jointly surjective
after base change, with no bound tying the indexing universe to the scheme universe. -/
theorem smallEtaleBaseChange_generatingCovers
    {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type v}
    {V : Y.Etale} {U : ι → Y.Etale} (g : ∀ i, U i ⟶ V)
    (hg : (⋃ i, Set.range (g i).left) = Set.univ) :
    (∀ i, AlgebraicGeometry.Etale (((smallEtaleBaseChange f).map (g i)).left)) ∧
      (⋃ i, Set.range (((smallEtaleBaseChange f).map (g i)).left)) = Set.univ := by
  refine ⟨fun i => inferInstance, ?_⟩
  apply (Scheme.ofArrows_mem_smallEtaleTopology_iff
    (fun i => (smallEtaleBaseChange f).map (g i))).mp
  have hCover := (Scheme.ofArrows_mem_smallEtaleTopology_iff g).mpr hg
  simpa only [Sieve.functorPushforward_ofArrows] using
    (smallEtaleBaseChange_coverPreserving f).cover_preserve hCover

/-- The actual original-site base-change functor is continuous for every `f`. -/
theorem smallEtaleBaseChange_isContinuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (smallEtaleBaseChange f).IsContinuous Y.smallEtaleTopology X.smallEtaleTopology := by
  let : PreservesFiniteLimits (smallEtaleBaseChange f) :=
    smallEtaleBaseChange_preservesFiniteLimits f
  let : RepresentablyFlat (smallEtaleBaseChange f) :=
    flat_of_preservesFiniteLimits (smallEtaleBaseChange f)
  exact Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat X.smallEtaleTopology (smallEtaleBaseChange f))
    (smallEtaleBaseChange_coverPreserving f)

/-- The literal precomposition sends every original abelian sheaf to a sheaf,
in an arbitrary independent coefficient universe. -/
theorem smallEtaleBaseChange_precomp_isSheaf
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}) :
    Presheaf.IsSheaf Y.smallEtaleTopology ((smallEtaleBaseChange f).op ⋙ F.obj) := by
  let := smallEtaleBaseChange_isContinuous f
  exact (smallEtaleBaseChange f).op_comp_isSheaf Y.smallEtaleTopology X.smallEtaleTopology F


end AlgebraicGeometry.Scheme.DerivedSections
