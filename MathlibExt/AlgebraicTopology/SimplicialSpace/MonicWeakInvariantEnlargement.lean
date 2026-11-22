/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LocalReplacementDeformation
import MathlibExt.AlgebraicTopology.SimplicialSpace.LocalReplacementDeformationRestriction

/-!
# Bounded invariant enlargement of a monic Rezk weak equivalence

For the same canonical replacement and stable cardinal envelope, enlarge a
prescribed bounded original subpresheaf of the target until the selected
stationary deformation restricts.  The literal pullback projection then has
bounded source and target and is a genuine Rezk weak equivalence.

The packet retains the selected global deformation, its invariant closure,
the restricted deformation, every cardinal bound, monicity, and the exact
restriction equations.  No second replacement or unrelated deformation data
is chosen.
-/

set_option autoImplicit false
noncomputable section

universe u

open Cardinal CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.MorphismProperty

namespace SimplicialSpace

/-- The complete prescribed-image enlargement packet for one original monic
Rezk weak equivalence. -/
structure MonicWeakInvariantEnlargement
    {κ : Cardinal.{u}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ]
    (e : LocalReplacementCardinalEnvelope κ)
    {X Y : SimplicialSpace.{u}} (i : X ⟶ Y)
    (U : Subfunctor (toPresheaf.obj Y)) where
  /-- The already selected strong deformation of the canonical Q-map. -/
  canonicalDeformation : innerOneSimplexPrecylinder.StrongDeformationData
    ((SmallObject.terminalIteration LocalGenerators.J.{u} κ).map i)
  /-- The bounded invariant original subpresheaf containing U. -/
  invariant : LocalReplacementInvariantSubpresheaf e Y
    canonicalDeformation.homotopy.h U
  /-- The same deformation restricted across the Q-preserved pullback. -/
  restricted : RestrictedLocalReplacementDeformation e i
    canonicalDeformation invariant
  /-- Native total points of the preimage subpresheaf remain bounded. -/
  preimage_points_le : Cardinal.mk
    (originalSubpresheafPreimage i invariant.V).toFunctor.Elements ≤ e.γ
  /-- Raw total points of the literal categorical pullback remain bounded. -/
  pullback_raw_points_le : Cardinal.mk (Functor.uncurry.obj
    (pullback i (originalSubpresheafInclusion invariant.V)).diagram).Elements ≤ e.γ
  /-- The literal pullback projection is monic. -/
  projection_mono : Mono
    (pullback.snd i (originalSubpresheafInclusion invariant.V))
  /-- The literal pullback projection is a genuine all-CSS Rezk weak map. -/
  projection_weak : rezkWeakEquivalences
    (pullback.snd i (originalSubpresheafInclusion invariant.V))

/-- Every prescribed bounded original subpresheaf admits one bounded invariant
enlargement for the same canonical Q and the same selected deformation. -/
theorem LocalReplacementCardinalEnvelope.exists_monicWeakInvariantEnlargement
    {κ : Cardinal.{u}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ]
    (e : LocalReplacementCardinalEnvelope κ)
    {X Y : SimplicialSpace.{u}} (i : X ⟶ Y) [Mono i]
    (hi : rezkWeakEquivalences i)
    (U : Subfunctor (toPresheaf.obj Y))
    (hU : Cardinal.mk U.toFunctor.Elements ≤ e.γ) :
    Nonempty (MonicWeakInvariantEnlargement e i U) := by
  let Q := SmallObject.terminalIteration LocalGenerators.J.{u} κ
  obtain ⟨D⟩ := canonical_localReplacement_strongDeformation κ i hi
  obtain ⟨C⟩ := e.exists_invariantSubpresheaf Y D.homotopy.h U hU
  obtain ⟨R⟩ := exists_restrictedLocalReplacementDeformation e i D C
  let p := pullback.snd i (originalSubpresheafInclusion C.V)
  have hpre := originalSubpresheafPreimage_mk_elements_le i C.V e.γ C.points_le
  have hpull : Cardinal.mk (Functor.uncurry.obj
      (pullback i (originalSubpresheafInclusion C.V)).diagram).Elements ≤ e.γ :=
    originalSubpresheafPullback_mk_elements_le i C.V e.γ C.points_le
  let hpMono : Mono p := inferInstance
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  have hQp : WeakEquivalence (Q.map p) :=
    (weakEquivalence_iff (Q.map p)).2 R.qProjection_weak
  have hpWeak : rezkWeakEquivalences p :=
    (canonical_terminalIteration_weak_detection κ p).2 hQp
  exact ⟨{
    canonicalDeformation := D
    invariant := C
    restricted := R
    preimage_points_le := hpre.1
    pullback_raw_points_le := hpull
    projection_mono := hpMono
    projection_weak := hpWeak }⟩

end SimplicialSpace
