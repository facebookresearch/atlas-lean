/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.StrongDeformationRestriction
import MathlibExt.AlgebraicTopology.SimplicialSpace.CanonicalTerminalIterationPreservation
import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerStrongDeformationWeakEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSpace.LocalReplacementInvariantClosure

/-!
# Restricting the canonical deformation across an invariant pullback

An invariant original subpresheaf of the target determines a literal pullback
of the original monomorphism.  Pullback preservation by the same canonical Q
constructs the restricted retraction.  The stored invariant homotopy and the
generic restriction theorem then give strong deformation data on the Q-image
of that pullback projection.

The returned packet retains its exact retraction and homotopy equations with
the selected global deformation.  Its Q-map is weak in the named Reedy model.
-/

set_option autoImplicit false
noncomputable section

universe u

open Cardinal CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.MorphismProperty

namespace SimplicialSpace

/-- The selected global deformation restricted to the Q-image of the literal
pullback projection over an invariant original subpresheaf. -/
structure RestrictedLocalReplacementDeformation
    {κ : Cardinal.{u}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ]
    (e : LocalReplacementCardinalEnvelope κ)
    {X Y : SimplicialSpace.{u}} (i : X ⟶ Y)
    (D : innerOneSimplexPrecylinder.StrongDeformationData
      ((SmallObject.terminalIteration LocalGenerators.J.{u} κ).map i))
    {U : Subfunctor (toPresheaf.obj Y)}
    (C : LocalReplacementInvariantSubpresheaf e Y D.homotopy.h U) where
  /-- Strong deformation data on the Q-image of the actual pullback projection. -/
  deformation : innerOneSimplexPrecylinder.StrongDeformationData
    ((SmallObject.terminalIteration LocalGenerators.J.{u} κ).map
      (pullback.snd i (originalSubpresheafInclusion C.V)))
  /-- The local retraction followed by the Q-image of the first projection is
  the global retraction restricted along QV. -/
  retraction_fac : deformation.retraction ≫
      (SmallObject.terminalIteration LocalGenerators.J.{u} κ).map
        (pullback.fst i (originalSubpresheafInclusion C.V)) =
    (SmallObject.terminalIteration LocalGenerators.J.{u} κ).map
        (originalSubpresheafInclusion C.V) ≫ D.retraction
  /-- The local retraction followed by the Q-image of the pullback projection
  is the endpoint-one restriction of the invariant homotopy. -/
  retraction_projection_fac : deformation.retraction ≫
      (SmallObject.terminalIteration LocalGenerators.J.{u} κ).map
        (pullback.snd i (originalSubpresheafInclusion C.V)) =
    (innerOneSimplexPrecylinder.app
      ((SmallObject.terminalIteration LocalGenerators.J.{u} κ).obj
        (originalSubpresheafObject C.V))).i₁ ≫ C.restrictedHomotopy
  /-- The selected global homotopy restricts to the local homotopy with the
  exact original inclusion equation. -/
  homotopy_fac : innerOneSimplexPrecylinder.I.map
      ((SmallObject.terminalIteration LocalGenerators.J.{u} κ).map
        (originalSubpresheafInclusion C.V)) ≫ D.homotopy.h =
    deformation.homotopy.h ≫
      (SmallObject.terminalIteration LocalGenerators.J.{u} κ).map
        (originalSubpresheafInclusion C.V)
  /-- The Q-image of the pullback projection is monic. -/
  qProjection_mono : Mono
    ((SmallObject.terminalIteration LocalGenerators.J.{u} κ).map
      (pullback.snd i (originalSubpresheafInclusion C.V)))
  /-- The Q-image of the pullback projection is weak in the named Reedy model. -/
  qProjection_weak :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    weakEquivalences SimplicialSpace.{u}
      ((SmallObject.terminalIteration LocalGenerators.J.{u} κ).map
        (pullback.snd i (originalSubpresheafInclusion C.V)))

/-- Pullback preservation by the same canonical Q restricts the selected
global strong deformation to every invariant original subpresheaf. -/
theorem exists_restrictedLocalReplacementDeformation
    {κ : Cardinal.{u}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ]
    (e : LocalReplacementCardinalEnvelope κ)
    {X Y : SimplicialSpace.{u}} (i : X ⟶ Y) [Mono i]
    (D : innerOneSimplexPrecylinder.StrongDeformationData
      ((SmallObject.terminalIteration LocalGenerators.J.{u} κ).map i))
    {U : Subfunctor (toPresheaf.obj Y)}
    (C : LocalReplacementInvariantSubpresheaf e Y D.homotopy.h U) :
    Nonempty (RestrictedLocalReplacementDeformation e i D C) := by
  let Q := SmallObject.terminalIteration LocalGenerators.J.{u} κ
  let P := innerOneSimplexPrecylinder
  let j := originalSubpresheafInclusion C.V
  let a := pullback.fst i j
  let b := pullback.snd i j
  let k := Q.map j
  let _ : Q.PreservesMonomorphisms :=
    canonical_terminalIteration_preservesMonomorphisms κ
  let _ : PreservesLimitsOfShape WalkingCospan Q :=
    canonical_terminalIteration_preservesPullbacks κ
  let _ : Mono j := originalSubpresheafInclusion_mono C.V
  let _ : Mono a := inferInstance
  let _ : Mono b := inferInstance
  let _ : Mono (Q.map a) := inferInstance
  let _ : Mono (Q.map b) := inferInstance
  let _ : Mono k := inferInstance
  let h₁V := (P.app (Q.obj (originalSubpresheafObject C.V))).i₁ ≫
    C.restrictedHomotopy
  have comm : (k ≫ D.retraction) ≫ Q.map i = h₁V ≫ k := by
    calc
      _ = k ≫ ((P.app (Q.obj Y)).i₁ ≫ D.homotopy.h) := by
        rw [D.homotopy.h₁, Category.assoc]
      _ = (P.app (Q.obj (originalSubpresheafObject C.V))).i₁ ≫
          (P.I.map k ≫ D.homotopy.h) := by
        simpa only [Functor.id_map, Category.assoc] using
          congrArg (fun q => q ≫ D.homotopy.h) (P.i₁.naturality k)
      _ = h₁V ≫ k := by
        rw [C.fac]
        dsimp only [h₁V, k, j, Q, P]
        rw [Category.assoc]
  let pullbackIso := PreservesPullback.iso Q i j
  let t := pullback.lift (k ≫ D.retraction) h₁V comm
  let rV := t ≫ pullbackIso.inv
  have hr₁ : rV ≫ Q.map a = k ≫ D.retraction := by
    simp only [rV, pullbackIso, t, a, k, Category.assoc,
      PreservesPullback.iso_inv_fst, pullback.lift_fst]
  have hr₂ : rV ≫ Q.map b = h₁V := by
    simp only [rV, pullbackIso, t, b, k, Category.assoc,
      PreservesPullback.iso_inv_snd, pullback.lift_snd]
  have square : Q.map a ≫ Q.map i = Q.map b ≫ k := by
    simp only [a, b, k, ← Q.map_comp, pullback.condition]
  let D₀ := D.restrict (Q.map a) (Q.map b) k square rV hr₁
    C.restrictedHomotopy C.fac
  have hweak :
      letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
      weakEquivalences SimplicialSpace.{u} (Q.map b) :=
    ReedyModel.weakEquivalence_of_innerStrongDeformationData D₀
  refine ⟨{
    deformation := D₀
    retraction_fac := hr₁
    retraction_projection_fac := hr₂
    homotopy_fac := ?_
    qProjection_mono := inferInstance
    qProjection_weak := hweak }⟩
  exact C.fac

end SimplicialSpace
