/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerOneSimplexCylinder
import MathlibExt.AlgebraicTopology.SimplicialSpace.CanonicalTerminalIterationPreservation
import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalSubpresheafPullback
import MathlibExt.CategoryTheory.Subfunctor.TransfiniteCardinality

/-!
# One bounded support step for a local-replacement deformation

Given a bounded literal subpresheaf `V` of `Y`, support the entire image of
the inner cylinder on `Q(V)` under a fixed map `I(QY) ⟶ QY`.  Joining that
support to `V` gives one bounded `W` and an actual whole map
`I(Q(V)) ⟶ Q(W)` with its exact inclusion equation.

All points and bidegrees are retained through the canonical raw/presheaf
comparison.  No vertex-only support, second replacement, closure packet or
transfinite union is used in this one-step result.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

universe u

open Cardinal CategoryTheory CategoryTheory.Limits
open CategoryTheory.MorphismProperty HomotopicalAlgebra

namespace SimplicialSpace

/-- One bounded enlargement step retaining the whole cylinder-image factor. -/
structure LocalReplacementDeformationSuccessor
    {κ : Cardinal.{u}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ]
    (e : LocalReplacementCardinalEnvelope κ) (Y : SimplicialSpace.{u})
    (H : innerOneSimplexPrecylinder.I.obj
      ((SmallObject.terminalIteration LocalGenerators.J.{u} κ).obj Y) ⟶
      (SmallObject.terminalIteration LocalGenerators.J.{u} κ).obj Y)
    (V : Subfunctor (toPresheaf.obj Y)) where
  /-- The bounded successor subpresheaf. -/
  W : Subfunctor (toPresheaf.obj Y)
  /-- The original stage is literally contained in its successor. -/
  le : V ≤ W
  /-- Native total points of the successor stay within the envelope. -/
  points_le : Cardinal.mk W.toFunctor.Elements ≤ e.γ
  /-- Raw original total points of the realized successor stay bounded. -/
  raw_points_le : Cardinal.mk
    (Functor.uncurry.obj (originalSubpresheafObject W).diagram).Elements ≤ e.γ
  /-- The whole restricted cylinder map lifted into the successor replacement. -/
  lift : innerOneSimplexPrecylinder.I.obj
      ((SmallObject.terminalIteration LocalGenerators.J.{u} κ).obj
        (originalSubpresheafObject V)) ⟶
    (SmallObject.terminalIteration LocalGenerators.J.{u} κ).obj
      (originalSubpresheafObject W)
  /-- Composing the lift with the original Q-inclusion recovers the supplied map. -/
  fac : innerOneSimplexPrecylinder.I.map
        ((SmallObject.terminalIteration LocalGenerators.J.{u} κ).map
          (originalSubpresheafInclusion V)) ≫ H =
      lift ≫ (SmallObject.terminalIteration LocalGenerators.J.{u} κ).map
        (originalSubpresheafInclusion W)

/-- Every bounded literal subpresheaf admits one bounded successor supporting
the full restricted deformation image. -/
theorem LocalReplacementCardinalEnvelope.exists_deformationSuccessor
    {κ : Cardinal.{u}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ]
    (e : LocalReplacementCardinalEnvelope κ) (Y : SimplicialSpace.{u})
    (H : innerOneSimplexPrecylinder.I.obj
      ((SmallObject.terminalIteration LocalGenerators.J.{u} κ).obj Y) ⟶
      (SmallObject.terminalIteration LocalGenerators.J.{u} κ).obj Y)
    (V : Subfunctor (toPresheaf.obj Y))
    (hV : Cardinal.mk V.toFunctor.Elements ≤ e.γ) :
    Nonempty (LocalReplacementDeformationSuccessor e Y H V) := by
  classical
  let Q := SmallObject.terminalIteration LocalGenerators.J.{u} κ
  let A := originalSubpresheafObject V
  let v := originalSubpresheafInclusion V
  let f : innerOneSimplexPrecylinder.I.obj (Q.obj A) ⟶ Q.obj Y :=
    innerOneSimplexPrecylinder.I.map (Q.map v) ≫ H
  have hA : Cardinal.mk (Functor.uncurry.obj A.diagram).Elements ≤ e.γ :=
    originalSubpresheaf_mk_elements_le V e.γ hV
  have hQA : Cardinal.mk (Functor.uncurry.obj (Q.obj A).diagram).Elements ≤ e.γ :=
    e.replacementPoints_le A hA
  have hIA : Cardinal.mk (Functor.uncurry.obj
      (innerOneSimplexPrecylinder.I.obj (Q.obj A)).diagram).Elements ≤ e.γ := by
    simpa only [innerOneSimplexPrecylinder_I] using
      e.innerCylinder_le (Q.obj A) hQA
  let mapPoint := (Functor.uncurry.map f.hom).mapElements.obj
  let S : Set (Functor.uncurry.obj (Q.obj Y).diagram).Elements := Set.range mapPoint
  let encode : (Functor.uncurry.obj
      (innerOneSimplexPrecylinder.I.obj (Q.obj A)).diagram).Elements → S :=
    fun x => ⟨mapPoint x, ⟨x, rfl⟩⟩
  have hencode : Function.Surjective encode := by
    rintro ⟨_, x, rfl⟩
    exact ⟨x, rfl⟩
  have hS : Cardinal.mk S ≤ e.γ :=
    (Cardinal.mk_le_of_surjective hencode).trans hIA
  obtain ⟨Z, hZ, _hZraw, _hmonoZ, φ, hφ⟩ := e.exists_bounded_support Y S hS
  let W := V ⊔ Z
  have hW : Cardinal.mk W.toFunctor.Elements ≤ e.γ :=
    Subfunctor.mk_elements_sup_le_of_le V Z e.aleph0_le_γ hV hZ
  have hWraw : Cardinal.mk
      (Functor.uncurry.obj (originalSubpresheafObject W).diagram).Elements ≤ e.γ :=
    originalSubpresheaf_mk_elements_le W e.γ hW
  let zW : originalSubpresheafObject Z ⟶ originalSubpresheafObject W :=
    originalSubpresheafMapOfLE le_sup_right
  let m : Q.obj (originalSubpresheafObject W) ⟶ Q.obj Y :=
    Q.map (originalSubpresheafInclusion W)
  let _ : Q.PreservesMonomorphisms :=
    canonical_terminalIteration_preservesMonomorphisms κ
  let _ : Mono m := inferInstance
  have hrange : Subfunctor.range (toPresheaf.map f) ≤
      Subfunctor.range (toPresheaf.map m) := by
    apply Subfunctor.range_le_range_of_app
    intro p x
    let xElem : (toPresheaf.obj
        (innerOneSimplexPrecylinder.I.obj (Q.obj A))).Elements :=
      Functor.elementsMk _ p x
    let xRaw := (totalPointsEquivToPresheaf _).symm xElem
    let s : S := ⟨mapPoint xRaw, ⟨xRaw, rfl⟩⟩
    let zRaw := φ s
    let wRaw := (Functor.uncurry.map (Q.map zW).hom).mapElements.obj zRaw
    let wElem := totalPointsEquivToPresheaf (Q.obj (originalSubpresheafObject W)) wRaw
    have hz := congrFun hφ s
    have hzW :
        (Functor.uncurry.map m.hom).mapElements.obj wRaw = mapPoint xRaw := by
      dsimp only [wRaw]
      have hcomp : Q.map zW ≫ m = Q.map (originalSubpresheafInclusion Z) := by
        dsimp only [m]
        rw [← Q.map_comp, originalSubpresheafMapOfLE_inclusion]
      change (Functor.uncurry.map ((Q.map zW ≫ m).hom)).mapElements.obj zRaw = _
      rw [hcomp]
      exact hz
    have hpEq : wElem.obj = p := by
      have hh := congrArg (fun q => q.obj)
        (totalPointsEquivToPresheaf_map m wRaw)
      have hfobj : (totalPointsEquivToPresheaf _ (mapPoint xRaw)).obj = p := by
        have hxmap := totalPointsEquivToPresheaf_map f xRaw
        change (totalPointsEquivToPresheaf _ (mapPoint xRaw)).obj = p
        rw [hxmap]
        rfl
      rw [← hzW] at hfobj
      exact hh.symm.trans hfobj
    let y := (toPresheaf.obj (Q.obj (originalSubpresheafObject W))).map
      (eqToHom hpEq) wElem.val
    let yElem : (toPresheaf.obj (Q.obj (originalSubpresheafObject W))).Elements :=
      Functor.elementsMk _ p y
    have hwy : wElem = yElem :=
      Functor.Elements.ext wElem yElem hpEq rfl
    refine ⟨y, ?_⟩
    have helemW : (toPresheaf.map m).mapElements.obj wElem =
        (toPresheaf.map f).mapElements.obj xElem := by
      calc
        _ = totalPointsEquivToPresheaf (Q.obj Y)
              ((Functor.uncurry.map m.hom).mapElements.obj wRaw) :=
            (totalPointsEquivToPresheaf_map m wRaw).symm
        _ = totalPointsEquivToPresheaf (Q.obj Y) (mapPoint xRaw) := by rw [hzW]
        _ = (toPresheaf.map f).mapElements.obj
              (totalPointsEquivToPresheaf _ xRaw) :=
            totalPointsEquivToPresheaf_map f xRaw
        _ = _ := by rw [Equiv.apply_symm_apply]
    have helem : (toPresheaf.map m).mapElements.obj yElem =
        (toPresheaf.map f).mapElements.obj xElem := by
      rw [← hwy]
      exact helemW
    exact eq_of_heq (Functor.Elements.mk.inj helem).2
  let lPresheaf := NatTrans.factorThruMono (toPresheaf.map f) (toPresheaf.map m) hrange
  let l := toPresheaf.preimage lPresheaf
  have hfac : l ≫ m = f := by
    apply toPresheaf.map_injective
    rw [Functor.map_comp]
    dsimp only [l]
    rw [Functor.map_preimage]
    exact NatTrans.factorThruMono_comp _ _ _
  exact ⟨{
    W := W
    le := le_sup_left
    points_le := hW
    raw_points_le := hWraw
    lift := l
    fac := hfac.symm }⟩


end SimplicialSpace
