/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LocalReplacementCardinalEnvelope
import MathlibExt.CategoryTheory.NatTrans.Elements
import MathlibExt.CategoryTheory.Subfunctor.CardinalPresentation
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# Simultaneous support for points of the canonical local replacement

The canonical presheaf equivalence transports the same local-replacement functor
to the product-site presheaf category. Accessibility then gives one bounded
original subpresheaf supporting every supplied bounded family of replacement
points at once.
-/

set_option autoImplicit false
noncomputable section

universe u

open Cardinal CategoryTheory CategoryTheory.Limits
open CategoryTheory.MorphismProperty

namespace SimplicialSpace

/-- The same canonical local replacement, conjugated to the outer-first
product-site presheaf category. -/
private def presheafLocalReplacement
    (κ : Cardinal.{u}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ] :
    ((SimplexCategory × SimplexCategory)ᵒᵖ ⥤ Type u) ⥤
      ((SimplexCategory × SimplexCategory)ᵒᵖ ⥤ Type u) :=
  equivalencePresheaf.inverse ⋙
    SmallObject.terminalIteration LocalGenerators.J.{u} κ ⋙
      equivalencePresheaf.functor

/-- Regard a native subfunctor of the canonical presheaf carrier as an original
simplicial space. -/
def originalSubpresheafObject {X : SimplicialSpace.{u}}
    (U : Subfunctor (toPresheaf.obj X)) : SimplicialSpace.{u} :=
  equivalencePresheaf.inverse.obj U.toFunctor

/-- The original inclusion of a native subfunctor, transported back to the
designated simplicial-space carrier. -/
def originalSubpresheafInclusion {X : SimplicialSpace.{u}}
    (U : Subfunctor (toPresheaf.obj X)) :
    originalSubpresheafObject U ⟶ X :=
  equivalencePresheaf.inverse.map U.ι ≫ (equivalencePresheaf.unitIso.app X).inv

instance originalSubpresheafInclusion_mono {X : SimplicialSpace.{u}}
    (U : Subfunctor (toPresheaf.obj X)) :
    Mono (originalSubpresheafInclusion U) := by
  let _ : equivalencePresheaf.inverse.PreservesMonomorphisms := inferInstance
  change Mono (equivalencePresheaf.inverse.map U.ι ≫
    (equivalencePresheaf.unitIso.app X).inv)
  infer_instance

/-- The realized original subpresheaf has exactly the native total points of
the literal subfunctor. -/
def originalSubpresheafTotalPointsEquiv {X : SimplicialSpace.{u}}
    (U : Subfunctor (toPresheaf.obj X)) :
    (Functor.uncurry.obj (originalSubpresheafObject U).diagram).Elements ≃
      U.toFunctor.Elements :=
  (totalPointsEquivToPresheaf (originalSubpresheafObject U)).trans
    (Functor.Elements.equivOfIso
      (equivalencePresheaf.counitIso.app U.toFunctor))

/-- A literal bounded subfunctor realizes to an original simplicial space with
the same total-point bound. -/
theorem originalSubpresheaf_mk_elements_le {X : SimplicialSpace.{u}}
    (U : Subfunctor (toPresheaf.obj X)) (γ : Cardinal.{u})
    (hU : Cardinal.mk U.toFunctor.Elements ≤ γ) :
    Cardinal.mk
        (Functor.uncurry.obj (originalSubpresheafObject U).diagram).Elements ≤
      γ := by
  rw [Cardinal.mk_congr (originalSubpresheafTotalPointsEquiv U)]
  exact hU

/-- On the original carrier image, the conjugated replacement identifies with
the same replacement followed by the presheaf equivalence. -/
private def presheafLocalReplacementComparisonIso
    (κ : Cardinal.{u}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ]
    (X : SimplicialSpace.{u}) :
    (presheafLocalReplacement κ).obj (toPresheaf.obj X) ≅
      toPresheaf.obj
        ((SmallObject.terminalIteration LocalGenerators.J.{u} κ).obj X) :=
  equivalencePresheaf.functor.mapIso
    ((SmallObject.terminalIteration LocalGenerators.J.{u} κ).mapIso
      (equivalencePresheaf.unitIso.app X).symm)

/-- The conjugated presheaf replacement is accessible at the same envelope
cardinal. -/
private theorem LocalReplacementCardinalEnvelope.presheafQ_isCardinalAccessible
    {κ : Cardinal.{u}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ]
    (e : LocalReplacementCardinalEnvelope κ) :
    letI : Fact e.μ.IsRegular := e.regular_μ
    (presheafLocalReplacement κ).IsCardinalAccessible e.μ := by
  let _ : Fact e.μ.IsRegular := e.regular_μ
  let _ :
      (SmallObject.terminalIteration LocalGenerators.J.{u} κ).IsCardinalAccessible
        e.μ :=
    e.q_isCardinalAccessible
  dsimp [presheafLocalReplacement]
  infer_instance

private theorem canonicalQ_preservesMonomorphisms
    (κ : Cardinal.{u}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ] :
    (SmallObject.terminalIteration LocalGenerators.J.{u} κ).PreservesMonomorphisms := by
  let t := terminal.fromNatTrans SimplicialSpace.{u}
  let d := SmallObject.functorialFactorizationData LocalGenerators.J.{u} κ
  let r := (d.functorCategory SimplicialSpace.{u}).factorizationData t
  have h : r.Z.PreservesMonomorphisms :=
    canonical_localReplacement_preservesMonomorphisms κ
  rw [SmallObject.canonical_terminal_middle_eq_terminalIteration
    LocalGenerators.J.{u} κ] at h
  exact h

/-- Every at-most-γ family of actual canonical-Q points is supported
simultaneously on one at-most-γ original subpresheaf. The returned point lifts
retain their original product-site degrees and map to the supplied points under
the same Q applied to the original inclusion. -/
private theorem LocalReplacementCardinalEnvelope.exists_presheaf_support
    {κ : Cardinal.{u}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ]
    (e : LocalReplacementCardinalEnvelope κ) (X : SimplicialSpace.{u})
    (S : Set (toPresheaf.obj
      ((SmallObject.terminalIteration LocalGenerators.J.{u} κ).obj X)).Elements)
    (hS : Cardinal.mk S ≤ e.γ) :
    ∃ U : Subfunctor (toPresheaf.obj X),
      Cardinal.mk U.toFunctor.Elements ≤ e.γ ∧
        Mono ((SmallObject.terminalIteration LocalGenerators.J.{u} κ).map
          (originalSubpresheafInclusion U)) ∧
        ∃ φ : S →
            ((presheafLocalReplacement κ).obj U.toFunctor).Elements,
          (((toPresheaf.map
              ((SmallObject.terminalIteration LocalGenerators.J.{u} κ).map
                (originalSubpresheafInclusion U))).mapElements).obj ∘ φ) =
            Subtype.val := by
  classical
  let _ : Fact e.μ.IsRegular := e.regular_μ
  let Q := SmallObject.terminalIteration LocalGenerators.J.{u} κ
  let T := presheafLocalReplacement κ
  let _ : T.IsCardinalAccessible e.μ := e.presheafQ_isCardinalAccessible
  let qIso := presheafLocalReplacementComparisonIso κ X
  let qElements := Functor.Elements.equivOfIso qIso
  let pullPoint : S → (T.obj (toPresheaf.obj X)).Elements :=
    fun s => qElements.symm s.val
  let S' : Set (T.obj (toPresheaf.obj X)).Elements := Set.range pullPoint
  let encode : S → S' := fun s => ⟨pullPoint s, ⟨s, rfl⟩⟩
  have hencode : Function.Surjective encode := by
    rintro ⟨_, s, rfl⟩
    exact ⟨s, rfl⟩
  have hS' : Cardinal.mk S' ≤ e.γ :=
    (Cardinal.mk_le_of_surjective hencode).trans hS
  obtain ⟨U, hU, ψ, hψ⟩ :=
    T.exists_bounded_subfunctor_support (toPresheaf.obj X) e.μ e.γ
      e.presheafSiteOperators_lt_μ e.μ_le_γ S' hS'
  let inclusion := originalSubpresheafInclusion U
  have hmap : T.map U.ι ≫ qIso.hom =
      toPresheaf.map (Q.map inclusion) := by
    dsimp [T, Q, qIso, inclusion, presheafLocalReplacement,
      presheafLocalReplacementComparisonIso, originalSubpresheafInclusion,
      toPresheaf]
    rw [← equivalencePresheaf.functor.map_comp, ← Q.map_comp]
    rfl
  let _ : Q.PreservesMonomorphisms := canonicalQ_preservesMonomorphisms κ
  let _ : Mono (Q.map inclusion) := inferInstance
  refine ⟨U, hU, inferInstance, fun s => ψ (encode s), ?_⟩
  funext s
  have hs := congrFun hψ (encode s)
  change
    ((toPresheaf.map (Q.map inclusion)).mapElements).obj (ψ (encode s)) =
      s.val
  have hmapPoint := congrArg
    (fun n => (n.mapElements).obj (ψ (encode s))) hmap
  have hIsoPoint :
      (qIso.hom.mapElements).obj (qElements.symm s.val) = s.val :=
    qElements.apply_symm_apply s.val
  calc
    _ = (qIso.hom.mapElements).obj
        ((T.map U.ι).mapElements.obj (ψ (encode s))) := hmapPoint.symm
    _ = (qIso.hom.mapElements).obj (encode s).val :=
      congrArg (fun z => (qIso.hom.mapElements).obj z) hs
    _ = s.val := hIsoPoint

/-- Every at-most-γ collection of actual raw QX points is supported
simultaneously on one original γ-small subpresheaf. The returned raw points
retain their original bidegrees and map to the supplied points under the same
canonical Q applied to the original inclusion. -/
theorem LocalReplacementCardinalEnvelope.exists_bounded_support
    {κ : Cardinal.{u}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [LocalGenerators.J.{u}.IsCardinalForSmallObjectArgument κ]
    (e : LocalReplacementCardinalEnvelope κ) (X : SimplicialSpace.{u})
    (S : Set (Functor.uncurry.obj
      ((SmallObject.terminalIteration LocalGenerators.J.{u} κ).obj X).diagram).Elements)
    (hS : Cardinal.mk S ≤ e.γ) :
    ∃ U : Subfunctor (toPresheaf.obj X),
      Cardinal.mk U.toFunctor.Elements ≤ e.γ ∧
      Cardinal.mk
          (Functor.uncurry.obj (originalSubpresheafObject U).diagram).Elements ≤
        e.γ ∧
      Mono ((SmallObject.terminalIteration LocalGenerators.J.{u} κ).map
        (originalSubpresheafInclusion U)) ∧
      ∃ φ : S → (Functor.uncurry.obj
          ((SmallObject.terminalIteration LocalGenerators.J.{u} κ).obj
            (originalSubpresheafObject U)).diagram).Elements,
        (((Functor.uncurry.map
            ((SmallObject.terminalIteration LocalGenerators.J.{u} κ).map
              (originalSubpresheafInclusion U)).hom).mapElements).obj ∘ φ) =
          Subtype.val := by
  classical
  let Q := SmallObject.terminalIteration LocalGenerators.J.{u} κ
  let targetPoints := totalPointsEquivToPresheaf (Q.obj X)
  let pushPoint : S → (toPresheaf.obj (Q.obj X)).Elements :=
    fun s => targetPoints s.val
  let S' : Set (toPresheaf.obj (Q.obj X)).Elements := Set.range pushPoint
  let encode : S → S' := fun s => ⟨pushPoint s, ⟨s, rfl⟩⟩
  have hencode : Function.Surjective encode := by
    rintro ⟨_, s, rfl⟩
    exact ⟨s, rfl⟩
  have hS' : Cardinal.mk S' ≤ e.γ :=
    (Cardinal.mk_le_of_surjective hencode).trans hS
  obtain ⟨U, hU, hmono, ψ, hψ⟩ :=
    e.exists_presheaf_support X S' hS'
  change S' →
    (toPresheaf.obj (Q.obj (originalSubpresheafObject U))).Elements at ψ
  let sourcePoints := totalPointsEquivToPresheaf
    (Q.obj (originalSubpresheafObject U))
  let φ : S → (Functor.uncurry.obj
      (Q.obj (originalSubpresheafObject U)).diagram).Elements :=
    fun s => sourcePoints.symm (ψ (encode s))
  refine ⟨U, hU, originalSubpresheaf_mk_elements_le U e.γ hU, hmono, φ, ?_⟩
  funext s
  apply targetPoints.injective
  change
    totalPointsEquivToPresheaf (Q.obj X)
        ((Functor.uncurry.map
          (Q.map (originalSubpresheafInclusion U)).hom).mapElements.obj (φ s)) =
      totalPointsEquivToPresheaf (Q.obj X) s.val
  rw [totalPointsEquivToPresheaf_map]
  change
    ((toPresheaf.map
        (Q.map (originalSubpresheafInclusion U))).mapElements).obj
          (sourcePoints (φ s)) =
      targetPoints s.val
  dsimp only [φ]
  rw [sourcePoints.apply_symm_apply]
  simpa only [Function.comp_apply, targetPoints, pushPoint, encode] using
    congrFun hψ (encode s)

end SimplicialSpace
