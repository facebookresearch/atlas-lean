/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryMatching
public import Mathlib.CategoryTheory.LiftingProperties.Basic

import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Boundary lifting and relative matching

The relative matching map is surjective exactly when every square against
`∂Δ[n] ⟶ Δ[n]` lifts. The two pullback projections record the prescribed
simplex in the target and its prescribed boundary in the source.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SSet.BoundaryMatching
open SSet.ProperFaceBoundary

/-- The matching comparison identifies the matching-object map with postcomposition. -/
theorem matching_map_readback {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ)
    (b : SimplicialObject.matchingObject X n) :
    (matchingBoundaryIso Y n).hom ((SimplicialObject.matchingObjectFunctor n).map f b) =
      (matchingBoundaryIso X n).hom b ≫ f := by
  apply (properFaceBoundaryIsColimit.{u} n).hom_ext
  intro a
  change properFaceBoundaryInclusion.{u} a.unop ≫
      (matchingBoundaryIso Y n).hom ((SimplicialObject.matchingObjectFunctor n).map f b) =
    properFaceBoundaryInclusion.{u} a.unop ≫ ((matchingBoundaryIso X n).hom b ≫ f)
  rw [matchingBoundaryIso_hom_face, ← Category.assoc, matchingBoundaryIso_hom_face]
  rw [yonedaEquiv_symm_comp]
  exact congrArg yonedaEquiv.symm
    (ConcreteCategory.congr_hom (SimplicialObject.matchingObjectFunctor_map_π n f a.unop) b)

/-- A lift against the boundary inclusion is equivalent to a preimage for each
point of the relative matching pullback. -/
theorem relativeMatching_surjective_iff_hasLiftingProperty_boundary {X Y : SSet.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    Function.Surjective (SimplicialObject.relativeMatchingMap f n) ↔
      HasLiftingProperty (boundary.{u} n).ι f := by
  let matchMap := (SimplicialObject.matchingObjectFunctor n).map f
  let targetMap := SimplicialObject.matchingMap Y n
  have hp := IsPullback.of_hasPullback targetMap matchMap
  have hfst (x : X.obj (op ⦋n⦌)) :
      pullback.fst targetMap matchMap (SimplicialObject.relativeMatchingMap f n x) =
        f.app (op ⦋n⦌) x :=
    ConcreteCategory.congr_hom (SimplicialObject.relativeMatchingMap_fst f n) x
  have hsnd (x : X.obj (op ⦋n⦌)) :
      pullback.snd targetMap matchMap (SimplicialObject.relativeMatchingMap f n x) =
        SimplicialObject.matchingMap X n x :=
    ConcreteCategory.congr_hom (SimplicialObject.relativeMatchingMap_snd f n) x
  let e := (matchingBoundaryIso X n).toEquiv
  constructor
  · intro hf
    refine ⟨fun {a} {b} sq => ?_⟩
    have hw : targetMap (yonedaEquiv b) = matchMap (e.symm a) := by
      apply (matchingBoundaryIso Y n).toEquiv.injective
      change (matchingBoundaryIso Y n).hom (SimplicialObject.matchingMap Y n (yonedaEquiv b)) =
        (matchingBoundaryIso Y n).hom (matchMap (e.symm a))
      rw [matchingMap_readback, yonedaEquiv.symm_apply_apply, matching_map_readback]
      exact sq.w.symm.trans (congrArg (fun z => z ≫ f) (e.apply_symm_apply a)).symm
    obtain ⟨p, hp₁, hp₂⟩ := Types.exists_of_isPullback hp (yonedaEquiv b) (e.symm a) hw
    obtain ⟨x, rfl⟩ := hf p
    apply CommSq.HasLift.mk'
    refine { l := yonedaEquiv.symm x, fac_left := ?_, fac_right := ?_ }
    · exact (matchingMap_readback X n x).symm.trans
        ((congrArg e ((hsnd x).symm.trans hp₂)).trans (e.apply_symm_apply a))
    · exact (yonedaEquiv_symm_comp x f).trans
        ((congrArg yonedaEquiv.symm ((hfst x).symm.trans hp₁)).trans
          (yonedaEquiv.symm_apply_apply b))
  · intro hf p
    let a := e (pullback.snd targetMap matchMap p)
    let b := yonedaEquiv.symm (pullback.fst targetMap matchMap p)
    have hCondition := ConcreteCategory.congr_hom
      (pullback.condition (f := targetMap) (g := matchMap)) p
    have sq : CommSq a (boundary n).ι f b := ⟨by
      have h := congrArg (fun t => (matchingBoundaryIso Y n).hom t) hCondition
      change (matchingBoundaryIso Y n).hom
          (SimplicialObject.matchingMap Y n (pullback.fst targetMap matchMap p)) =
        (matchingBoundaryIso Y n).hom (matchMap (pullback.snd targetMap matchMap p)) at h
      rw [matchingMap_readback, matching_map_readback] at h
      exact h.symm⟩
    let : HasLiftingProperty (boundary n).ι f := hf
    refine ⟨yonedaEquiv sq.lift, Types.ext_of_isPullback hp ?_ ?_⟩
    · rw [hfst, ← yonedaEquiv_comp, sq.fac_right]
      exact yonedaEquiv.apply_symm_apply _
    · rw [hsnd]
      apply e.injective
      change (matchingBoundaryIso X n).hom
          (SimplicialObject.matchingMap X n (yonedaEquiv sq.lift)) = a
      rw [matchingMap_readback, yonedaEquiv.symm_apply_apply, sq.fac_left]

/-- Surjectivity of the relative matching map supplies a lift of each boundary square. -/
theorem hasLiftingProperty_boundary_of_relativeMatching_surjective {X Y : SSet.{u}}
    (f : X ⟶ Y) (n : ℕ) (hf : Function.Surjective (SimplicialObject.relativeMatchingMap f n)) :
    HasLiftingProperty (boundary.{u} n).ι f :=
  (relativeMatching_surjective_iff_hasLiftingProperty_boundary f n).mp hf

end SSet.BoundaryMatching
