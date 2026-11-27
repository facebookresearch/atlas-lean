/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SSetULiftPiNaturality
public import MathlibExt.AlgebraicTopology.SimplicialSet.SSetULiftGroupoidNaturality
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexW

/-!
# Genuine original Kan weak class under universe lift

The actual full original fundamental-groupoid lift and homotopy-group
lift equivalences retain every source map and original basepoint. The
canonical original Kan weak class is preserved and reflected by the
same full coefficient universe lift, with no desired weak-map input.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.KanComplex

/-- The fundamental-groupoid weak property is preserved and reflected by coefficient universe
lift. -/
theorem ulift_mapFundamentalGroupoid_isEquivalence_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    (SSet.mapFundamentalGroupoid (SSet.uliftFunctor.{v,u}.map f)).IsEquivalence ↔
      (SSet.mapFundamentalGroupoid f).IsEquivalence := by
  let A := SSet.fundamentalGroupoidULift.{u,v} X
  let B := SSet.fundamentalGroupoidULift.{u,v} Y
  let _ : A.IsEquivalence :=
    (SSet.fundamentalGroupoidULiftEquivalence.{u,v} X).isEquivalence_functor
  let _ : B.IsEquivalence :=
    (SSet.fundamentalGroupoidULiftEquivalence.{u,v} Y).isEquivalence_functor
  have he := SSet.fundamentalGroupoidULift_naturality.{u,v} f
  constructor
  · intro h
    let _ := h
    let _ : (A ⋙ SSet.mapFundamentalGroupoid (SSet.uliftFunctor.{v,u}.map f)).IsEquivalence :=
      inferInstance
    let _ : (SSet.mapFundamentalGroupoid f ⋙ B).IsEquivalence := he ▸ inferInstance
    exact Functor.isEquivalence_of_comp_right (SSet.mapFundamentalGroupoid f) B
  · intro h
    let _ := h
    let _ : (SSet.mapFundamentalGroupoid f ⋙ B).IsEquivalence := inferInstance
    let _ : (A ⋙ SSet.mapFundamentalGroupoid (SSet.uliftFunctor.{v,u}.map f)).IsEquivalence :=
      he.symm ▸ inferInstance
    exact Functor.isEquivalence_of_comp_left A
      (SSet.mapFundamentalGroupoid (SSet.uliftFunctor.{v,u}.map f))

/-- The based homotopy map is bijective exactly when its coefficient lift is, in every degree. -/
theorem ulift_piMap_bijective_iff {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (f : X ⟶ Y) (n : ℕ) (x : X _⦋0⦌) :
    Function.Bijective (π.map (SSet.uliftFunctor.{v,u}.map f) rfl n (x := ULift.up x)) ↔
      Function.Bijective (π.map f rfl n (x := x)) := by
  let A := uliftPiEquiv.{u,v} X n x
  let B := uliftPiEquiv.{u,v} Y n (f.app _ x)
  have he : B ∘ π.map f rfl n = π.map (SSet.uliftFunctor.{v,u}.map f) rfl n ∘ A :=
    funext (uliftPiEquiv_naturality f n x)
  constructor
  · intro h
    have hcomp : Function.Bijective (B ∘ π.map f rfl n) := he.symm ▸ h.comp A.bijective
    constructor
    · intro p q hpq
      exact hcomp.1 (congrArg B hpq)
    · intro q
      obtain ⟨p, hp⟩ := hcomp.2 (B q)
      exact ⟨p, B.injective hp⟩
  · intro h
    have hcomp : Function.Bijective (π.map (SSet.uliftFunctor.{v,u}.map f) rfl n ∘ A) :=
      he ▸ B.bijective.comp h
    constructor
    · intro p q hpq
      obtain ⟨p', rfl⟩ := A.surjective p
      obtain ⟨q', rfl⟩ := A.surjective q
      exact congrArg A (hcomp.1 hpq)
    · intro q
      obtain ⟨p, hp⟩ := hcomp.2 q
      exact ⟨A p, hp⟩

/-- The coefficient universe lift preserves and reflects the original Kan weak equivalences. -/
theorem W_ulift_map_iff {X Y : SSet.{u}} [KanComplex X] [KanComplex Y] (f : X ⟶ Y) :
    W (SSet.uliftFunctor.{v,u}.map f) ↔ W f := by
  let _ := SSet.kanComplex_ulift.{u,v} X
  let _ := SSet.kanComplex_ulift.{u,v} Y
  constructor
  · intro h
    refine ⟨inferInstance, inferInstance,
      (ulift_mapFundamentalGroupoid_isEquivalence_iff f).mp h.2.2.1, ?_⟩
    intro n x
    exact (ulift_piMap_bijective_iff f n x).mp (h.2.2.2 n (ULift.up x))
  · intro h
    refine ⟨inferInstance, inferInstance,
      (ulift_mapFundamentalGroupoid_isEquivalence_iff f).mpr h.2.2.1, ?_⟩
    intro n x
    cases x with
    | up x => exact (ulift_piMap_bijective_iff f n x).mpr (h.2.2.2 n x)

end SSet.KanComplex
