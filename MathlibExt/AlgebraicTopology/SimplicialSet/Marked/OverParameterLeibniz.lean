/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverParameterBifunctors
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ParameterUnderlyingPushout
import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
import Mathlib.CategoryTheory.Limits.Over

/-!
# Actual parameter pushout-products over the original marked base

The original slice products and their supplied base maps form the native
pushout-product. Its full underlying marked pushout has precisely the
original marked side images. The actual relative mapping pullback
comparison transposes whole lifting squares; original parameter boundary
and horn tests give the genuine simplicial right classes. No base Kan
hypothesis or marked-model structure is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite MonoidalCategory HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.Marked

/-- The actual original parameter/source pushout square in the supplied marked slice. -/
def overParameterPushout {Z : Marked.{u}} {A D : SSet.{u}} {X Y : Over Z}
    (a : A ⟶ D) (f : X ⟶ Y) : (overParameterBifunctor Z).PushoutObjObj f a :=
  Functor.PushoutObjObj.ofHasPushout _ _ _

/-- The native original parameter pushout-product retains the supplied whole base map. -/
def overParameterPushoutProduct {Z : Marked.{u}} {A D : SSet.{u}} {X Y : Over Z}
    (a : A ⟶ D) (f : X ⟶ Y) : (overParameterPushout a f).pt ⟶ overParameter Z Y D :=
  (overParameterPushout a f).ι

/-- The actual original relative mapping pullback square keeps both supplied marked slice maps. -/
def overParameterMappingPullback {Z : Marked.{u}} {X Y E F : Over Z}
    (f : X ⟶ Y) (p : E ⟶ F) : (overParameterMappingBifunctor Z).PullbackObjObj f p :=
  Functor.PullbackObjObj.ofHasPullback _ _ _

/-- The full native fixed-base mapping comparison uses the original restriction and postcomposition maps. -/
def overParameterMappingComparison {Z : Marked.{u}} {X Y E F : Over Z}
    (f : X ⟶ Y) (p : E ⟶ F) :
    relativeMappingComplex .maximal Y.hom E.hom ⟶ (overParameterMappingPullback f p).pt :=
  (overParameterMappingPullback f p).π

/-- Forgetting the slice retains the actual original marked pushout square and parameter map. -/
def overParameterUnderlyingPushout {Z : Marked.{u}} {A D : SSet.{u}} {X Y : Over Z}
    (a : A ⟶ D) (f : X ⟶ Y) : maxTensorBifunctor.PushoutObjObj f.left a := by
  let s := overParameterPushout a f
  exact
    { pt := s.pt.left
      inl := s.inl.left
      inr := s.inr.left
      isPushout := (Over.forget Z).map_isPushout s.isPushout
      ι := s.ι.left
      inl_ι := congrArg Over.Hom.left s.inl_ι
      inr_ι := congrArg Over.Hom.left s.inr_ι }

/-- The selected slice pushout marking consists exactly of original marked side-edge images. -/
theorem overParameterPushout_mem_marking_iff {Z : Marked.{u}} {A D : SSet.{u}} {X Y : Over Z}
    (a : A ⟶ D) (f : X ⟶ Y) (e : (overParameterPushout a f).pt.left.toSSet _⦋1⦌) :
    e ∈ (overParameterPushout a f).pt.left.marking ↔
      (∃ x : (A ⊗ Y.left.toSSet) _⦋1⦌, x.2 ∈ Y.left.marking ∧
        (overParameterPushout a f).inl.left.hom.app (op ⦋1⦌) x = e) ∨
      (∃ y : (D ⊗ X.left.toSSet) _⦋1⦌, y.2 ∈ X.left.marking ∧
        (overParameterPushout a f).inr.left.hom.app (op ⦋1⦌) y = e) := by
  let s := overParameterUnderlyingPushout a f
  let e' : s.pt.toSSet _⦋1⦌ := e
  refine (mem_marking_of_isPushout_iff s.isPushout e').trans ?_
  constructor
  · rintro (⟨x, hx, h⟩ | ⟨y, hy, h⟩)
    · exact Or.inl ⟨x, hx.2, h⟩
    · exact Or.inr ⟨y, hy.2, h⟩
  · rintro (⟨x, hx, h⟩ | ⟨y, hy, h⟩)
    · exact Or.inl ⟨x, ⟨Set.mem_univ _, hx⟩, h⟩
    · exact Or.inr ⟨y, ⟨Set.mem_univ _, hy⟩, h⟩

/-- Whole native slice pushout-product lifting is exactly the original parameter lifting against the
  relative mapping comparison. -/
theorem overParameterPushoutProduct_hasLiftingProperty_iff {Z : Marked.{u}}
    {A D : SSet.{u}} {X Y E F : Over Z} (a : A ⟶ D) (f : X ⟶ Y) (p : E ⟶ F) :
    HasLiftingProperty (overParameterPushoutProduct a f) p ↔
      HasLiftingProperty a (overParameterMappingComparison f p) :=
  (overParameterAdjunction₂ Z).hasLiftingProperty_iff
    (overParameterPushout a f) (overParameterMappingPullback f p)

/-- Every original boundary parameter gives the exact native fixed-base mapping comparison boundary right class. -/
theorem overParameterBoundary_lifting_iff {Z : Marked.{u}} {X Y E F : Over Z}
    (f : X ⟶ Y) (p : E ⟶ F) :
    (∀ n : ℕ, HasLiftingProperty (overParameterPushoutProduct (boundary.{u} n).ι f) p) ↔
      modelCategoryQuillen.I.{u}.rlp (overParameterMappingComparison f p) := by
  constructor
  · intro h A D a ha
    obtain ⟨n⟩ := ha
    exact (overParameterPushoutProduct_hasLiftingProperty_iff _ f p).mp (h n)
  · intro h n
    exact (overParameterPushoutProduct_hasLiftingProperty_iff _ f p).mpr
      (h _ (modelCategoryQuillen.boundary_ι_mem_I n))

/-- Positive-dimensional original horn parameters give the actual native relative mapping comparison Kan
  fibration class. -/
theorem overParameterHorn_lifting_iff {Z : Marked.{u}} {X Y E F : Over Z}
    (f : X ⟶ Y) (p : E ⟶ F) :
    (∀ (n : ℕ) (i : Fin (n + 2)),
      HasLiftingProperty (overParameterPushoutProduct (horn.{u} (n + 1) i).ι f) p) ↔
      Fibration (overParameterMappingComparison f p) := by
  rw [fibration_iff, modelCategoryQuillen.fibrations_eq]
  constructor
  · intro h A D a ha
    simp only [modelCategoryQuillen.J, MorphismProperty.iSup_iff] at ha
    obtain ⟨n, ⟨i⟩⟩ := ha
    exact (overParameterPushoutProduct_hasLiftingProperty_iff _ f p).mp (h n i)
  · intro h n i
    exact (overParameterPushoutProduct_hasLiftingProperty_iff _ f p).mpr
      (h _ (by simp only [modelCategoryQuillen.J, MorphismProperty.iSup_iff]; exact ⟨n, ⟨i⟩⟩))

end SSet.Marked
