/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ParameterAdjunction
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.PushoutMarking
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.SmallLimits
import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations

/-!
# Native marked parameter pushout-products and mapping comparisons

The actual pushout-product uses the original maximally marked parameter
products and their original two inclusions. Its marking is precisely the
images of the original marked side edges. The parametrized adjunction
transposes whole native lifting squares to the genuine marked mapping
pullback comparison. Specializing the parameter to original boundaries
or horns gives the exact native simplicial right-lifting tests.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite HomotopicalAlgebra MonoidalCategory
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.Marked

/-- The native marked pushout square of the original parameter map and marked source map. -/
def parameterPushout {A D : SSet.{u}} {X Y : Marked.{u}} (a : A ⟶ D) (f : X ⟶ Y) :
    maxTensorBifunctor.PushoutObjObj f a := Functor.PushoutObjObj.ofHasPushout _ _ _

/-- The original parameter pushout-product map retains the actual native pushout object. -/
def parameterPushoutProduct {A D : SSet.{u}} {X Y : Marked.{u}} (a : A ⟶ D) (f : X ⟶ Y) :
    (parameterPushout a f).pt ⟶ prod (max D) Y := (parameterPushout a f).ι

/-- The mapping pullback square keeps the original source restriction and target postcomposition. -/
def parameterMappingPullback {X Y E F : Marked.{u}} (f : X ⟶ Y) (p : E ⟶ F) :
    maxMappingBifunctor.PullbackObjObj f p := Functor.PullbackObjObj.ofHasPullback _ _ _

/-- The whole native maximal mapping pullback comparison associated to the original two marked maps. -/
def parameterMappingComparison {X Y E F : Marked.{u}} (f : X ⟶ Y) (p : E ⟶ F) :
    mappingComplex .maximal Y E ⟶ (parameterMappingPullback f p).pt :=
  (parameterMappingPullback f p).π

/-- The first original marked side retains the whole original parameter map. -/
@[reassoc]
theorem parameterPushoutProduct_inl {A D : SSet.{u}} {X Y : Marked.{u}}
    (a : A ⟶ D) (f : X ⟶ Y) :
    (parameterPushout a f).inl ≫ parameterPushoutProduct a f = prodMap (maximal.map a) (𝟙 Y) :=
  (parameterPushout a f).inl_ι

/-- The other original side keeps the original marked source map literally. -/
@[reassoc]
theorem parameterPushoutProduct_inr {A D : SSet.{u}} {X Y : Marked.{u}}
    (a : A ⟶ D) (f : X ⟶ Y) :
    (parameterPushout a f).inr ≫ parameterPushoutProduct a f = prodMap (𝟙 (max D)) f :=
  (parameterPushout a f).inr_ι

/-- The actual selected pushout marking consists exactly of the two original marked source-side images. -/
theorem parameterPushout_mem_marking_iff {A D : SSet.{u}} {X Y : Marked.{u}}
    (a : A ⟶ D) (f : X ⟶ Y) (e : (parameterPushout a f).pt.toSSet _⦋1⦌) :
    e ∈ (parameterPushout a f).pt.marking ↔
      (∃ x : (A ⊗ Y.toSSet) _⦋1⦌, x.2 ∈ Y.marking ∧
        (parameterPushout a f).inl.hom.app (op ⦋1⦌) x = e) ∨
      (∃ y : (D ⊗ X.toSSet) _⦋1⦌, y.2 ∈ X.marking ∧
        (parameterPushout a f).inr.hom.app (op ⦋1⦌) y = e) := by
  rw [mem_marking_of_isPushout_iff (parameterPushout a f).isPushout]
  constructor
  · rintro (⟨x, hx, h⟩ | ⟨y, hy, h⟩)
    · exact Or.inl ⟨x, hx.2, h⟩
    · exact Or.inr ⟨y, hy.2, h⟩
  · rintro (⟨x, hx, h⟩ | ⟨y, hy, h⟩)
    · exact Or.inl ⟨x, ⟨Set.mem_univ _, hx⟩, h⟩
    · exact Or.inr ⟨y, ⟨Set.mem_univ _, hy⟩, h⟩

/-- Whole native pushout-product lifting is exactly original simplicial parameter lifting against the
  mapping comparison. -/
theorem parameterPushoutProduct_hasLiftingProperty_iff {A D : SSet.{u}} {X Y E F : Marked.{u}}
    (a : A ⟶ D) (f : X ⟶ Y) (p : E ⟶ F) :
    HasLiftingProperty (parameterPushoutProduct a f) p ↔
      HasLiftingProperty a (parameterMappingComparison f p) :=
  maxTensorAdjunction₂.hasLiftingProperty_iff (parameterPushout a f) (parameterMappingPullback f p)

/-- Original boundary parameters detect precisely the actual mapping comparison's boundary right class. -/
theorem parameterBoundary_lifting_iff {X Y E F : Marked.{u}} (f : X ⟶ Y) (p : E ⟶ F) :
    (∀ n : ℕ, HasLiftingProperty (parameterPushoutProduct (boundary.{u} n).ι f) p) ↔
      modelCategoryQuillen.I.{u}.rlp (parameterMappingComparison f p) := by
  constructor
  · intro h A D a ha
    obtain ⟨n⟩ := ha
    exact (parameterPushoutProduct_hasLiftingProperty_iff _ f p).mp (h n)
  · intro h n
    exact (parameterPushoutProduct_hasLiftingProperty_iff _ f p).mpr
      (h _ (modelCategoryQuillen.boundary_ι_mem_I n))

/-- Original positive-dimensional horn parameters detect the native Kan fibration mapping comparison. -/
theorem parameterHorn_lifting_iff {X Y E F : Marked.{u}} (f : X ⟶ Y) (p : E ⟶ F) :
    (∀ (n : ℕ) (i : Fin (n + 2)),
      HasLiftingProperty (parameterPushoutProduct (horn.{u} (n + 1) i).ι f) p) ↔
      Fibration (parameterMappingComparison f p) := by
  rw [fibration_iff, modelCategoryQuillen.fibrations_eq]
  constructor
  · intro h A D a ha
    simp only [modelCategoryQuillen.J, MorphismProperty.iSup_iff] at ha
    obtain ⟨n, ⟨i⟩⟩ := ha
    exact (parameterPushoutProduct_hasLiftingProperty_iff _ f p).mp (h n i)
  · intro h n i
    exact (parameterPushoutProduct_hasLiftingProperty_iff _ f p).mpr
      (h _ (by simp only [modelCategoryQuillen.J, MorphismProperty.iSup_iff]; exact ⟨n, ⟨i⟩⟩))

end SSet.Marked
