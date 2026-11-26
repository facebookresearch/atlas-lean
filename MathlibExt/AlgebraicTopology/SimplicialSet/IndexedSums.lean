/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Literal indexed sums of original simplicial sets

The original index and its actual simplex are retained in every degree.
The entire coproduct universal property and map equations are proved on
those same simplices, including arbitrary and empty original index types.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace SSet.IndexedSums

variable {I : Type u} (X : I → SSet.{u})

/-- The actual simplicial set of an original index and its unchanged simplex. -/
def object : SSet.{u} where
  obj q := Σ i : I, (X i).obj q
  map f := ↾fun p => ⟨p.1, (X p.1).map f p.2⟩
  map_id q := by
    apply ConcreteCategory.hom_ext
    intro p
    rcases p with ⟨i, p⟩
    exact congrArg (Sigma.mk (β := fun i : I => (X i).obj q) i)
      (congrArg (fun f => f p) ((X i).map_id q))
  map_comp {q r t} f g := by
    apply ConcreteCategory.hom_ext
    intro p
    rcases p with ⟨i, p⟩
    exact congrArg (Sigma.mk (β := fun i : I => (X i).obj t) i)
      (congrArg (fun f => f p) ((X i).map_comp f g))

/-- Include the same simplex at its individually supplied original index. -/
def inclusion (i : I) : X i ⟶ object X where
  app _q := ↾fun p => ⟨i, p⟩
  naturality _q _r _f := rfl

/-- Evaluate an original indexed simplex by its own supplied cocone leg. -/
def desc {Y : SSet.{u}} (f : ∀ i, X i ⟶ Y) : object X ⟶ Y where
  app q := ↾fun p => (f p.1).app q p.2
  naturality q r g := by
    apply ConcreteCategory.hom_ext
    intro p
    exact congr($((f p.1).naturality g) p.2)

/-- The actual whole sum desc reads back each supplied original leg. -/
theorem inclusion_desc {Y : SSet.{u}} (f : ∀ i, X i ⟶ Y) (i : I) :
    inclusion X i ≫ desc X f = f i := rfl

/-- Original indexed inclusions determine the entire simplicial map. -/
theorem hom_ext {Y : SSet.{u}} (f g : object X ⟶ Y)
    (h : ∀ i, inclusion X i ≫ f = inclusion X i ≫ g) : f = g := by
  ext q p
  exact congr($(h p.1).app q p.2)

/-- The actual original indexed inclusions form a full coproduct cocone. -/
def cofan : Cofan X := Cofan.mk (object X) (inclusion X)

/-- The literal indexed simplicial sum has the entire coproduct universal property. -/
def isColimit : IsColimit (cofan X) :=
  Cofan.IsColimit.mk _ (fun s => desc X s.inj)
    (fun s i => inclusion_desc X s.inj i)
    (fun s m h => hom_ext X m (desc X s.inj) (fun i => (h i).trans (inclusion_desc X s.inj i).symm))

/-- A supplied indexed family acts on every original indexed simplex by its same map. -/
def map {Y : I → SSet.{u}} (f : ∀ i, X i ⟶ Y i) : object X ⟶ object Y :=
  desc X (fun i => f i ≫ inclusion Y i)

/-- Indexed sum maps commute with the same original supplied inclusions. -/
theorem inclusion_map {Y : I → SSet.{u}} (f : ∀ i, X i ⟶ Y i) (i : I) :
    inclusion X i ≫ map X f = f i ≫ inclusion Y i := rfl

/-- Any genuinely coproduct-stable scalar property applies to this entire original sum map. -/
theorem map_property (P : MorphismProperty SSet.{u}) [P.IsStableUnderCoproductsOfShape I]
    {Y : I → SSet.{u}} (f : ∀ i, X i ⟶ Y i) (hf : ∀ i, P (f i)) : P (map X f) := by
  exact (MorphismProperty.IsStableUnderColimitsOfShape.condition (W := P)
    (Discrete.functor X) (Discrete.functor Y) (cofan X) (cofan Y)
    (isColimit X) (isColimit Y) (Discrete.natTrans (fun i => f i.as)) (fun i => hf i.as)
    (map X f) (fun i => inclusion_map X f i.as))

end SSet.IndexedSums
