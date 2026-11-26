/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectFreeQuiver
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The fixed-object free and Hom adjunction

The source is the category of ordered Hom families.
Its free functor uses the canonical finite-path enrichment, and its right
adjoint reads every complete Hom. The unit is the 
generator; the counit evaluates all paths by the 
Composition. All object labels, maps and both triangle identities are retained.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FixedObjectFree

variable {O : Type u}

/-- The category of `O × O`-indexed simplicial sets. -/
abbrev Families (O : Type u) := O × O → SSet.{u}

/-- Read a Hom family as the canonical supplied generating quiver. -/
def quiver (Q : Families O) : SimplicialQuiver.Data O := ⟨fun x y => Q (x, y)⟩

/-- The free enrichment uses the generators and finite path composition. -/
def freeFunctor : Families O ⥤ FixedObjects O where
  obj Q := FreeQuiver.object (quiver Q)
  map {Q R} f := FreeQuiver.map (Q := quiver Q) (R := quiver R) (fun x y => f (x, y))
  map_id Q := by
    apply FreeQuiver.generators_ext
    intro x y
    erw [FreeQuiver.generator_map]
  map_comp f g := by
    apply FreeQuiver.generators_ext
    intro x y
    erw [FreeQuiver.generator_map]

/-- The right adjoint reads every complete Hom map at both supplied labels. -/
def underlyingFunctor : FixedObjects O ⥤ Families O where
  obj C p := hom C p.1 p.2
  map f p := homMap f p.1 p.2
  map_id C := by
    funext p
    exact homMap_id C p.1 p.2
  map_comp f g := by
    funext p
    exact homMap_comp f g p.1 p.2

/-- The unit retains each generating Hom simplex as its length-one path. -/
def unit : 𝟭 (Families O) ⟶ freeFunctor.{u} (O := O) ⋙ underlyingFunctor.{u} (O := O) where
  app Q p := FreeQuiver.generator (quiver Q) p.1 p.2
  naturality Q R f := by
    funext p
    exact (FreeQuiver.generator_map (Q := quiver Q) (R := quiver R) (fun x y => f (x,
      y)) p.1 p.2).symm

/-- The path evaluation uses the supplied target composition. -/
def evaluate (C : FixedObjects O) :
    (freeFunctor.{u} (O := O)).obj ((underlyingFunctor.{u} (O := O)).obj C) ⟶ C :=
  FreeQuiver.extend (quiver ((underlyingFunctor.{u} (O := O)).obj C)) C (fun x y => 𝟙 (hom C x y))

/-- Reading a generator after path evaluation gives its identical Hom map. -/
theorem generator_evaluate (C : FixedObjects O) (x y : O) :
    FreeQuiver.generator (quiver ((underlyingFunctor.{u} (O := O)).obj C)) x y ≫
      homMap (evaluate C) x y = 𝟙 (hom C x y) :=
  FreeQuiver.generator_extend _ _ _ x y

/-- The counit evaluates all finite paths in the supplied enriched target. -/
theorem evaluate_naturality {C D : FixedObjects O} (f : C ⟶ D) :
    FreeQuiver.map
      (Q := quiver ((underlyingFunctor.{u} (O := O)).obj C))
      (R := quiver ((underlyingFunctor.{u} (O := O)).obj D))
      (fun x y => homMap f x y) ≫ evaluate D = evaluate C ≫ f := by
  apply FreeQuiver.generators_ext
  intro x y
  erw [homMap_comp, homMap_comp]
  calc
    _ = (homMap f x y ≫
        FreeQuiver.generator (quiver ((underlyingFunctor.{u} (O := O)).obj D)) x y) ≫
          homMap (evaluate D) x y := by
      rw [← Category.assoc]
      exact congrArg (fun k => k ≫ homMap (evaluate D) x y)
        (FreeQuiver.generator_map
          (Q := quiver ((underlyingFunctor.{u} (O := O)).obj C))
          (R := quiver ((underlyingFunctor.{u} (O := O)).obj D))
          (fun a b => homMap f a b) x y)
    _ = homMap f x y := by erw [Category.assoc, generator_evaluate, Category.comp_id]
    _ = _ := by erw [← Category.assoc, generator_evaluate, Category.id_comp]

/-- The counit evaluates all finite paths in the supplied enriched target. -/
def counit : underlyingFunctor.{u} (O := O) ⋙ freeFunctor.{u} (O := O) ⟶ 𝟭 (FixedObjects O) where
  app C := evaluate C
  naturality _C _D f := evaluate_naturality f

/-- Reading the generator after the counit returns that identical Hom map. -/
theorem generator_counit (C : FixedObjects O) (x y : O) :
    FreeQuiver.generator (quiver ((underlyingFunctor.{u} (O := O)).obj C)) x y ≫
      homMap ((counit.{u} (O := O)).app C) x y = 𝟙 (hom C x y) :=
  generator_evaluate C x y

/-- The free generator and path evaluation satisfy the left triangle. -/
theorem free_triangle (Q : Families O) :
    (freeFunctor.{u} (O := O)).map ((unit.{u} (O := O)).app Q) ≫
      (counit.{u} (O := O)).app ((freeFunctor.{u} (O := O)).obj Q) =
        𝟙 ((freeFunctor.{u} (O := O)).obj Q) := by
  apply FreeQuiver.generators_ext
  intro x y
  ext n a
  rfl

/-- The Hom unit and counit satisfy the right triangle at every pair. -/
theorem underlying_triangle (C : FixedObjects O) :
    (unit.{u} (O := O)).app ((underlyingFunctor.{u} (O := O)).obj C) ≫
      (underlyingFunctor.{u} (O := O)).map ((counit.{u} (O := O)).app C) =
        𝟙 ((underlyingFunctor.{u} (O := O)).obj C) := by
  funext p
  exact generator_counit C p.1 p.2

/-- The free and Hom functors form an adjunction on the unchanged labels. -/
def adjunction : freeFunctor.{u} (O := O) ⊣ underlyingFunctor.{u} (O := O) where
  unit := unit.{u} (O := O)
  counit := counit.{u} (O := O)
  left_triangle_components := free_triangle
  right_triangle_components := underlying_triangle

/-- The adjunction unit is the identical generator family. -/
theorem adjunction_unit (Q : Families O) (p : O × O) :
    (adjunction.{u} (O := O)).unit.app Q p = FreeQuiver.generator (quiver Q) p.1 p.2 := rfl

/-- The adjunction counit is the same path evaluation. -/
theorem adjunction_counit (C : FixedObjects O) :
    (adjunction.{u} (O := O)).counit.app C = counit.app C := rfl

end CategoryTheory.SimplicialEnrichment.FixedObjects.FixedObjectFree
