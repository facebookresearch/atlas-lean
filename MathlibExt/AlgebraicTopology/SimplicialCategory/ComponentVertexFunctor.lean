/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.ComponentCategoryVertexLaws
import Mathlib.CategoryTheory.Enriched.Ordinary.Basic

/-!
# The actual original vertex-to-component functor

For every original simplicial enriched ordinary category, its actual
unit-Hom vertex maps to the SAME component Hom class. The original
Cartesian component comparison reads vertex pairs literally, so this
assignment preserves the full original identity and composition. All
object, ordinary Hom and coefficient universes remain independent.
-/

noncomputable section
universe u v w
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SSet

/-- The original component functor's full monoidal multiplication reads the SAME two original vertices. -/
theorem piZeroMonoidal_μ_mk (X Y : SSet.{u}) (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    (Functor.LaxMonoidal.μ SSet.π₀Functor X Y) (π₀.mk x, π₀.mk y) =
      π₀.mk (componentTensorSimplex _ x y) := by
  apply (piZeroTensorEquiv X Y).injective
  apply Prod.ext
  · exact congrArg (fun f : (π₀ X × π₀ Y) ⟶ π₀ X => f (π₀.mk x, π₀.mk y))
      (Functor.Monoidal.μ_fst SSet.π₀Functor X Y)
  · exact congrArg (fun f : (π₀ X × π₀ Y) ⟶ π₀ Y => f (π₀.mk x, π₀.mk y))
      (Functor.Monoidal.μ_snd SSet.π₀Functor X Y)

/-- The original component unit retains the SAME unique original unit-Hom vertex. -/
theorem piZeroMonoidal_ε_unit :
    (Functor.LaxMonoidal.ε SSet.π₀Functor.{u}) PUnit.unit =
      π₀.mk (PUnit.unit : (𝟙_ SSet.{u}) _⦋0⦌) := by
  obtain ⟨v, hv⟩ := ((Functor.LaxMonoidal.ε SSet.π₀Functor.{u}) PUnit.unit).mk_surjective
  exact hv.symm.trans (congrArg π₀.mk
    (@Subsingleton.elim PUnit.{u + 1} inferInstance v PUnit.unit))

end SSet

namespace CategoryTheory.SimplicialEnrichment.ComponentCategory

variable (C : Type v) [Category.{w} C] [EnrichedOrdinaryCategory SSet.{u} C]

/-- The SAME original unit-Hom vertex arrow, regarded in the original component category. -/
def vertexFunctor : C ⥤ objects.{u} C where
  obj x := objectOf.{u} C x
  map f := SSet.π₀.mk (SSet.unitHomEquiv _ (eHomEquiv SSet.{u} f))
  map_id x := by
    change SSet.π₀.mk (SSet.unitHomEquiv _ (eHomEquiv SSet.{u} (𝟙 x))) =
      SSet.mapπ₀ (eId SSet.{u} x) ((Functor.LaxMonoidal.ε SSet.π₀Functor) PUnit.unit)
    rw [eHomEquiv_id, SSet.piZeroMonoidal_ε_unit, SSet.mapπ₀_mk]
    rfl
  map_comp {x y z} f g := by
    change SSet.π₀.mk (SSet.unitHomEquiv _ (eHomEquiv SSet.{u} (f ≫ g))) =
      SSet.mapπ₀ (eComp SSet.{u} x y z)
        ((Functor.LaxMonoidal.μ SSet.π₀Functor _ _)
          (SSet.π₀.mk (SSet.unitHomEquiv _ (eHomEquiv SSet.{u} f)),
            SSet.π₀.mk (SSet.unitHomEquiv _ (eHomEquiv SSet.{u} g))))
    rw [eHomEquiv_comp, SSet.piZeroMonoidal_μ_mk, SSet.mapπ₀_mk]
    rfl

/-- The whole actual component functor retains each SAME individual original object. -/
theorem vertexFunctor_obj (x : C) : (vertexFunctor C).obj x = objectOf.{u} C x := rfl

/-- The original component Hom readback retains the actual unit-Hom vertex of the SAME ordinary map. -/
theorem vertexFunctor_map {x y : C} (f : x ⟶ y) :
    (vertexFunctor C).map f = arrowOf C (SSet.unitHomEquiv _ (eHomEquiv SSet.{u} f)) := rfl

end CategoryTheory.SimplicialEnrichment.ComponentCategory
