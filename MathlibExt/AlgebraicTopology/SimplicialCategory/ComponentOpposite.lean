/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.ComponentVertexFunctor
import Mathlib.CategoryTheory.Enriched.Opposite

/-!
# Original component classes commute with enriched opposites

The actual opposite enrichment reverses the SAME whole original Homs
and uses their original Cartesian braiding. Its component composition
therefore reverses the SAME original component arrows. This gives an
actual ordinary opposite-component functor, retaining individual
objects and full original Hom-component maps in every universe.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.ComponentCategory

variable (C : Type v) [EnrichedCategory SSet.{u} C]

/-- The SAME original component multiplication is reversed by the actual enriched opposite braiding. -/
theorem opposite_comp (x y z : C) (a : SSet.π₀ (x ⟶[SSet.{u}] y)) (b : SSet.π₀ (y ⟶[SSet.{u}] z)) :
    SSet.mapπ₀ (eComp SSet.{u} (op z) (op y) (op x))
      ((Functor.LaxMonoidal.μ SSet.π₀Functor _ _) (b, a)) =
    SSet.mapπ₀ (eComp SSet.{u} x y z)
      ((Functor.LaxMonoidal.μ SSet.π₀Functor _ _) (a, b)) := by
  induction a using SSet.π₀.rec with
  | mk a =>
    induction b using SSet.π₀.rec with
    | mk b =>
      simp only [SSet.piZeroMonoidal_μ_mk, SSet.mapπ₀_mk]
      rfl

/-- The actual opposite-component functor retains the SAME original objects and reversed original component Hom maps. -/
def oppositeFunctor : (objects.{u} C)ᵒᵖ ⥤ objects.{u} Cᵒᵖ where
  obj x := objectOf.{u} Cᵒᵖ (op (originalObject C x.unop))
  map f := f.unop
  map_id _x := rfl
  map_comp {x y z} f g := by
    change SSet.mapπ₀ (eComp SSet.{u} (originalObject C z.unop) (originalObject C y.unop) (originalObject C x.unop))
      ((Functor.LaxMonoidal.μ SSet.π₀Functor _ _) (g.unop, f.unop)) =
      SSet.mapπ₀ (eComp SSet.{u} (op (originalObject C x.unop))
        (op (originalObject C y.unop)) (op (originalObject C z.unop)))
        ((Functor.LaxMonoidal.μ SSet.π₀Functor _ _) (f.unop, g.unop))
    exact (opposite_comp C _ _ _ g.unop f.unop).symm

/-- The whole opposite-component object map retains the SAME individual original object. -/
theorem oppositeFunctor_obj (x : C) :
    (oppositeFunctor C).obj (op (objectOf.{u} C x)) = objectOf.{u} Cᵒᵖ (op x) := rfl

end CategoryTheory.SimplicialEnrichment.ComponentCategory
