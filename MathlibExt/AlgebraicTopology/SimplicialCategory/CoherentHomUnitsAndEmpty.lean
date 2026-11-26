/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentVertices

/-!
# Literal identity and empty coherent Hom objects

A same-endpoint interval path is the singleton path. Its 
Hom nerve is the tensor unit. A reverse interval has no 
path simplex in any scalar degree. These facts keep the objects
and do not use a Kan or enriched-model assumption.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HomUnitsAndEmpty
open SimplicialEnrichment
variable {J : Type u} [LinearOrder J]

/-- A same-endpoint interval path is determined by that individual endpoint. -/
theorem diagonalPath_unique (a : J) (p q : SimplicialThickening.Path a a) : p = q := by
  apply SimplicialThickening.Path.ext
  ext x
  constructor
  · intro hx
    have h : x = a := le_antisymm (p.le_right x hx) (p.left_le x hx)
    simpa only [h] using q.left
  · intro hx
    have h : x = a := le_antisymm (q.le_right x hx) (q.left_le x hx)
    simpa only [h] using p.left

private instance (a : J) (p q : SimplicialThickening.Path a a) : Subsingleton (p ⟶ q) where
  allEq f g := by
    apply InducedCategory.Hom.ext
    exact Subsingleton.elim _ _

/-- Every same-endpoint scalar Hom simplex is the same singleton path chain. -/
theorem diagonalSimplex_unique (a : J) (q : SimplexCategoryᵒᵖ)
    (p r : (nerve (SimplicialThickening.Path a a)).obj q) : p = r :=
  CategoryTheory.Functor.ext (fun _ => diagonalPath_unique a _ _) (fun _ _ _ =>
    Subsingleton.elim _ _)

/-- The enriched identity gives the same-endpoint Hom isomorphism from
the tensor unit. -/
def unitIso (a : J) : 𝟙_ SSet.{u} ≅ nerve (SimplicialThickening.Path a a) where
  hom := eId SSet.{u} (SimplicialThickening.mk a)
  inv := toUnit _
  hom_inv_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro p
    rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro p
    exact diagonalSimplex_unique a q _ _

/-- The enriched identity map is genuinely an isomorphism on its same-endpoint
Hom. -/
theorem unit_isIso (a : J) : IsIso (eId SSet.{u} (SimplicialThickening.mk a)) :=
  (unitIso a).isIso_hom

/-- A scalar intervalHom simplex supplies the endpoint order. -/
theorem source_order {a b : J} {q : SimplexCategoryᵒᵖ}
    (p : (nerve (SimplicialThickening.Path a b)).obj q) : a ≤ b := (p.obj 0).le

/-- The reverse-interval Hom maps uniquely, since it has no scalar
simplices. -/
def emptyMap {a b : J} (h : ¬a ≤ b) (Y : SSet.{u}) : nerve (SimplicialThickening.Path a b) ⟶ Y where
  app q := ↾fun p => False.elim (h (source_order p))
  naturality q r f := by
    apply ConcreteCategory.hom_ext
    intro p
    exact False.elim (h (source_order p))

/-- Two maps from a genuinely reverse interval Hom are equal in every scalar
degree. -/
theorem empty_hom_ext {a b : J} (h : ¬a ≤ b) {Y : SSet.{u}}
    (f g : nerve (SimplicialThickening.Path a b) ⟶ Y) : f = g := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro p
  exact False.elim (h (source_order p))

end CategoryTheory.CoherentRealization.HomUnitsAndEmpty
