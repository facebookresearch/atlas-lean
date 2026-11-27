/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomUnitsAndEmpty

/-!
# Literal original coherent Hom of adjacent vertices

If an original interval has only its two endpoint vertices, its actual
path category has one original path and its whole nerve is the tensor
unit. The comparison is given by that endpoint path, not by a component
or a supplied enriched-equivalence outcome.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.AdjacentHom
open SimplicialEnrichment
variable {J : Type u} [LinearOrder J] (a b : J) (hab : a ≤ b)

/-- The actual original path containing precisely the two supplied endpoint vertices. -/
def endpointPath : SimplicialThickening.Path a b where
  I := {a, b}
  left := Or.inl rfl
  right := Or.inr rfl
  left_le k := by rintro (rfl | rfl); exacts [le_rfl, hab]
  le_right k := by rintro (rfl | rfl); exacts [hab, le_rfl]

/-- With no original vertex between the two endpoints, every original interval path is that
same endpoint path. -/
theorem path_eq (hAdj : ∀ k : J, a ≤ k → k ≤ b → k = a ∨ k = b)
    (p : SimplicialThickening.Path a b) : p = endpointPath a b hab := by
  apply SimplicialThickening.Path.ext
  ext k
  constructor
  · intro hk
    exact hAdj k (p.left_le k hk) (p.le_right k hk)
  · rintro (rfl | rfl)
    exacts [p.left, p.right]

/-- The whole simplicial tensor-unit map carrying the same original two-endpoint path in
every degree. -/
def fromUnit : 𝟙_ SSet.{u} ⟶ nerve (SimplicialThickening.Path a b) where
  app q := ↾fun _ => (Functor.const (Fin (q.unop.len + 1))).obj (endpointPath a b hab)
  naturality q r f := by ext t; rfl

/-- The entire original adjacent-interval Hom is the actual tensor unit, with the supplied
original endpoint
  path as forward map. -/
def unitIso (hAdj : ∀ k : J, a ≤ k → k ≤ b → k = a ∨ k = b) :
    𝟙_ SSet.{u} ≅ nerve (SimplicialThickening.Path a b) where
  hom := fromUnit a b hab
  inv := toUnit _
  hom_inv_id := by ext q p; rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro p
    refine Functor.ext (fun i => (path_eq a b hab hAdj (p.obj i)).symm) ?_
    intro i j f
    apply InducedCategory.Hom.ext
    exact Subsingleton.elim _ _

/-- The supplied original endpoint path is the degree-zero forward vertex of the full unit
comparison. -/
theorem unit_vertex : (fromUnit a b hab).app (op ⦋0⦌) PUnit.unit =
    ComposableArrows.mk₀ (endpointPath a b hab) := rfl

/-- Every actual original interval path between zero and one has no other original vertex. -/
theorem finTwo_vertices (k : ULift.{u} (Fin 2)) :
    k = ULift.up (0 : Fin 2) ∨ k = ULift.up (1 : Fin 2) := by
  by_cases h₀ : k.down = 0
  · exact Or.inl (ULift.ext h₀)
  · right
    apply ULift.ext
    apply Fin.ext
    have hN : k.down.val ≠ 0 := fun h => h₀ (Fin.ext h)
    have hK := k.down.isLt
    change k.down.val = 1
    omega

end CategoryTheory.CoherentRealization.AdjacentHom
