/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.ToAugmented
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# Simplicial data in examples

The faces and degeneracies of a simplicial object form simplicial data, and `toSimplicialObject`
returns a simplicial object with the same objects, faces and degeneracies, and the same components
for a simplicial map. On the standard 1-simplex the two faces of the nondegenerate edge are its two
distinct vertices and the degeneracy of a vertex is the constant edge at it. The constant data on
`Bool` gives the constant simplicial set, with identity faces.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Opposite Simplicial

universe v u

namespace CategoryTheory.SimplicialObject.ToSimplicialTests

variable {C : Type u} [Category.{v} C]

/-- The faces and degeneracies of a simplicial object, as simplicial data. -/
def dataOf (X : SimplicialObject C) : Data C where
  obj n := X _⦋n⦌
  δ i := X.δ i
  σ i := X.σ i
  δ_comp_δ h := X.δ_comp_δ h
  δ_comp_σ_of_le h := X.δ_comp_σ_of_le h
  δ_comp_σ_self := X.δ_comp_σ_self
  δ_comp_σ_succ := X.δ_comp_σ_succ
  δ_comp_σ_of_gt h := X.δ_comp_σ_of_gt h
  σ_comp_σ h := X.σ_comp_σ h

/-- A simplicial map, as a morphism of simplicial data. -/
def dataMap {X Y : SimplicialObject C} (g : X ⟶ Y) : Data.Hom (dataOf X) (dataOf Y) where
  app n := g.app (op ⦋n⦌)
  w_δ i := (g.naturality (SimplexCategory.δ i).op).symm
  w_σ i := (g.naturality (SimplexCategory.σ i).op).symm

example (X : SimplicialObject C) (n : ℕ) : (dataOf X).toSimplicialObject _⦋n⦌ = X _⦋n⦌ := rfl

/-- The transported simplicial object has the original faces. -/
theorem toSimplicialObject_dataOf_δ (X : SimplicialObject C) {n : ℕ} (i : Fin (n + 2)) :
    (dataOf X).toSimplicialObject.δ i = X.δ i :=
  (dataOf X).toSimplicialObject_map_δ i

/-- The transported simplicial object has the original degeneracies. -/
theorem toSimplicialObject_dataOf_σ (X : SimplicialObject C) {n : ℕ} (i : Fin (n + 1)) :
    (dataOf X).toSimplicialObject.σ i = X.σ i :=
  (dataOf X).toSimplicialObject_map_σ i

/-- The transported map of a simplicial map has the original components. -/
example {X Y : SimplicialObject C} (g : X ⟶ Y) (n : ℕ) :
    (Data.toSimplicialFunctor.map (dataMap g)).app (op ⦋n⦌) = g.app (op ⦋n⦌) :=
  Data.toSimplicialFunctor_map_app_mk (dataMap g) n

/-! ### The standard 1-simplex -/

/-- The nondegenerate edge of the standard 1-simplex. -/
abbrev edge : Δ[1] _⦋1⦌ := SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)

/-- The face of the edge opposite to vertex `0` is vertex `1`. -/
theorem δ_zero_edge :
    (dataOf Δ[1]).toSimplicialObject.δ 0 edge = SSet.stdSimplex.const 1 1 (op ⦋0⦌) := by
  rw [toSimplicialObject_dataOf_δ]
  refine SSet.stdSimplex.ext _ _ fun j => ?_
  fin_cases j
  rfl

/-- The face of the edge opposite to vertex `1` is vertex `0`. -/
theorem δ_one_edge :
    (dataOf Δ[1]).toSimplicialObject.δ 1 edge = SSet.stdSimplex.const 1 0 (op ⦋0⦌) := by
  rw [toSimplicialObject_dataOf_δ]
  refine SSet.stdSimplex.ext _ _ fun j => ?_
  fin_cases j
  rfl

/-- The two transported faces of the edge are different vertices. -/
theorem δ_zero_edge_ne_δ_one_edge :
    (dataOf Δ[1]).toSimplicialObject.δ 0 edge ≠ (dataOf Δ[1]).toSimplicialObject.δ 1 edge := by
  rw [δ_zero_edge, δ_one_edge]
  intro h
  have h₀ := congrArg (fun x : Δ[1] _⦋0⦌ => x 0) h
  exact absurd h₀ (by decide)

/-- The degeneracy of a vertex is the constant edge at that vertex. -/
theorem σ_const (k : Fin 2) :
    (dataOf Δ[1]).toSimplicialObject.σ (n := 0) 0 (SSet.stdSimplex.const 1 k (op ⦋0⦌)) =
      SSet.stdSimplex.const 1 k (op ⦋1⦌) := by
  rw [toSimplicialObject_dataOf_σ]
  exact SSet.stdSimplex.ext _ _ fun j => rfl

/-- The edge is not degenerate: it is not the degeneracy of either of its faces. -/
example (k : Fin 2) :
    (dataOf Δ[1]).toSimplicialObject.σ (n := 0) 0 (SSet.stdSimplex.const 1 k (op ⦋0⦌)) ≠
      edge := by
  rw [σ_const]
  intro h
  have h₀ := congrArg (fun x : Δ[1] _⦋1⦌ => x 0) h
  have h₁ := congrArg (fun x : Δ[1] _⦋1⦌ => x 1) h
  change k = 0 at h₀
  change k = 1 at h₁
  exact absurd (h₀.symm.trans h₁) (by decide)

/-! ### Constant data -/

example (n : ℕ) : (Data.constData Bool).toSimplicialObject _⦋n⦌ = Bool := rfl

example {n : ℕ} (i : Fin (n + 2)) :
    (Data.constData Bool).toSimplicialObject.δ i = 𝟙 Bool :=
  Data.constData_toSimplicialObject_map_δ Bool i

example (n : ℕ) : (Data.constDataIso Bool).hom.app (op ⦋n⦌) = 𝟙 Bool := rfl

end CategoryTheory.SimplicialObject.ToSimplicialTests
