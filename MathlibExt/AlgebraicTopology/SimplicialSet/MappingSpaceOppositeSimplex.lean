/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.MappingSpaceOppositeOperators
public import Mathlib.CategoryTheory.HomCongr

/-!
# The exact opposite simplices with fixed mapping-space endpoints

The standard-simplex opposite Iso gives a bijection of whole original
simplices. It exchanges the constant front face and last vertex with
the first vertex and constant back face, at the same supplied endpoints.
No fibrancy hypothesis or quotient of the original vertices is used.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.MappingSpaceOpposite

variable {X Y : SSet.{u}}

/-- The genuine opposite bijection on the whole original standard simplex. -/
abbrev simplexEquiv (X : SSet.{u}) (n : ℕ) :
    ((Δ[n] : SSet.{u}) ⟶ X) ≃ ((Δ[n] : SSet.{u}) ⟶ X.op) :=
  SSet.oppositeSimplexEquiv X n

/-- The compatibility bijection reads the same original neutral opposite simplex. -/
theorem simplexEquiv_apply (X : SSet.{u}) (n : ℕ) (σ : (Δ[n] : SSet.{u}) ⟶ X) :
    simplexEquiv X n σ = (SSet.stdSimplex.opIso ⦋n⦌).inv ≫ opFunctor.map σ :=
  SSet.oppositeSimplexEquiv_apply X n σ

/-- Every original simplex operator is reversed by the whole opposite bijection. -/
theorem simplexEquiv_precomp {n m : ℕ} (φ : ⦋n⦌ ⟶ ⦋m⦌)
    (σ : (Δ[m] : SSet.{u}) ⟶ X) :
    simplexEquiv X n (SSet.stdSimplex.map φ ≫ σ) =
      SSet.stdSimplex.map (SimplexCategory.rev.map φ) ≫ simplexEquiv X m σ := by
  rw [simplexEquiv_apply, simplexEquiv_apply, Functor.map_comp, ← Category.assoc,
    MappingSpaceOppositeOperators.stdSimplex_opIso_naturality, Category.assoc]

/-- The opposite of the supplied original vertex, with no object-class quotient. -/
abbrev vertex (x : (Δ[0] : SSet.{u}) ⟶ X) : (Δ[0] : SSet.{u}) ⟶ X.op :=
  SSet.oppositeVertex x

/-- The opposite bijection preserves the supplied constant simplex exactly. -/
theorem simplexEquiv_constant (n : ℕ) (x : (Δ[0] : SSet.{u}) ⟶ X) :
    simplexEquiv X n (toDeltaZero Δ[n] ≫ x) = toDeltaZero Δ[n] ≫ vertex x := by
  let φ : ⦋n⦌ ⟶ ⦋0⦌ := SimplexCategory.const _ _ 0
  have hφ : SSet.stdSimplex.map φ = toDeltaZero (Δ[n] : SSet.{u}) := toDeltaZero_eq _
  have hr : SimplexCategory.rev.map φ = φ := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext i
    apply Fin.ext
    simp [φ, SimplexCategory.const, SimplexCategory.rev_map_apply]
  have hvertex : simplexEquiv X 0 x = vertex x := SSet.oppositeSimplexEquiv_apply X 0 x
  simpa only [hφ, hr, hvertex] using (simplexEquiv_precomp φ x)

/-- Postcomposition is the same original opposite map, on the whole simplex. -/
theorem simplexEquiv_postcomp (n : ℕ) (σ : (Δ[n] : SSet.{u}) ⟶ X) (f : X ⟶ Y) :
    simplexEquiv Y n (σ ≫ f) = simplexEquiv X n σ ≫ opFunctor.map f := by
  rw [simplexEquiv_apply, simplexEquiv_apply, Functor.map_comp, Category.assoc]

/-- Opposite vertices carry exactly the same supplied original map. -/
theorem vertex_map (x : (Δ[0] : SSet.{u}) ⟶ X) (f : X ⟶ Y) :
    vertex (x ≫ f) = vertex x ≫ opFunctor.map f :=
  SSet.oppositeVertex_comp x f

private theorem rev_lastVertex (n : ℕ) :
    SimplexCategory.rev.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ (Fin.last (n + 1))) =
      SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0 := by
  apply SimplexCategory.Hom.ext_zero_left
  apply Fin.ext
  simp [SimplexCategory.rev_map_apply, SimplexCategory.const]

/-- The actual two fixed right-mapping boundaries are precisely the opposite left-mapping boundaries. -/
theorem boundaries_iff (x y : (Δ[0] : SSet.{u}) ⟶ X) (n : ℕ)
    (σ : (Δ[n + 1] : SSet.{u}) ⟶ X) :
    (frontInclusion n ≫ σ = toDeltaZero Δ[n] ≫ x ∧ rightVertex n ≫ σ = y) ↔
      (vertexZeroStd n ≫ simplexEquiv X (n + 1) σ = vertex y ∧
        SSet.stdSimplex.δ (0 : Fin (n + 2)) ≫ simplexEquiv X (n + 1) σ =
          toDeltaZero Δ[n] ≫ vertex x) := by
  have hfront : simplexEquiv X n (frontInclusion n ≫ σ) =
      SSet.stdSimplex.δ (0 : Fin (n + 2)) ≫ simplexEquiv X (n + 1) σ := by
    rw [frontInclusion_eq, stdSimplex_δ_eq_map, simplexEquiv_precomp,
      SimplexCategory.rev_map_δ, Fin.rev_last, ← stdSimplex_δ_eq_map]
  have hlast : simplexEquiv X 0 (rightVertex n ≫ σ) =
      vertexZeroStd n ≫ simplexEquiv X (n + 1) σ := by
    have hr : AugmentedSimplexCategory.inr' ⦋n⦌ ⦋0⦌ =
        SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ (Fin.last (n + 1)) := by
      apply SimplexCategory.Hom.ext_zero_left
      exact inr'_toOrderHom_zero n
    rw [rightVertex_eq, hr, simplexEquiv_precomp, rev_lastVertex]
  constructor
  · rintro ⟨h₀, h₁⟩
    constructor
    · exact hlast.symm.trans (congrArg (simplexEquiv X 0) h₁)
    · exact hfront.symm.trans ((congrArg (simplexEquiv X n) h₀).trans
        (simplexEquiv_constant n x))
  · rintro ⟨h₁, h₀⟩
    constructor
    · apply (simplexEquiv X n).injective
      exact hfront.trans (h₀.trans (simplexEquiv_constant n x).symm)
    · apply (simplexEquiv X 0).injective
      exact hlast.trans h₁

/-- The degreewise opposite mapping-space comparison is a bijection of whole original simplices with the
  supplied endpoints. -/
def mappingSimplexEquiv (X : SSet.{u}) (x y : (Δ[0] : SSet.{u}) ⟶ X) (n : ℕ) :
    (mappingSpaceRight X x y).obj (op ⦋n⦌) ≃
      (mappingSpaceLeft X.op (vertex y) (vertex x)).obj (op ⦋n⦌) :=
  (mappingSpaceRight.simplexEquivSucc X x y n).trans
    (((simplexEquiv X (n + 1)).subtypeEquiv (boundaries_iff x y n)).trans
      (mappingSpaceLeft.simplexEquivSuccStd X.op (vertex y) (vertex x) n).symm)

/-- Readback of the comparison is the literal opposite of the same original whole mapping simplex. -/
theorem mappingSimplexEquiv_readback (X : SSet.{u}) (x y : (Δ[0] : SSet.{u}) ⟶ X) (n : ℕ)
    (σ : (mappingSpaceRight X x y).obj (op ⦋n⦌)) :
    (mappingSpaceLeft.simplexEquivSuccStd X.op (vertex y) (vertex x) n (mappingSimplexEquiv X x y n σ)).val =
      simplexEquiv X (n + 1) ((mappingSpaceRight.simplexEquivSucc X x y n) σ).val := by
  exact congrArg Subtype.val ((mappingSpaceLeft.simplexEquivSuccStd X.op (vertex y) (vertex x) n).apply_symm_apply _)

end SSet.MappingSpaceOpposite
