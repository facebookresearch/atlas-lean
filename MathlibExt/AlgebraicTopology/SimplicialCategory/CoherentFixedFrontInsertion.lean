/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentConstantInsertion
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontVertices

/-!
# The actual distinguished simplex of the fixed-front realization

The projected original identity successor simplex supplies the genuine
enriched insertion. Its entire original front is constant at the
structural source. Every actual resolving simplex is an original operator
of this distinguished simplex, including the structural collapsed point.
All statements concern the constructed quotient, not a supplied chart.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.FixedFrontInsertion
open SimplicialEnrichment FixedFrontCollapse FixedFrontVertices

/-- The actual projected original identity successor simplex. -/
def simplex (n : ℕ) : (FixedFrontCollapse.object.{u} n) _⦋n + 1⦌ :=
  (projection n).app (op ⦋n + 1⦌) (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n + 1⦌))

/-- Its genuine whole enriched insertion into the actual realization. -/
def functor (n : ℕ) : coherentSimplex.{u} ⦋n + 1⦌ ⟶ realization (FixedFrontCollapse.object.{u} n) :=
  simplexInto (FixedFrontCollapse.object n) (simplex n)

/-- The inserted distinguished simplex reads each original resolving vertex through the
actual quotient projection. -/
theorem vertex_eq (n : ℕ) (i : Fin (n + 2)) :
    (functor.{u} n).obj (SimplicialThickening.mk (ULift.up i)) =
      (projection n).app (op ⦋0⦌) (SSet.stdSimplex.objEquiv.symm (SimplexCategory.const
        ⦋0⦌ ⦋n + 1⦌ i)) := by
  change _root_.Quotient.mk _ ((Δ[n + 1] : SSet.{u}).map
    (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ i).op (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n + 1⦌))) = _
  rw [SSet.stdSimplex.map_objEquiv_symm, Category.comp_id]
  rfl

/-- Each individual original front label has exactly the structural source image. -/
theorem front_obj (n : ℕ) (i : Fin (n + 1)) :
    (functor.{u} n).obj (SimplicialThickening.mk (ULift.up i.castSucc)) = source n :=
  (vertex_eq n i.castSucc).trans (front_vertex i.castSucc (ne_of_lt (Fin.castSucc_lt_last i)))

/-- The actual original last label has exactly the structural target image. -/
theorem last_obj (n : ℕ) :
    (functor.{u} n).obj (SimplicialThickening.mk (ULift.up (Fin.last (n + 1)))) = target n :=
  vertex_eq n (Fin.last (n + 1))

/-- The entire front of the actual projected identity simplex is the original constant
structural source simplex. -/
theorem front_simplex (n : ℕ) :
    (FixedFrontCollapse.object.{u} n).map (SimplexCategory.δ (Fin.last (n + 1))).op (simplex n) =
      (FixedFrontCollapse.object n).map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op (source n) := by
  apply _root_.Quotient.sound
  right
  constructor
  · intro j
    change (Fin.last (n + 1)).succAbove j ≠ Fin.last (n + 1)
    exact Fin.succAbove_ne _ _
  · intro j
    exact ne_of_lt Fin.last_pos

/-- The whole original coherent front insertion, including all its original Hom maps, is
actually constant
  at the structural source. -/
theorem front_functor (n : ℕ) :
    coherentSimplexMap (SimplexCategory.δ (Fin.last (n + 1))) ≫ functor.{u} n =
      constantSimplex (realization (FixedFrontCollapse.object n)) ⦋n⦌ (source n) :=
  (simplexInto_operator (FixedFrontCollapse.object n)
    (SimplexCategory.δ (Fin.last (n + 1))) (simplex n)).trans
    ((congrArg (simplexInto (FixedFrontCollapse.object n)) (front_simplex n)).trans
      (ConstantInsertion.constant (FixedFrontCollapse.object n) ⦋n⦌ (source n)))

/-- Each projected original resolving simplex is the corresponding genuine operator of the
distinguished
  successor simplex. -/
theorem projected_operator (n : ℕ) {m : SimplexCategory}
    (a : (Δ[n + 1] : SSet.{u}).obj (op m)) :
    (FixedFrontCollapse.object n).map a.down.op (simplex n) = (projection n).app (op m) a := by
  change _root_.Quotient.mk _ ((Δ[n + 1] : SSet.{u}).map a.down.op
    (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n + 1⦌))) = _root_.Quotient.mk _ a
  rw [SSet.stdSimplex.map_objEquiv_symm, Category.comp_id]
  rfl

/-- Every projected original resolving simplex gives the same whole enriched insertion as
its original
  operator of the distinguished simplex. -/
theorem projected_functor (n : ℕ) {m : SimplexCategory}
    (a : (Δ[n + 1] : SSet.{u}).obj (op m)) :
    coherentSimplexMap a.down ≫ functor n =
      simplexInto (FixedFrontCollapse.object n) ((projection n).app (op m) a) :=
  (simplexInto_operator (FixedFrontCollapse.object n) a.down (simplex n)).trans
    (congrArg (simplexInto (FixedFrontCollapse.object n)) (projected_operator n a))

/-- Every actual fixed-front resolving simplex has an original successor-simplex representative. -/
theorem exists_representative (n : ℕ) {m : SimplexCategory}
    (σ : (FixedFrontCollapse.object.{u} n).obj (op m)) :
    ∃ a : (Δ[n + 1] : SSet.{u}).obj (op m), (projection n).app (op m) a = σ := by
  induction σ using _root_.Quotient.inductionOn with
  | _ a => exact ⟨a, rfl⟩

/-- Each actual whole enriched simplex insertion is an original operator of the
distinguished successor simplex. -/
theorem exists_operator (n : ℕ) {m : SimplexCategory}
    (σ : (FixedFrontCollapse.object.{u} n).obj (op m)) :
    ∃ a : (Δ[n + 1] : SSet.{u}).obj (op m),
      coherentSimplexMap a.down ≫ functor n = simplexInto (FixedFrontCollapse.object n) σ := by
  obtain ⟨a, rfl⟩ := exists_representative n σ
  exact ⟨a, projected_functor n a⟩

end CategoryTheory.CoherentRealization.FixedFrontInsertion
