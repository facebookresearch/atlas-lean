/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeCofacePositiveBoundarySection

/-!
# Exact original positive coface base-unit transports

The whole original native base-restriction transport evaluated at a
positive coefficient composes with its proved original coface target
equality to exactly the original double-coface vertex transport. This
keeps the original marked source coefficients and native unit maps.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

private theorem indexEqToHom_component (n : ℕ) {F G : EnrichedDiagram (Index.{u} n)ᵒᵖ}
    (h : F = G) (i : (Index.{u} n)ᵒᵖ) :
    (eqToHom h).app i = eqToHom (congrArg (fun A : EnrichedDiagram (Index.{u} n)ᵒᵖ => A.obj i) h) := by
  cases h
  rfl

/-- The actual whole original coface base-restriction unit transport at every positive coefficient composes to
precisely the same original double-coface vertex/base transport. -/
theorem nativeCofacePositiveUnitTransport (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌)
    (k : Fin (n + 3)) (hk : 0 < k) (i : Vertex.{u} n) :
    ((eqToHom (nativeChartBase_restriction_comp B (SimplexCategory.δ k) σ)).app
      (nativeSubcomplexChart B (n + 2) σ (boundary (n + 2)))).app
        (op (SimplicialThickening.mk (coneTailEmbedding n i))) ≫
          eqToHom (nativeCofacePositiveTarget B n σ k hk i) =
      eqToHom (congrArg (fun v : Vertex.{u} (n + 2) =>
        (nativeSubcomplexChart B (n + 2) σ (boundary (n + 2))).obj
          ((EnrichedFunctor.opposite (simplexInto B σ)).obj (op (SimplicialThickening.mk v))))
            (coneTailCofaceVertex k hk i).symm) := by
  let S := nativeSubcomplexChart B (n + 2) σ (boundary (n + 2))
  let h := nativeChartBase_restriction_comp B (SimplexCategory.δ k) σ
  let x := op (SimplicialThickening.mk (coneTailEmbedding n i))
  let hS := Functor.congr_obj h S
  let h₀ := congrArg (fun F : EnrichedDiagram (Index.{u} (n + 1))ᵒᵖ => F.obj x) hS
  let h₁ := nativeCofacePositiveTarget B n σ k hk i
  have ht : ((eqToHom h).app S).app x = eqToHom h₀ :=
    (congrArg (fun z => z.app x) (eqToHom_app h S)).trans (indexEqToHom_component (n + 1) hS x)
  exact (congrArg (fun z => z ≫ eqToHom h₁) ht).trans (eqToHom_trans h₀ h₁)

end SSet.Marked
