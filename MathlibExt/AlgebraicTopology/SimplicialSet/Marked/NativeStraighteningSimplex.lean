/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeUnstraightening
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RepresentableSliceHom
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentUnstraighteningFibre
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedLeftKanAdjunction

/-!
# The actual native straightening chart of an original marked simplex

The chart is the proved marked enriched left extension of the original
maximum-marked cone weight along the whole coherent base simplex.
Its native Hom correspondence is exactly the original minimal simplex
slice Hom into unstraightening. The actual coherent unit, original
Yoneda representative and selected pullback are retained in both
directions; no chart-representation outcome is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The original minimally marked simplex lies over the original base through its exact Yoneda representative. -/
def nativeSimplexBasis (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) : Over (max B) :=
  Over.mk (toMax (SSet.yonedaEquiv.symm σ) : min (Δ[n] : SSet.{u}) ⟶ max B)

/-- The original native straightening chart is the actual marked left extension of its whole cone weight. -/
def nativeSimplexChart (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌) : EnrichedDiagram (realization B)ᵒᵖ :=
  EnrichedLeftKan.object (EnrichedFunctor.opposite (simplexInto B σ)) (coneDiagram n)

/-- Original same-base simplex maps into unstraightening are precisely the full cone sections over their
  actual coherent base simplex. -/
def nativeSimplexUnHomEquiv (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌)
    (F : EnrichedDiagram (realization B)ᵒᵖ) :
    (nativeSimplexBasis B n σ ⟶ (nativeUnstraightening B).obj F) ≃
      {a : UnstraighteningSimplex F n // a.base = simplexInto B σ} :=
  ((Over.mapPullbackAdj (maximal.map (unit B))).homEquiv
    (nativeSimplexBasis B n σ) ((coherentUnstraighteningFunctor (realization B)).obj F)).symm.trans
    ((overMinSimplexHomEquiv ((coherentUnstraighteningFunctor (realization B)).obj F) n
      (toMax (SSet.yonedaEquiv.symm σ ≫ unit B) : min (Δ[n] : SSet.{u}) ⟶
        max (coherentBase (realization B)))).trans
      (Equiv.subtypeEquiv (Equiv.refl _) (fun a => by
        change (a.base = SSet.yonedaEquiv (SSet.yonedaEquiv.symm σ ≫ unit B)) ↔ a.base = simplexInto B σ
        rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
        rfl)))

/-- The actual chart represents the whole original marked simplex slice Hom into native unstraightening. -/
def nativeSimplexChartHomEquiv (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌)
    (F : EnrichedDiagram (realization B)ᵒᵖ) :
    (nativeSimplexChart B n σ ⟶ F) ≃ (nativeSimplexBasis B n σ ⟶ (nativeUnstraightening B).obj F) :=
  (EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B σ)) (coneDiagram n) F).trans
    ((fixedSectionEquiv F (simplexInto B σ)).symm.trans (nativeSimplexUnHomEquiv B n σ F).symm)

end SSet.Marked
