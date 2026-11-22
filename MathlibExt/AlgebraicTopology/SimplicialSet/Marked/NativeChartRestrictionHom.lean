/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeSimplexUnRestriction

/-!
# Exact whole native chart restriction Hom equation

The original native chart restriction is defined by the same actual
straightening and original image/unit mates. Its Hom equation follows
from the whole native adjunction and original chart unit inverse laws.
This relates the original scalar restriction and actual cone-section
readbacks without a comparison outcome premise.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Postcomposition of the actual native image unit mate reads exactly the original native chart Hom correspondence. -/
theorem nativeSimplexImageIso_post_homEquiv (B : SSet.{u}) (n : ℕ) (σ : B _⦋n⦌)
    (F : EnrichedDiagram (realization B)ᵒᵖ) (g : nativeSimplexChart B n σ ⟶ F) :
    (nativeStraighteningAdjunction B).homEquiv _ _ ((nativeSimplexImageIso B n σ).hom ≫ g) =
      nativeSimplexChartHomEquiv B n σ F g := by
  have h := (nativeStraighteningAdjunction B).homEquiv_naturality_right
    (nativeSimplexImageIso B n σ).hom g
  have hc := nativeSimplexChartHomEquiv_natural_right B n σ (𝟙 _) g
  rw [Category.id_comp] at hc
  exact h.trans ((congrArg (fun f => f ≫ (nativeUnstraightening B).map g)
    (nativeSimplexImageIso_homEquiv B n σ)).trans hc.symm)

/-- Precomposing the actual native chart by its original restriction reads exactly precomposition of the
  same whole native unstraightening simplex. -/
theorem nativeChartRestriction_homEquiv (B : SSet.{u}) {n m : ℕ}
    (f : ⦋n⦌ ⟶ ⦋m⦌) (σ : B _⦋m⦌) (F : EnrichedDiagram (realization B)ᵒᵖ)
    (g : nativeSimplexChart B m σ ⟶ F) :
    nativeSimplexChartHomEquiv B n (B.map f.op σ) F (nativeSimplexChartRestriction B f σ ≫ g) =
      nativeSimplexRestriction B f σ ≫ nativeSimplexChartHomEquiv B m σ F g := by
  let e := nativeSimplexImageIso B n (B.map f.op σ)
  let d := nativeSimplexImageIso B m σ
  have hS := nativeSimplexChartRestriction_square B f σ
  have hS' : e.hom ≫ (nativeSimplexChartRestriction B f σ ≫ g) =
      (nativeStraightening B).map (nativeSimplexRestriction B f σ) ≫ (d.hom ≫ g) :=
    (Category.assoc _ _ _).symm.trans ((congrArg (fun f => f ≫ g) hS).trans (Category.assoc _ _ _))
  have hA := congrArg (fun g' => (nativeStraighteningAdjunction B).homEquiv _ _ g') hS'
  have hr := (nativeStraighteningAdjunction B).homEquiv_naturality_left (nativeSimplexRestriction B f σ)
    (d.hom ≫ g)
  exact (nativeSimplexImageIso_post_homEquiv B n (B.map f.op σ) F _).symm.trans
    (hA.trans (hr.trans (congrArg (fun f' => nativeSimplexRestriction B f σ ≫ f')
      (nativeSimplexImageIso_post_homEquiv B m σ F g))))

end SSet.Marked
