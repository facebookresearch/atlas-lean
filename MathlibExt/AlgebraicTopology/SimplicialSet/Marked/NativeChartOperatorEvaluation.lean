/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeConeOperatorComparison

/-!
# Full original coefficient readback of every native chart operator

The entire native chart restriction has the original cone direct-image
operator followed by the actual target left-extension unit at each
original coefficient. The readback retains the actual base object and
whole marked map, so its equality is stated heterogeneously when the
original base-object presentations differ. Faces and degeneracies use
the same construction; no operator, mark or unit is replaced.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Every entire original coefficient component of the native chart operator is the same whole original cone
  image followed by the genuine target left-extension unit, with the original dependent base-object
  transport retained. -/
theorem nativeChartRestriction_component_heq (B : SSet.{u}) {n m : ℕ}
    (f : ⦋n⦌ ⟶ ⦋m⦌) (σ : B _⦋m⦌) (i : (Index.{u} n)ᵒᵖ) :
    HEq ((EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B (B.map f.op σ)))
      (coneDiagram n) (nativeSimplexChart B m σ) (nativeSimplexChartRestriction B f σ)).app i)
      (coneImage f.toOrderHom.uliftMap i.unop.as ≫
        (EnrichedLeftKan.unit (EnrichedFunctor.opposite (simplexInto B σ)) (coneDiagram m)).app
          (op ((indexMap f.toOrderHom.uliftMap).obj i.unop))) := by
  let F := nativeSimplexChart B m σ
  have hl := congrArg Subtype.val (nativeSimplexChartHomEquiv_section B n (B.map f.op σ) F
    (nativeSimplexChartRestriction B f σ))
  have hr := congrArg Subtype.val (nativeSimplexChartHomEquiv_section B m σ F (𝟙 _))
  have hraw := hl.symm.trans ((nativeChartRestriction_un_raw B f σ).trans
    (congrArg (fun a => a.pull f.toOrderHom.uliftMap) hr))
  let read := fun a : UnstraighteningSimplex F n =>
    (⟨a.base.obj i.unop, a.sectionMap.app i⟩ :
      Σ c : (realization B), coneWeight i.unop.as ⟶ F.obj (op c))
  exact (Sigma.mk.inj (congrArg read hraw)).2

end SSet.Marked
