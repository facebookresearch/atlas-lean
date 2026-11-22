/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCofacePositiveCoefficient
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativePositiveBoundaryTailSection
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeBoundaryUnitDoubleCoface

/-!
# Genuine original positive coface sections in the same native boundary

The original coface and face-zero double-coface relation is an equality
inside the actual native boundary source. The whole original tail
coefficient isomorphism cancels its original cone-image parametrization.
Consequently every original positive coface coefficient has exactly the
same whole marked section as the original positive-boundary inverse,
with both original coherent base and vertex transports retained.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Every original positive coface coefficient has the same actual native source target as its unchanged face-zero
composite, through the original whole coherent base operator and original double-coface vertex equality. -/
theorem nativeCofacePositiveTarget (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌)
    (k : Fin (n + 3)) (hk : 0 < k) (i : Vertex.{u} n) :
    (nativeSubcomplexChart B (n + 2) σ (boundary (n + 2))).obj
      ((EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ k).op σ))).obj
        (op (SimplicialThickening.mk (coneTailEmbedding n i)))) =
      (nativeSubcomplexChart B (n + 2) σ (boundary (n + 2))).obj
        ((EnrichedFunctor.opposite (simplexInto B σ)).obj
          (op (SimplicialThickening.mk (coneTailEmbedding (n + 1) (coneCofaceEmbedding (k.pred (ne_of_gt hk)) i)))))
            := by
  let S := nativeSubcomplexChart B (n + 2) σ (boundary (n + 2))
  let b := EnrichedFunctor.opposite (simplexInto B σ)
  have hi := nativeChartOperatorBaseObject B (SimplexCategory.δ k) σ
    (op (SimplicialThickening.mk (coneTailEmbedding n i)))
  have hv := congrArg (fun v : Vertex.{u} (n + 2) => b.obj (op (SimplicialThickening.mk v)))
    (coneTailCofaceVertex k hk i).symm
  exact congrArg S.obj (hi.trans hv)

private theorem coefficient_heq_same_target {A X Y T : Marked.{u}}
    (a : A ⟶ X) (b : A ⟶ Y) (hab : HEq a b) (hx : X = T) (hy : Y = T) :
    a ≫ eqToHom hx = b ≫ eqToHom hy := by
  cases hx
  cases hy
  exact (Category.comp_id a).trans ((eq_of_heq hab).trans (Category.comp_id b).symm)

private theorem coefficient_heq_transport {A X Y : Marked.{u}} (h : X = Y)
    (a : A ⟶ X) (b : A ⟶ Y) (hab : HEq a b) : a ≫ eqToHom h = b := by
  cases h
  exact (Category.comp_id a).trans (eq_of_heq hab)

/-- The whole marked original native boundary coface section at every positive coefficient is precisely the same
original positive-boundary section through its unchanged coface cone-image coefficient map and genuine original
base/vertex transports. -/
theorem nativeCofacePositiveBoundarySection_unit (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌)
    (k : Fin (n + 3)) (hk : 0 < k) (i : Vertex.{u} n) :
    (EnrichedLeftKan.universalHomEquiv
      (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ k).op σ)))
      (coneDiagram (n + 1)) (nativeSubcomplexChart B (n + 2) σ (boundary (n + 2)))
      (nativeBoundaryCofaceChartMap B (n + 1) σ k)).app (op (SimplicialThickening.mk (coneTailEmbedding n i))) ≫
        eqToHom (nativeCofacePositiveTarget B n σ k hk i) =
      coneCofacePositiveCoefficient k hk i ≫
        (nativePositiveRootBoundarySection B σ).app
          (op (SimplicialThickening.mk (coneTailEmbedding (n + 1) (coneCofaceEmbedding (k.pred (ne_of_gt hk)) i))))
            := by
  let S := nativeSubcomplexChart B (n + 2) σ (boundary (n + 2))
  let fi := coneCofaceEmbedding (k.pred (ne_of_gt hk)) i
  let ti := coneTailEmbedding n i
  let v := coneTailEmbedding (n + 1) fi
  let U₀ := EnrichedLeftKan.universalHomEquiv
    (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ (0 : Fin (n + 3))).op σ)))
    (coneDiagram (n + 1)) S (nativeBoundaryCofaceChartMap B (n + 1) σ (0 : Fin (n + 3)))
  let U := EnrichedLeftKan.universalHomEquiv
    (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ k).op σ)))
    (coneDiagram (n + 1)) S (nativeBoundaryCofaceChartMap B (n + 1) σ k)
  let P := nativePositiveRootBoundarySection B σ
  let f := (coneCofaceEmbedding.{u} (k.pred (ne_of_gt hk))).toOrderHom
  let c := (coneTailEmbedding.{u} n).toOrderHom
  let e := coneTailCoefficientIso n i
  let a := (coneTailAfterCoefficientIso (n + 1) fi).hom
  let Φ := coneCofacePositiveCoefficient k hk i
  let h₀ := congrArg S.obj (nativeChartOperatorBaseObject B (SimplexCategory.δ (0 : Fin (n + 3))) σ
    (op (SimplicialThickening.mk fi)))
  let h₁ := nativeCofacePositiveTarget B n σ k hk i
  have hd := nativeBoundaryCofaceSections_double_heq B n σ (0 : Fin (n + 2)) k hk
    (op (SimplicialThickening.mk i))
  have hp : (coneImage f i ≫ U₀.app (op (SimplicialThickening.mk fi))) ≫ eqToHom h₀ =
      (coneImage c i ≫ U.app (op (SimplicialThickening.mk ti))) ≫ eqToHom h₁ :=
    coefficient_heq_same_target _ _ hd h₀ h₁
  have ht : U₀.app (op (SimplicialThickening.mk fi)) ≫ eqToHom h₀ = a ≫ P.app (op (SimplicialThickening.mk v)) :=
    coefficient_heq_transport h₀ _ _
      (nativePositiveBoundarySection_tail_heq B (n + 1) σ (op (SimplicialThickening.mk fi)))
  have hf : coneImage f i ≫ a = e.hom ≫ Φ := coneCofacePositiveCoefficient_tail k hk i
  have hl : (coneImage f i ≫ U₀.app (op (SimplicialThickening.mk fi))) ≫ eqToHom h₀ =
      e.hom ≫ (Φ ≫ P.app (op (SimplicialThickening.mk v))) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => coneImage f i ≫ z) ht).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫ P.app (op (SimplicialThickening.mk v))) hf).trans (Category.assoc _ _ _))))
  have hr : (coneImage c i ≫ U.app (op (SimplicialThickening.mk ti))) ≫ eqToHom h₁ =
      e.hom ≫ (U.app (op (SimplicialThickening.mk ti)) ≫ eqToHom h₁) :=
    (Category.assoc _ _ _).trans
      (congrArg (fun z => z ≫ (U.app (op (SimplicialThickening.mk ti)) ≫ eqToHom h₁)) (coneTailCoefficientIso_hom n
        i).symm)
  apply (cancel_epi e.hom).mp
  exact hr.symm.trans (hp.symm.trans hl)

end SSet.Marked
