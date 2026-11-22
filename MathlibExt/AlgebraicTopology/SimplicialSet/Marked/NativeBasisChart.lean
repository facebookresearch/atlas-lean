/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeSimplexChartNaturality
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeSharpChartNaturality
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.GeneratorBasisOver

/-!
# Actual native charts of the complete marked presentation basis

Every original basis map has its native simplex or sharp-edge chart.
The concrete source identification uses only the original whole
Yoneda map, with identity underlying carrier maps. The full Hom
correspondence and its target naturality retain the actual original
marked source and base projection.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Each original marked basis map has its actual simplex or sharp-edge straightening chart. -/
def nativeBasisRepresenter (B : SSet.{u}) :
    (k : GeneratorBasis.Generator.{u}) → (GeneratorBasis.generatorFunctor.obj k ⟶ max B) →
      EnrichedDiagram (realization B)ᵒᵖ
  | some n, p => nativeSimplexChart B n (SSet.yonedaEquiv p.hom)
  | none, p => nativeSharpChart B (SSet.yonedaEquiv p.hom)

/-- The original basis projection equals its exact full Yoneda representative. -/
private theorem simplexProjection_eq (B : SSet.{u}) (n : ℕ) (p : min (Δ[n] : SSet.{u}) ⟶ max B) :
    toMax (SSet.yonedaEquiv.symm (SSet.yonedaEquiv p.hom)) = p :=
  Hom.ext (SSet.yonedaEquiv.symm_apply_apply _)

private theorem sharpProjection_eq (B : SSet.{u}) (p : max (Δ[1] : SSet.{u}) ⟶ max B) :
    toMax (SSet.yonedaEquiv.symm (SSet.yonedaEquiv p.hom)) = p :=
  Hom.ext (SSet.yonedaEquiv.symm_apply_apply _)

/-- The actual marked basis chart represents its entire original same-base slice Hom into native unstraightening. -/
def nativeBasisRepresenterHomEquiv (B : SSet.{u}) (k : GeneratorBasis.Generator.{u})
    (p : GeneratorBasis.generatorFunctor.obj k ⟶ max B) (F : EnrichedDiagram (realization B)ᵒᵖ) :
    (nativeBasisRepresenter B k p ⟶ F) ≃ (Over.mk p ⟶ (nativeUnstraightening B).obj F) := by
  cases k with
  | some n =>
      let e := eqToIso (congrArg (fun p : min (Δ[n] : SSet.{u}) ⟶ max B => Over.mk p)
        (simplexProjection_eq B n p))
      exact (nativeSimplexChartHomEquiv B n (SSet.yonedaEquiv p.hom) F).trans
        (Iso.homCongr e (Iso.refl ((nativeUnstraightening B).obj F)))
  | none =>
      let e := eqToIso (congrArg (fun p : max (Δ[1] : SSet.{u}) ⟶ max B => Over.mk p)
        (sharpProjection_eq B p))
      exact (nativeSharpChartHomEquiv B (SSet.yonedaEquiv p.hom) F).trans
        (Iso.homCongr e (Iso.refl ((nativeUnstraightening B).obj F)))

/-- Whole marked target maps act naturally on the actual original marked basis chart correspondence. -/
theorem nativeBasisRepresenterHomEquiv_natural_right (B : SSet.{u}) (k : GeneratorBasis.Generator.{u})
    (p : GeneratorBasis.generatorFunctor.obj k ⟶ max B)
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (f : nativeBasisRepresenter B k p ⟶ F) (φ : F ⟶ G) :
    nativeBasisRepresenterHomEquiv B k p G (f ≫ φ) =
      nativeBasisRepresenterHomEquiv B k p F f ≫ (nativeUnstraightening B).map φ := by
  cases k with
  | some n =>
      let e := eqToIso (congrArg (fun p : min (Δ[n] : SSet.{u}) ⟶ max B => Over.mk p)
        (simplexProjection_eq B n p))
      let f' : nativeSimplexChart B n (SSet.yonedaEquiv p.hom) ⟶ F := f
      change e.inv ≫ nativeSimplexChartHomEquiv B n (SSet.yonedaEquiv p.hom) G (f' ≫ φ) =
        (e.inv ≫ nativeSimplexChartHomEquiv B n (SSet.yonedaEquiv p.hom) F f') ≫ _
      exact (congrArg (fun h => e.inv ≫ h)
        (nativeSimplexChartHomEquiv_natural_right B n (SSet.yonedaEquiv p.hom) f' φ)).trans
          (Category.assoc _ _ _).symm
  | none =>
      let e := eqToIso (congrArg (fun p : max (Δ[1] : SSet.{u}) ⟶ max B => Over.mk p)
        (sharpProjection_eq B p))
      let f' : nativeSharpChart B (SSet.yonedaEquiv p.hom) ⟶ F := f
      change e.inv ≫ nativeSharpChartHomEquiv B (SSet.yonedaEquiv p.hom) G (f' ≫ φ) =
        (e.inv ≫ nativeSharpChartHomEquiv B (SSet.yonedaEquiv p.hom) F f') ≫ _
      exact (congrArg (fun h => e.inv ≫ h)
        (nativeSharpChartHomEquiv_natural_right B (SSet.yonedaEquiv p.hom) f' φ)).trans
          (Category.assoc _ _ _).symm

end SSet.Marked
