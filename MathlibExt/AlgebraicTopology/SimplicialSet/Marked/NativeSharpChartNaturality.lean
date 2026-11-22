/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeStraighteningSharp

/-!
# Whole target naturality of the native sharp-edge chart

The inverse native pullback adjunction and interval Yoneda read the
entire original unstraightening edge. That readback detects the whole
marked slice map. The actual sharp-section inverse keeps precisely
the restricted cone section, and original coefficient composition
proves full target naturality of the native sharp chart.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The original raw coherent edge is read through the actual inverse unit-pullback adjunction and Yoneda. -/
def nativeSharpUnRaw (B : SSet.{u}) (σ : B _⦋1⦌) (F : EnrichedDiagram (realization B)ᵒᵖ)
    (f : nativeSharpBasis B σ ⟶ (nativeUnstraightening B).obj F) : UnstraighteningSimplex F 1 :=
  SSet.yonedaEquiv
    (((Over.mapPullbackAdj (maximal.map (unit B))).homEquiv (nativeSharpBasis B σ)
      ((coherentUnstraighteningFunctor (realization B)).obj F)).symm f).left.hom

/-- The original raw edge detects the whole native sharp marked slice map. -/
theorem nativeSharpUnRaw_injective (B : SSet.{u}) (σ : B _⦋1⦌)
    (F : EnrichedDiagram (realization B)ᵒᵖ) : Function.Injective (nativeSharpUnRaw B σ F) := by
  intro f g h
  apply (((Over.mapPullbackAdj (maximal.map (unit B))).homEquiv (nativeSharpBasis B σ)
    ((coherentUnstraighteningFunctor (realization B)).obj F)).symm).injective
  apply Over.OverMorphism.ext
  apply Hom.ext
  apply SSet.yonedaEquiv.injective
  exact h

/-- The exact marked section fibre retains the same original raw coherent edge. -/
theorem nativeSharpUnRaw_fixedSection (B : SSet.{u}) (σ : B _⦋1⦌)
    (F : EnrichedDiagram (realization B)ᵒᵖ) (f : nativeSharpBasis B σ ⟶ (nativeUnstraightening B).obj F) :
    ((fixedSharpSectionEquiv F (simplexInto B σ)).symm (nativeSharpUnSectionEquiv B σ F f)).val.val =
      nativeSharpUnRaw B σ F f := by
  change ((fixedSharpSectionEquiv F (simplexInto B σ)).symm
    ((fixedSharpSectionEquiv F (simplexInto B σ)) (nativeSharpUnMarkedFibreEquiv B σ F f))).val.val = _
  exact congrArg (fun a => a.val.val)
    ((fixedSharpSectionEquiv F (simplexInto B σ)).symm_apply_apply (nativeSharpUnMarkedFibreEquiv B σ F f))

/-- The inverse original sharp section has precisely its original restricted cone section and full base edge. -/
theorem nativeSharpUnRaw_inverseSection (B : SSet.{u}) (σ : B _⦋1⦌)
    (F : EnrichedDiagram (realization B)ᵒᵖ)
    (a : EnrichedDiagramMap (sharpConeDiagram 1) (simplexCoefficient F (simplexInto B σ))) :
    nativeSharpUnRaw B σ F ((nativeSharpUnSectionEquiv B σ F).symm a) =
      ⟨simplexInto B σ, coneSharp 1 ≫ a⟩ := by
  have h := nativeSharpUnRaw_fixedSection B σ F ((nativeSharpUnSectionEquiv B σ F).symm a)
  have he := congrArg (fun b => ((fixedSharpSectionEquiv F (simplexInto B σ)).symm b).val.val)
    ((nativeSharpUnSectionEquiv B σ F).apply_symm_apply a)
  exact h.symm.trans he

/-- Actual whole coefficient composition sends the original raw sharp edge to its same original coefficient image. -/
theorem nativeSharpUnRaw_post (B : SSet.{u}) (σ : B _⦋1⦌)
    {F G : EnrichedDiagram (realization B)ᵒᵖ}
    (f : nativeSharpBasis B σ ⟶ (nativeUnstraightening B).obj F) (φ : F ⟶ G) :
    nativeSharpUnRaw B σ G (f ≫ (nativeUnstraightening B).map φ) =
      (nativeSharpUnRaw B σ F f).mapCoefficient φ := by
  let a := Over.mapPullbackAdj (maximal.map (unit B))
  let K := nativeSharpBasis B σ
  let U := coherentUnstraighteningFunctor (realization B)
  have h := a.homEquiv_naturality_right_symm f (U.map φ)
  exact congrArg (fun g : (Over.map (maximal.map (unit B))).obj K ⟶ U.obj G =>
    SSet.yonedaEquiv g.left.hom) h

/-- The actual whole sharp-chart Hom correspondence is natural on every original marked coefficient map. -/
theorem nativeSharpChartHomEquiv_natural_right (B : SSet.{u}) (σ : B _⦋1⦌)
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (f : nativeSharpChart B σ ⟶ F) (φ : F ⟶ G) :
    nativeSharpChartHomEquiv B σ G (f ≫ φ) =
      nativeSharpChartHomEquiv B σ F f ≫ (nativeUnstraightening B).map φ := by
  apply nativeSharpUnRaw_injective B σ G
  have hn := EnrichedLeftKan.universalHomEquiv_natural_right
    (EnrichedFunctor.opposite (simplexInto B σ)) (sharpConeDiagram 1) f φ
  have hf := nativeSharpUnRaw_inverseSection B σ F
    (EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B σ)) (sharpConeDiagram 1) F f)
  have hg := nativeSharpUnRaw_inverseSection B σ G
    (EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B σ)) (sharpConeDiagram 1) G (f ≫ φ))
  have hc :
      (⟨simplexInto B σ,
        coneSharp 1 ≫ EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B σ))
          (sharpConeDiagram 1) G (f ≫ φ)⟩ : UnstraighteningSimplex G 1) =
        (⟨simplexInto B σ,
          coneSharp 1 ≫ EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B σ))
            (sharpConeDiagram 1) F f⟩ : UnstraighteningSimplex F 1).mapCoefficient φ := by
    apply UnstraighteningSimplex.ext rfl
    apply heq_of_eq
    exact (congrArg (fun a => coneSharp 1 ≫ a) hn).trans (Category.assoc _ _ _).symm
  exact hg.trans
    (hc.trans ((congrArg (fun a => a.mapCoefficient φ) hf.symm).trans (nativeSharpUnRaw_post B σ _ φ).symm))

end SSet.Marked
