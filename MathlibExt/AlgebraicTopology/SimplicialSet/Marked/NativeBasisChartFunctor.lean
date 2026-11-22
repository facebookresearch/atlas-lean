/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeBasisChart

/-!
# The actual native straightening functor on the marked presentation basis

Every basis object uses its actual proved native chart. A whole marked
basis map extends through the original chart Hom correspondence and
target unit. Proved target naturality gives identities, composition
and the whole unit square. No chart family or functor outcome is an
input to the construction.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace SSet.Marked
open CategoryTheory.CoherentRealization

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

variable (B : SSet.{u})

/-- The original marked basis objects over the supplied original base. -/
def nativeBasisFunctor : GeneratorBasis.Index (max B) ⥤ Over (max B) where
  obj i := Over.mk i.hom
  map {i j} f := Over.homMk (GeneratorBasis.generatorFunctor.map f.left) (CostructuredArrow.w f)
  map_id i := by apply Over.OverMorphism.ext; rfl
  map_comp f g := by apply Over.OverMorphism.ext; rfl

/-- Every original basis object retains its actual native simplex or sharp-edge chart. -/
def nativeBasisChartObject (i : GeneratorBasis.Index (max B)) : EnrichedDiagram (realization B)ᵒᵖ :=
  nativeBasisRepresenter B i.left i.hom

/-- Its whole Hom correspondence is the already proved native chart correspondence on the same basis object. -/
def nativeBasisChartEquiv (i : GeneratorBasis.Index (max B)) (F : EnrichedDiagram (realization B)ᵒᵖ) :
    (nativeBasisChartObject B i ⟶ F) ≃ ((nativeBasisFunctor B).obj i ⟶ (nativeUnstraightening B).obj F) :=
  nativeBasisRepresenterHomEquiv B i.left i.hom F

/-- The original basis-chart unit is the actual universal image of its identity map. -/
def nativeBasisChartUnit (i : GeneratorBasis.Index (max B)) :
    (nativeBasisFunctor B).obj i ⟶ (nativeUnstraightening B).obj (nativeBasisChartObject B i) :=
  nativeBasisChartEquiv B i (nativeBasisChartObject B i) (𝟙 _)

/-- The entire original marked basis map extends through its actual target chart and original basis unit. -/
def nativeBasisChartMap {i j : GeneratorBasis.Index (max B)} (f : i ⟶ j) :
    nativeBasisChartObject B i ⟶ nativeBasisChartObject B j :=
  (nativeBasisChartEquiv B i (nativeBasisChartObject B j)).symm
    ((nativeBasisFunctor B).map f ≫ nativeBasisChartUnit B j)

/-- The original native Hom image of the extended map is precisely its whole basis map followed by the actual unit. -/
theorem nativeBasisChartMap_equiv {i j : GeneratorBasis.Index (max B)} (f : i ⟶ j) :
    nativeBasisChartEquiv B i (nativeBasisChartObject B j) (nativeBasisChartMap B f) =
      (nativeBasisFunctor B).map f ≫ nativeBasisChartUnit B j :=
  (nativeBasisChartEquiv B i (nativeBasisChartObject B j)).apply_symm_apply _

/-- The entire basis-chart unit is natural on every original marked basis map. -/
theorem nativeBasisChartUnit_natural {i j : GeneratorBasis.Index (max B)} (f : i ⟶ j) :
    nativeBasisChartUnit B i ≫ (nativeUnstraightening B).map (nativeBasisChartMap B f) =
      (nativeBasisFunctor B).map f ≫ nativeBasisChartUnit B j := by
  have h := nativeBasisRepresenterHomEquiv_natural_right B i.left i.hom
    (𝟙 (nativeBasisChartObject B i)) (nativeBasisChartMap B f)
  exact h.symm.trans
    ((congrArg (nativeBasisRepresenterHomEquiv B i.left i.hom (nativeBasisChartObject B j))
      (Category.id_comp (nativeBasisChartMap B f))).trans (nativeBasisChartMap_equiv B f))

/-- The original basis identity extends to the actual identity of its entire native chart. -/
theorem nativeBasisChartMap_id (i : GeneratorBasis.Index (max B)) :
    nativeBasisChartMap B (𝟙 i) = 𝟙 (nativeBasisChartObject B i) := by
  apply (nativeBasisChartEquiv B i (nativeBasisChartObject B i)).injective
  exact (nativeBasisChartMap_equiv B (𝟙 i)).trans
    ((congrArg (fun f => f ≫ nativeBasisChartUnit B i) ((nativeBasisFunctor B).map_id i)).trans
      (Category.id_comp (nativeBasisChartUnit B i)))

/-- Consecutive whole marked basis maps extend through their original native chart composition. -/
theorem nativeBasisChartMap_comp {i j k : GeneratorBasis.Index (max B)} (f : i ⟶ j) (g : j ⟶ k) :
    nativeBasisChartMap B (f ≫ g) = nativeBasisChartMap B f ≫ nativeBasisChartMap B g := by
  apply (nativeBasisChartEquiv B i (nativeBasisChartObject B k)).injective
  have hr : nativeBasisChartEquiv B i (nativeBasisChartObject B k)
      (nativeBasisChartMap B f ≫ nativeBasisChartMap B g) =
        ((nativeBasisFunctor B).map f ≫ nativeBasisChartUnit B j) ≫
          (nativeUnstraightening B).map (nativeBasisChartMap B g) :=
    (nativeBasisRepresenterHomEquiv_natural_right B i.left i.hom
      (nativeBasisChartMap B f) (nativeBasisChartMap B g)).trans
      (congrArg (fun t => t ≫ (nativeUnstraightening B).map (nativeBasisChartMap B g))
        (nativeBasisChartMap_equiv B f))
  exact (nativeBasisChartMap_equiv B (f ≫ g)).trans
    ((congrArg (fun t => t ≫ nativeBasisChartUnit B k) ((nativeBasisFunctor B).map_comp f g)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun t => (nativeBasisFunctor B).map f ≫ t) (nativeBasisChartUnit_natural B g).symm).trans
          ((Category.assoc _ _ _).symm.trans hr.symm))))

/-- The actual native straightening chart functor on every original full marked basis morphism. -/
def nativeBasisChartFunctor : GeneratorBasis.Index (max B) ⥤ EnrichedDiagram (realization B)ᵒᵖ where
  obj := nativeBasisChartObject B
  map := nativeBasisChartMap B
  map_id := nativeBasisChartMap_id B
  map_comp := nativeBasisChartMap_comp B

end SSet.Marked
