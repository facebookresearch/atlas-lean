/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.WeakEquivalences
import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerMapping
import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerHomColimits

/-!
# Coproduct closure of monic all-CSS Rezk weak maps

The actual supplied source/target coproduct cocones and their original total
comparison are retained. Scalar opposite left-lifting closure and actual
inner-Hom colimit preservation prove weakness at every same-u CSS target;
monicity follows separately from the named Reedy cofibration dictionary.
Empty coproducts are included without identifying different initial points.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open CategoryTheory.MorphismProperty
open scoped SimplicialSpace.Inner
namespace SimplicialSpace

/-- Supplied coproducts of original monic ALL-CSS weak arrows stay monic and weak. -/
theorem monomorphisms_inf_rezkWeakEquivalences_isStableUnderCoproducts :
    (monomorphisms SimplicialSpace.{u} ⊓ rezkWeakEquivalences.{u}).IsStableUnderCoproducts.{u} := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  constructor
  intro J
  constructor
  intro F₁ F₂ c₁ c₂ hc₁ hc₂ f hf φ hφ
  have hcof (a : Discrete J) : cofibrations SimplicialSpace.{u} (f.app a) :=
    (HomotopicalAlgebra.cofibration_iff _).mp ((ReedyModel.cofibration_iff _).mpr (hf a).1)
  have hφcof : cofibrations SimplicialSpace.{u} φ :=
    (inferInstance : (cofibrations SimplicialSpace.{u}).IsStableUnderCoproductsOfShape J).condition
      F₁ F₂ c₁ c₂ hc₁ hc₂ f hcof φ hφ
  change Mono φ ∧ rezkWeakEquivalences φ
  refine ⟨(ReedyModel.cofibration_iff φ).mp
    ((HomotopicalAlgebra.cofibration_iff φ).mpr hφcof), ?_⟩
  intro Z hZ
  let G := (innerHomFunctor.{u}.flip.obj Z).rightOp
  let P := (cofibrations SSet.{u}).op.llp
  let _ : PreservesColimitsOfShape (Discrete J) G :=
    innerHom_rightOp_preservesColimitsOfShape (Discrete J) Z
  have hcomponent (a : Discrete J) : P (G.map (f.app a)) := by
    have hgF : fibrations SSet.{u} ((innerHomFunctor.map (f.app a).op).app Z) :=
      ReedyModel.inner_precomp_fibration (f.app a) Z (hcof a) hZ.1
    have hgTF : trivialFibrations SSet.{u} ((innerHomFunctor.map (f.app a).op).app Z) :=
      ⟨hgF, (hf a).2 Z hZ⟩
    have hgRLP : (cofibrations SSet.{u}).rlp
        ((innerHomFunctor.map (f.app a).op).app Z) := by
      rw [cofibrations_rlp SSet.{u}]
      exact hgTF
    intro A B i hi
    change cofibrations SSet.{u} i.unop at hi
    change HasLiftingProperty ((innerHomFunctor.map (f.app a).op).app Z).op i
    simpa only [Quiver.Hom.op_unop] using (hgRLP i.unop hi).op
  have hmapped (a : Discrete J) :
      (G.mapCocone c₁).ι.app a ≫ G.map φ =
        (Functor.whiskerRight f G).app a ≫ (G.mapCocone c₂).ι.app a := by
    change G.map (c₁.ι.app a) ≫ G.map φ = G.map (f.app a) ≫ G.map (c₂.ι.app a)
    simpa only [Functor.map_comp] using congrArg (fun g => G.map g) (hφ a)
  have hwhole : P (G.map φ) :=
    (inferInstance : P.IsStableUnderCoproductsOfShape J).condition
      (F₁ ⋙ G) (F₂ ⋙ G) (G.mapCocone c₁) (G.mapCocone c₂)
      (isColimitOfPreserves G hc₁) (isColimitOfPreserves G hc₂)
      (Functor.whiskerRight f G) hcomponent (G.map φ) hmapped
  have hRLP : (cofibrations SSet.{u}).rlp ((innerHomFunctor.map φ.op).app Z) := by
    intro A B i hi
    have hh : HasLiftingProperty (G.map φ) i.op := hwhole i.op hi
    have hu := hh.unop
    change HasLiftingProperty i ((innerHomFunctor.map φ.op).app Z) at hu
    exact hu
  have hTF : trivialFibrations SSet.{u} ((innerHomFunctor.map φ.op).app Z) := by
    rw [← cofibrations_rlp SSet.{u}]
    exact hRLP
  exact hTF.2

end SimplicialSpace
