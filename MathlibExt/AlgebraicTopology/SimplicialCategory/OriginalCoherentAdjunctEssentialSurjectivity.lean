/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentComponentHomotopyCategory
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentAdjunction
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedDwyerKanClasses

/-!
# Original coherent adjuncts retain actual essential surjectivity

The actual enriched counit factorization identifies the component
object of every original adjunct vertex with the same original object
of the enriched map. The genuine locally Kan component readback lifts
the supplied isomorphisms. Raw coherent realizations need not be Kan.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalQuillenComparison

open SimplicialEnrichment

/-- The full original adjunct vertex retains precisely the same actual original enriched object through its actual
counit factorization. -/
theorem adjunct_component_obj {K : SSet.{u}} {C : Carrier.{u}}
    (g : K ⟶ coherentNerveFunctor.obj C) (F : realization K ⟶ C)
    (hfac : realizationMap g ≫ counit C = F) (x : K _⦋0⦌) :
    (SSet.mapHomotopyCategory g ⋙ ComponentHomotopyCategory.readFunctor C).obj
      (SSet.HomotopyCategory.mk x) = ComponentCategory.objectOf.{u} C (F.obj x) := by
  change vertexOf C (g.app (op ⦋0⦌) x) = F.obj x
  exact congrArg (fun H : realization K ⟶ C => H.obj x) hfac

/-- Essential surjectivity of the SAME original component functor gives essential surjectivity of the SAME original
adjunct, using only the genuine original target Hom Kan hypotheses. -/
theorem adjunct_essSurj_of_component {K : SSet.{u}} {C : Carrier.{u}}
    (hKan : ∀ x y : C, SSet.KanComplex (x ⟶[SSet.{u}] y))
    (g : K ⟶ coherentNerveFunctor.obj C) (F : realization K ⟶ C)
    (hfac : realizationMap g ≫ counit C = F) (hF : (ComponentCategory.mapFunctor F).EssSurj) :
    (SSet.mapHomotopyCategory g).EssSurj := by
  let R := ComponentHomotopyCategory.readFunctor C
  let _ : R.IsEquivalence := ComponentHomotopyCategory.isEquivalence C hKan
  let _ : (SSet.mapHomotopyCategory g ⋙ R).EssSurj := by
    constructor
    intro y
    obtain ⟨x, hx⟩ := hF.mem_essImage y
    refine ⟨SSet.HomotopyCategory.mk x, ?_⟩
    exact (adjunct_component_obj g F hfac x).symm ▸ hx
  exact Functor.essSurj_of_comp_fully_faithful (SSet.mapHomotopyCategory g) R

end CategoryTheory.CoherentRealization.OriginalQuillenComparison
