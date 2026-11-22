/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedGadgetInputs
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalPointedCoherentHomFunctor
import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanAugmentation
import MathlibExt.AlgebraicTopology.SimplicialSet.SSetULiftPointWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanIndexNerveSquare

/-!
# The full original raw Hom gadget input diagram and augmentation

Every full original pointed gadget over K contributes its SAME entire
original raw endpoint Hom. All original input maps give the literal
coherent Hom evaluation. The canonical coefficient universe lift records
the actual u+1 input category without changing original coefficients.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalGadgetComparison

open OriginalPointed

/-- The actual full original gadget input indexing category. -/
abbrev Input (K : OriginalPointed.Category.{u}) := CostructuredArrow gadgetInclusion K

/-- The same full original raw Hom coefficient diagram on every complete original gadget input. -/
def rawHomDiagram (K : OriginalPointed.Category.{u}) : Input K ⥤ SSet.{u} :=
  CostructuredArrow.proj gadgetInclusion K ⋙ gadgetInclusion ⋙ homFunctor

/-- The literal same original raw Hom evaluation on each complete original input map. -/
def rawHomInputAugmentation (K : OriginalPointed.Category.{u}) :
    rawHomDiagram K ⟶ (Functor.const (Input K)).obj (homObject K) where
  app X := homFunctor.map X.hom
  naturality X Y f := by
    change homFunctor.map f.left.hom ≫ homFunctor.map Y.hom = homFunctor.map X.hom ≫ 𝟙 _
    exact (homFunctor.map_comp _ _).symm.trans
      ((congrArg homFunctor.map (CostructuredArrow.w f)).trans (Category.comp_id _).symm)

/-- The same complete original raw Hom diagram with its explicit actual indexing coefficient-universe lift. -/
def liftedRawHomDiagram (K : OriginalPointed.Category.{u}) : Input K ⥤ SSet.{u+1} :=
  rawHomDiagram K ⋙ SSet.uliftFunctor.{u+1,u}

/-- The same entire original input evaluation, lifted only in its actual coefficient universe. -/
def liftedRawHomInputAugmentation (K : OriginalPointed.Category.{u}) :
    liftedRawHomDiagram K ⟶ (Functor.const (Input K)).obj (SSet.uliftFunctor.{u+1,u}.obj (homObject K)) where
  app X := SSet.uliftFunctor.map ((rawHomInputAugmentation K).app X)
  naturality X Y f := by
    have h : (rawHomDiagram K).map f ≫ (rawHomInputAugmentation K).app Y =
        (rawHomInputAugmentation K).app X :=
      ((rawHomInputAugmentation K).naturality f).trans (Category.comp_id _)
    exact (SSet.uliftFunctor.map_comp _ _).symm.trans
      ((congrArg SSet.uliftFunctor.map h).trans (Category.comp_id _).symm)

/-- The actual canonical original raw Hom gadget hocolim augmentation at the explicit indexing universe. -/
def rawHomHocolimAugmentation (K : OriginalPointed.Category.{u}) :
    SSet.bkHocolim (liftedRawHomDiagram K) ⟶ SSet.uliftFunctor.{u+1,u}.obj (homObject K) :=
  SSet.bkAugmentation (liftedRawHomInputAugmentation K)

/-- Every full original gadget coefficient has its genuine original raw-Hom point weakness. -/
theorem rawHomDiagram_point_weak (K : OriginalPointed.Category.{u}) (X : Input K) :
    SSet.realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from ((rawHomDiagram K).obj X)) :=
  X.left.property.1

/-- The same full original gadget coefficient point weakness holds at its actual input indexing universe. -/
theorem liftedRawHomDiagram_point_weak (K : OriginalPointed.Category.{u}) (X : Input K) :
    SSet.realizationWeakEquivalences (SSet.stdSimplex.isTerminalObj₀.from ((liftedRawHomDiagram K).obj X)) :=
  (SSet.realizationWeak_ulift_point_iff.{u,u+1} ((rawHomDiagram K).obj X)).mpr
    (rawHomDiagram_point_weak K X)

/-- The actual original full gadget raw-Hom hocolim projection to its entire native input nerve is weak. -/
theorem rawHomHocolimNerveProjection_weak (K : OriginalPointed.Category.{u}) :
    SSet.realizationWeakEquivalences (SSet.bkHocolimToNerve (liftedRawHomDiagram K)) :=
  SSet.bkHocolimToNerve_weak _ (liftedRawHomDiagram_point_weak K)

end CategoryTheory.CoherentRealization.OriginalGadgetComparison
