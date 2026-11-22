/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.SequentialBoundaryScalarPresentation
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectBoundaryCofibrantRetract
import MathlibExt.CategoryTheory.SmallObject.BoundaryOmegaIndex
import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic

/-!
# Full actual scalar generators of the original boundary source

The SAME original small-object boundary cell diagram is reindexed along
the proved native omega stage order isomorphism. Every original stage,
whole successor cell and terminal cocone is retained. The constructed
compatible sequential presentations give the full scalar free
presentation of its SAME original boundary factorization source.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra Opposite
attribute [local instance] Cardinal.fact_isRegular_aleph0 Cardinal.orderBotAleph0OrdToType

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FreeFactorization
open RelativeWords
variable {O : Type u} (C : FixedObjects O)

/-- Reindex the SAME entire original boundary-cell diagram by its native natural-number stages. -/
def boundarySequence : ℕ ⥤ FixedObjects O :=
  SmallObject.aleph0StageOrderIso.equivalence.functor ⋙ (boundaryCells (initial.to C)).F

/-- The SAME complete original terminal boundary-cell cocone, with its original legs. -/
def boundarySequenceCocone : Cocone (boundarySequence C) :=
  (Cocone.mk (cofibrantSource C) (boundaryCells (initial.to C)).incl).whisker
    SmallObject.aleph0StageOrderIso.equivalence.functor

/-- The SAME original whole boundary source is the actual colimit of those SAME original stages. -/
def boundarySequenceIsColimit : IsColimit (boundarySequenceCocone C) :=
  IsColimit.whiskerEquivalence (boundaryCells (initial.to C)).isColimit
    SmallObject.aleph0StageOrderIso.equivalence

/-- The first reindexed stage retains the exact original boundary diagram bottom isomorphism. -/
def boundarySequenceZeroIso : (boundarySequence C).obj 0 ≅ ⊥_ (FixedObjects O) :=
  (boundaryCells (initial.to C)).F.mapIso (eqToIso SmallObject.aleph0Stage_zero) ≪≫
    (boundaryCells (initial.to C)).isoBot

/-- Every successor retains the full original actual boundary-cell attachment. -/
def boundarySequenceCells (n : ℕ) :
    AttachCells.{u} (boundaryFamily O).homFamily
      ((boundarySequence C).map (homOfLE (n.le_add_right 1))) := by
  let j := SmallObject.aleph0Stage.{u} n
  let _ : NoMaxOrder Cardinal.aleph0.{u}.ord.ToType := Cardinal.noMaxOrder (le_refl _)
  let a := (boundaryCells (initial.to C)).attachCells j (not_isMax j)
  let e : (boundaryCells (initial.to C)).F.obj (Order.succ j) ≅
      (boundarySequence C).obj (n+1) :=
    (boundaryCells (initial.to C)).F.mapIso (eqToIso (SmallObject.aleph0Stage_succ n).symm)
  refine a.ofArrowIso (Arrow.isoMk (Iso.refl _) e ?_)
  change 𝟙 _ ≫ (boundaryCells (initial.to C)).F.map
    (SmallObject.aleph0StageOrderIso.equivalence.functor.map (homOfLE (n.le_add_right 1))) =
    (boundaryCells (initial.to C)).F.map (homOfLE (Order.le_succ j)) ≫
      (boundaryCells (initial.to C)).F.map
        (eqToHom (SmallObject.aleph0Stage_succ n).symm)
  rw [Category.id_comp, ← Functor.map_comp]
  apply congrArg (boundaryCells (initial.to C)).F.map
  exact Subsingleton.elim _ _

/-- Construct the SAME original bottom-stage scalar free presentation. -/
def boundarySequenceZeroPresentation (q : SimplexCategoryᵒᵖ) :
    FreePresentation.{u,u,u} (scalarCategory ((boundarySequence C).obj 0) q) where
  quiver := (InitialScalarFreePresentation.presentation (O := O) q).quiver
  map {a b} p := (homMap (boundarySequenceZeroIso C).inv a b).app q
    ((InitialScalarFreePresentation.presentation (O := O) q).map p)
  map_id a := by
    rw [(InitialScalarFreePresentation.presentation (O := O) q).map_id]
    exact congr($(identityMap_homMap (boundarySequenceZeroIso C).inv a).app q PUnit.unit)
  map_comp {a b d} p r := by
    rw [(InitialScalarFreePresentation.presentation (O := O) q).map_comp]
    exact congr($(compositionMap_homMap (boundarySequenceZeroIso C).inv a b d).app q
      ((InitialScalarFreePresentation.presentation (O := O) q).map p,
        (InitialScalarFreePresentation.presentation (O := O) q).map r))
  bijective a b := by
    let e := (evaluation a b).mapIso (boundarySequenceZeroIso C).symm
    let eq := ((CategoryTheory.evaluation _ _).obj q).mapIso e
    have h := ConcreteCategory.bijective_of_isIso eq.hom
    exact h.comp ((InitialScalarFreePresentation.presentation (O := O) q).bijective a b)

/-- Every full scalar category of the SAME actual original boundary factorization source is genuinely free. -/
def boundarySourceScalarPresentation (q : SimplexCategoryᵒᵖ) :
    FreePresentation.{u,u,u} (scalarCategory (cofibrantSource C) q) :=
  SequentialBoundaryScalarPresentation.terminalPresentation (boundarySequence C)
    (boundarySequenceCells C) q (boundarySequenceZeroPresentation C q)
    (boundarySequenceCocone C) (boundarySequenceIsColimit C)

end CategoryTheory.SimplicialEnrichment.FixedObjects.FreeFactorization
