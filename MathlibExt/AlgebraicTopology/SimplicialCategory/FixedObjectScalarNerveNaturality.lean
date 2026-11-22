/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectScalarNerveDiagrams

/-!
# Whole original fixed-label scalar nerve map naturality

The SAME original fixed-label maps and ordinal operators commute on
all original Hom simplices. Full native scalar nerve diagrams and
label-to-canonical comparisons retain each supplied object, coefficient
and original enriched functor. Diagonalization keeps those exact maps.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial
namespace CategoryTheory.SimplicialEnrichment.FixedObjects
variable {O : Type u}

/-- The complete original fixed-label scalar category diagram map. -/
def scalarLabelDiagramMap {C D : FixedObjects O} (F : C ⟶ D) : scalarCatDiagram C ⟶ scalarCatDiagram D where
  app q := scalarCatMap F q
  naturality {q r} f := by
    apply Cat.ext
    exact CategoryTheory.Functor.hext (fun _ => rfl) (fun x y a =>
      heq_of_eq (scalarFunctor_operator F f x y a))

/-- The full original labelled scalar nerve diagram map uses the SAME original enriched functor. -/
def scalarLabelNerveMap {C D : FixedObjects O} (F : C ⟶ D) : scalarLabelNerveDiagram C ⟶ scalarLabelNerveDiagram D :=
  Functor.whiskerRight (scalarLabelDiagramMap F) nerveFunctor

/-- The SAME entire original labelled scalar base map. -/
def scalarLabelBaseMap {C D : FixedObjects O} (F : C ⟶ D) : scalarLabelBase C ⟶ scalarLabelBase D :=
  SSet.simplicialDiagonalFunctor.map (scalarLabelNerveMap F)

/-- Original scalar wrappers and labels retain the SAME complete ordinal operator. -/
lemma labelsToScalar_operator (C : FixedObjects O) {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r) :
    ((scalarCatDiagram C).map f).toFunctor ⋙ labelsToScalar C r =
      labelsToScalar C q ⋙ SSet.scalarOperator (C := C.val) f := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
  intro x y a
  exact HEq.rfl

/-- The SAME original label-to-canonical scalar comparison is a whole nerve diagram map. -/
def labelsToCanonicalNerve (C : FixedObjects O) :
    scalarLabelNerveDiagram C ⟶ SSet.ScalarUnderCategory.baseNerveDiagram C.val where
  app q := nerveMap (labelsToScalar C q)
  naturality {q r} f := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro w
    exact (Functor.assoc w (((scalarCatDiagram C).map f).toFunctor) (labelsToScalar C r)).trans
      ((congrArg (fun F => w ⋙ F) (labelsToScalar_operator C f)).trans
        (Functor.assoc w (labelsToScalar C q) (SSet.scalarOperator (C := C.val) f)).symm)

/-- The SAME actual original fixed-label base coordinates compare weakly to the original canonical base diagonal. -/
def labelBaseToCanonical (C : FixedObjects O) : scalarLabelBase C ⟶ SSet.ScalarUnderCategory.baseTotal C.val :=
  SSet.simplicialDiagonalFunctor.map (labelsToCanonicalNerve C)

/-- Every full original scalar label-coordinate comparison is genuinely nerve weak. -/
theorem labelsToCanonicalNerve_weak (C : FixedObjects O) (q : SimplexCategoryᵒᵖ) :
    SSet.realizationWeakEquivalences ((labelsToCanonicalNerve C).app q) :=
  CategoryTheory.nerveMap_mem_realizationWeakEquivalences_of_isEquivalence (labelsToScalar C q)

/-- The SAME actual full original base coordinate comparison is weak by the genuine native diagonal theorem. -/
theorem labelBaseToCanonical_weak (C : FixedObjects O) :
    SSet.realizationWeakEquivalences (labelBaseToCanonical C) :=
  SSet.simplicialDiagonal_map_mem_realizationWeakEquivalences (labelsToCanonicalNerve C)
    (fun n => labelsToCanonicalNerve_weak C (op ⦋n⦌))

/-- Every original fixed-label map retains the whole original scalar Hom map after canonical scalar wrapping. -/
lemma labelsToScalar_natural {C D : FixedObjects O} (F : C ⟶ D) (q : SimplexCategoryᵒᵖ) :
    (scalarCatMap F q).toFunctor ⋙ labelsToScalar D q = labelsToScalar C q ⋙ SSet.scalarFunctor F.val q := by
  refine CategoryTheory.Functor.hext (fun x => congrArg (SSet.ScalarObject.mk (Δ := q)) (map_vertex F x).symm) ?_
  intro x y a
  have helement : ∀ {X Y : SSet.{u}} (h : X = Y) (q : SimplexCategoryᵒᵖ) (a : X.obj q),
      HEq ((eqToHom h : X ⟶ Y).app q a) a := by
    intro X Y h q a
    subst Y
    rfl
  change HEq ((homMap F x y).app q a) ((F.val.map (vertex C x) (vertex C y)).app q a)
  exact helement _ q _

/-- The SAME original labelled-base map retains the actual original canonical base map and both coordinate
comparisons. -/
theorem scalarLabelBaseMap_natural {C D : FixedObjects O} (F : C ⟶ D) :
    scalarLabelBaseMap F ≫ labelBaseToCanonical D =
      labelBaseToCanonical C ≫ SSet.ScalarUnderCategory.baseMap F.val := by
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro w
  exact (Functor.assoc w (scalarCatMap F q).toFunctor (labelsToScalar D q)).trans
    ((congrArg (fun G => w ⋙ G) (labelsToScalar_natural F q)).trans
      (Functor.assoc w (labelsToScalar C q) (SSet.scalarFunctor F.val q)).symm)

end CategoryTheory.SimplicialEnrichment.FixedObjects
