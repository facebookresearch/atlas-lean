/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedHomGraphCoordinates
import MathlibExt.AlgebraicTopology.SimplicialSet.EquifibredDiagonalPullback

/-!
# Full original scalar-under operator target coordinates

Every original ordinal operator retains its complete base word. Its
native relative-comparison target is the same full word paired with
the entire original Hom to its selected first vertex. Native under-word
reconstruction and recovery give the whole isomorphism and both projections.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.ScalarUnderCategory

variable (C : CategoryTheory.SimplicialEnrichment.Carrier.{u})

/-- The SAME full original base-row ordinal operator. -/
def baseRowOperator {n m : SimplexCategory} (f : n ⟶ m) : baseRow C m.len ⟶ baseRow C n.len :=
  (simplicialTransposeFunctor.obj (baseNerveDiagram C)).map f.op

/-- The SAME full original scalar-under ordinal operator. -/
def underRowOperator (z : C) {n m : SimplexCategory} (f : n ⟶ m) :
    underRow C z m.len ⟶ underRow C z n.len :=
  (simplicialTransposeFunctor.obj (nerveDiagram C z)).map f.op

/-- The actual complete original operator-relative comparison. -/
def rowRelativeComparison (z : C) {n m : SimplexCategory} (f : n ⟶ m) :
    underRow C z m.len ⟶ pullback (rowProjection C z n.len) (baseRowOperator C f) :=
  EquifibredDiagonal.relativeComparison (simplicialTransposeFunctor.map (nerveProjection C z)) f

/-- Reconstruct the SAME complete restricted under-word from its original selected Hom coefficient. -/
def selectedCoefficientsToUnder (z : C) {n m : SimplexCategory} (f : n ⟶ m) :
    rowGraphCoefficients C _root_.Prod.snd z m.len (f 0) ⟶ underRow C z n.len where
  app q := ↾fun a => Under.chainFromInitialArrow ((baseRowOperator C f).app q a.1)
    (X := sourceObject C z q) a.2
  naturality q r g := by
    apply ConcreteCategory.hom_ext
    intro a
    exact (Under.chainFromInitialArrow_post ((baseRowOperator C f).app q a.1) a.2
      (scalarOperator (C := C) g)).symm

/-- The complete reconstructed original word has its SAME entire restricted base projection. -/
lemma selectedCoefficientsToUnder_projection (z : C) {n m : SimplexCategory} (f : n ⟶ m) :
    selectedCoefficientsToUnder C z f ≫ rowProjection C z n.len =
      rowGraphProjection C _root_.Prod.snd z m.len (f 0) ≫ baseRowOperator C f := by
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro a
  exact Under.chainFromInitialArrow_forget ((baseRowOperator C f).app q a.1) a.2

/-- The SAME whole original target coordinate comparison into the native relative pullback. -/
def selectedCoefficientsToRelativeTarget (z : C) {n m : SimplexCategory} (f : n ⟶ m) :
    rowGraphCoefficients C _root_.Prod.snd z m.len (f 0) ⟶
      pullback (rowProjection C z n.len) (baseRowOperator C f) :=
  pullback.lift (selectedCoefficientsToUnder C z f) (rowGraphProjection C _root_.Prod.snd z m.len (f 0))
    (selectedCoefficientsToUnder_projection C z f)

/-- Its first projection is the SAME whole restricted original under-word. -/
@[reassoc]
lemma selectedCoefficientsToRelativeTarget_fst (z : C) {n m : SimplexCategory} (f : n ⟶ m) :
    selectedCoefficientsToRelativeTarget C z f ≫ pullback.fst _ _ = selectedCoefficientsToUnder C z f :=
  pullback.lift_fst _ _ _

/-- Its second projection is the SAME complete original base word. -/
@[reassoc]
lemma selectedCoefficientsToRelativeTarget_snd (z : C) {n m : SimplexCategory} (f : n ⟶ m) :
    selectedCoefficientsToRelativeTarget C z f ≫ pullback.snd _ _ =
      rowGraphProjection C _root_.Prod.snd z m.len (f 0) := pullback.lift_snd _ _ _

/-- The entire original selected-Hom coordinate map is an actual full Iso. -/
instance selectedCoefficientsToRelativeTarget_isIso (z : C) {n m : SimplexCategory} (f : n ⟶ m) :
    IsIso (selectedCoefficientsToRelativeTarget C z f) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro q
  rw [isIso_iff_bijective]
  let P := rowProjection C z n.len
  let b := baseRowOperator C f
  let E := (CategoryTheory.evaluation SimplexCategoryᵒᵖ (Type u)).obj q
  have hpb := (IsPullback.of_hasPullback P b).map E
  have hfst := congrArg (fun g => g.app q) (selectedCoefficientsToRelativeTarget_fst C z f)
  have hsnd := congrArg (fun g => g.app q) (selectedCoefficientsToRelativeTarget_snd C z f)
  constructor
  · rintro ⟨w, h⟩ ⟨w', h'⟩ ha
    have hw : w = w' :=
      (congr($(hsnd) (⟨w, h⟩ : (rowGraphCoefficients C _root_.Prod.snd z m.len (f 0)).obj q))).symm.trans
      ((congrArg (fun t => (pullback.snd P b).app q t) ha).trans
        (congr($(hsnd) (⟨w', h'⟩ : (rowGraphCoefficients C _root_.Prod.snd z m.len (f 0)).obj q))))
    subst w'
    have he : Under.chainFromInitialArrow (b.app q w) (X := sourceObject C z q) h =
        Under.chainFromInitialArrow (b.app q w) (X := sourceObject C z q) h' :=
      (congr($(hfst) (⟨w, h⟩ : (rowGraphCoefficients C _root_.Prod.snd z m.len (f 0)).obj q))).symm.trans
        ((congrArg (fun t => (pullback.fst P b).app q t) ha).trans
          (congr($(hfst) (⟨w, h'⟩ : (rowGraphCoefficients C _root_.Prod.snd z m.len (f 0)).obj q))))
    exact congrArg (fun h => (⟨w, h⟩ : (rowGraphCoefficients C _root_.Prod.snd z m.len (f 0)).obj q))
      (Under.chainFromInitialArrow_injective (b.app q w) he)
  · intro a
    let w := (pullback.snd P b).app q a
    let U := (pullback.fst P b).app q a
    have h : U ⋙ forget C z q = b.app q w :=
      congr($(pullback.condition (f := P) (g := b)).app q a)
    let e := Under.projectionInitialArrow U (b.app q w) h
    let v : (rowGraphCoefficients C _root_.Prod.snd z m.len (f 0)).obj q := ⟨w, e⟩
    refine ⟨v, Types.ext_of_isPullback hpb ?_ ?_⟩
    · exact (congr($(hfst) v)).trans (Under.projectionChain U (b.app q w) h).symm
    · exact congr($(hsnd) v)

/-- Both whole original operations identify the SAME native operator target
with the entire original base word and original selected Hom coefficient. -/
def selectedRelativeTargetIso (z : C) {n m : SimplexCategory} (f : n ⟶ m) :
    rowGraphCoefficients C _root_.Prod.snd z m.len (f 0) ≅
      pullback (rowProjection C z n.len) (baseRowOperator C f) :=
  asIso (selectedCoefficientsToRelativeTarget C z f)

end SSet.ScalarUnderCategory
