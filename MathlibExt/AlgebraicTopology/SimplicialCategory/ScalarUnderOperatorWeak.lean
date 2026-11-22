/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarUnderRowTransport
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarUnderOperatorCoordinates

/-!
# Every original scalar-under ordinal comparison is weak

The full native relative comparison is identified with the actual
composition transport by both original pullback projections. The
first projection is the full native under-word precomposition formula,
including operators that move the first vertex. No base word or Hom
simplex is replaced or discarded.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.ScalarUnderCategory

variable (C : CategoryTheory.SimplicialEnrichment.Carrier.{u})

/-- The first native relative projection is the SAME whole original under-word operator. -/
@[reassoc]
lemma rowRelativeComparison_fst (z : C) {n m : SimplexCategory} (f : n ⟶ m) :
    rowRelativeComparison C z f ≫ pullback.fst _ _ = underRowOperator C z f :=
  pullback.lift_fst _ _ _

/-- The second native relative projection retains the SAME entire original base word. -/
@[reassoc]
lemma rowRelativeComparison_snd (z : C) {n m : SimplexCategory} (f : n ⟶ m) :
    rowRelativeComparison C z f ≫ pullback.snd _ _ = rowProjection C z m.len :=
  pullback.lift_snd _ _ _

/-- Every actual ordinal operator is the SAME complete coefficient transport
followed by the original whole restricted-word reconstruction. -/
lemma rowCoefficientsToUnder_operator (z : C) {n m : SimplexCategory} (f : n ⟶ m) :
    rowCoefficientsToUnder C z m.len ≫ underRowOperator C z f =
      rowGraphTransport C z m.len (f 0) ≫ selectedCoefficientsToUnder C z f := by
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro a
  exact Under.chainFromInitialArrow_precomp a.1 (X := sourceObject C z q) a.2
    (SimplexCategory.toCat.map f).toFunctor

/-- BOTH actual native projections identify the whole original relative
comparison with the SAME full original coefficient transport. -/
lemma rowRelativeComparison_transport_square (z : C) {n m : SimplexCategory} (f : n ⟶ m) :
    rowCoefficientsToUnder C z m.len ≫ rowRelativeComparison C z f =
      rowGraphTransport C z m.len (f 0) ≫ selectedCoefficientsToRelativeTarget C z f := by
  apply pullback.hom_ext
  · apply NatTrans.ext
    funext q
    apply ConcreteCategory.hom_ext
    intro a
    have h₁ := congrArg (fun h => h.app q) (rowRelativeComparison_fst C z f)
    have h₂ := congrArg (fun h => h.app q) (selectedCoefficientsToRelativeTarget_fst C z f)
    have h₃ := congrArg (fun h => h.app q) (rowCoefficientsToUnder_operator C z f)
    exact (congr($(h₁) ((rowCoefficientsToUnder C z m.len).app q a))).trans
      ((congr($(h₃) a)).trans
        (congr($(h₂) ((rowGraphTransport C z m.len (f 0)).app q a))).symm)
  · apply NatTrans.ext
    funext q
    apply ConcreteCategory.hom_ext
    intro a
    have h₁ := congrArg (fun h => h.app q) (rowRelativeComparison_snd C z f)
    have h₂ := congrArg (fun h => h.app q) (selectedCoefficientsToRelativeTarget_snd C z f)
    have h₃ := congrArg (fun h => h.app q) (rowCoefficientsIso_hom_projection C z m.len)
    exact (congr($(h₁) ((rowCoefficientsToUnder C z m.len).app q a))).trans
      ((congr($(h₃) a)).trans
        (congr($(h₂) ((rowGraphTransport C z m.len (f 0)).app q a))).symm)

/-- EVERY actual full original relative ordinal comparison is weak when
the SAME original component category is a groupoid, without any Kan premise. -/
theorem rowRelativeComparison_weak
    [IsGroupoid (CategoryTheory.SimplicialEnrichment.ComponentCategory.objects.{u} C)]
    (z : C) {n m : SimplexCategory} (f : n ⟶ m) :
    realizationWeakEquivalences (rowRelativeComparison C z f) := by
  let e : Arrow.mk (rowGraphTransport C z m.len (f 0)) ≅ Arrow.mk (rowRelativeComparison C z f) :=
    Arrow.isoMk' _ _ (rowCoefficientsIso C z m.len) (selectedRelativeTargetIso C z f)
      (rowRelativeComparison_transport_square C z f)
  exact (realizationWeakEquivalences.arrow_mk_iso_iff e).mp
    (rowGraphTransport_weak C z m.len (f 0))

end SSet.ScalarUnderCategory
