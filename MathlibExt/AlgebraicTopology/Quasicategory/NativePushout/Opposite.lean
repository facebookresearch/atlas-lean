/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Quasicategory.NativePushout.Basic
public import MathlibExt.AlgebraicTopology.Quasicategory.NativePullback.Basic
public import MathlibExt.AlgebraicTopology.Quasicategory.ColimitCone

/-!
# Opposite native pullback and pushout squares

The original under-slice restriction and its reversed over-slice restriction
are isomorphic arrows. The actual shape inclusions and every standard boundary
are retained under reversal. This proves the equivalence of the independently
defined native pullback and pushout conditions on the reversed whole squares.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open CategoryTheory
open scoped Simplicial

universe u


namespace SSet.NativePullback

/-- The original whole native pullback condition is invariant under an ambient isomorphism. -/
theorem isPullbackSquare_iff_of_iso {X Y : SSet.{u}} (q : squareShape.{u} ⟶ X)
    (e : X ≅ Y) : IsPullbackSquare q ↔ IsPullbackSquare (q ≫ e.hom) := by
  unfold IsPullbackSquare
  apply forall_congr'
  intro n
  exact sliceOver.hasLiftingProperty_restrictionAmbient_iff q cospanInclusion e (boundary n).ι

end SSet.NativePullback

namespace SSet.NativePushout

/-- The actual pullback diamond maps isomorphically to the opposite pushout diamond. -/
def pullbackToOppositeSquareIso : NativePullback.squareShape.{u} ≅ squareShape.{u}.op :=
  opEquivalence.unitIso.app NativePullback.squareShape ≪≫ opFunctor.mapIso squareOppositeIso

/-- The actual cospan maps isomorphically to the opposite walking span. -/
def cospanToOppositeSpanIso : NativePullback.cospanShape.{u} ≅ spanShape.{u}.op :=
  opEquivalence.unitIso.app NativePullback.cospanShape ≪≫ opFunctor.mapIso spanOppositeIso

/-- The two original shape inclusions commute through the full opposite comparisons. -/
@[reassoc]
theorem cospanInclusion_comp_pullbackToOppositeSquareIso_hom :
    NativePullback.cospanInclusion.{u} ≫ pullbackToOppositeSquareIso.hom =
      cospanToOppositeSpanIso.hom ≫ opFunctor.map spanInclusion := by
  have hu : (opEquivalence.unitIso.app NativePullback.cospanShape).hom ≫
        opFunctor.map (opFunctor.map NativePullback.cospanInclusion) =
      NativePullback.cospanInclusion ≫
        (opEquivalence.unitIso.app NativePullback.squareShape).hom :=
    opEquivalence.unitIso.hom.naturality NativePullback.cospanInclusion
  have hi := congrArg opFunctor.map op_cospanInclusion_comp_squareOppositeIso_hom
  simp only [CategoryTheory.Functor.map_comp] at hi
  let uD : NativePullback.squareShape ⟶ NativePullback.squareShape.op.op :=
    (opEquivalence.unitIso.app NativePullback.squareShape).hom
  let uC : NativePullback.cospanShape ⟶ NativePullback.cospanShape.op.op :=
    (opEquivalence.unitIso.app NativePullback.cospanShape).hom
  let d : NativePullback.squareShape.op.op ⟶ squareShape.op :=
    opFunctor.map squareOppositeIso.hom
  let c : NativePullback.cospanShape.op.op ⟶ spanShape.op :=
    opFunctor.map spanOppositeIso.hom
  let i : spanShape.op ⟶ squareShape.op := opFunctor.map spanInclusion
  let j : NativePullback.cospanShape.op.op ⟶ NativePullback.squareShape.op.op :=
    opFunctor.map (opFunctor.map NativePullback.cospanInclusion)
  have hu' : uC ≫ j = NativePullback.cospanInclusion ≫ uD := hu
  have hi' : j ≫ d = c ≫ i := hi
  change NativePullback.cospanInclusion ≫ (uD ≫ d) = (uC ≫ c) ≫ i
  rw [← Category.assoc, ← hu', Category.assoc, hi', ← Category.assoc]

variable {X : SSet.{u}}

/-- The reversed entire original pushout square, on the actual native pullback shape. -/
def oppositeSquare (q : squareShape.{u} ⟶ X) : NativePullback.squareShape.{u} ⟶ X.op :=
  pullbackToOppositeSquareIso.hom ≫ opFunctor.map q

/-- Reversal of the whole original square is natural in its ambient simplicial map. -/
theorem oppositeSquare_comp {Y : SSet.{u}} (q : squareShape.{u} ⟶ X) (f : X ⟶ Y) :
    oppositeSquare (q ≫ f) = oppositeSquare q ≫ opFunctor.map f := by
  unfold oppositeSquare
  rw [CategoryTheory.Functor.map_comp, Category.assoc]

/-- Native pushout is native pullback of the reversed whole original square. -/
theorem isPushoutSquare_iff_isPullbackSquare_opposite (q : squareShape.{u} ⟶ X) :
    IsPushoutSquare q ↔ NativePullback.IsPullbackSquare (oppositeSquare q) := by
  unfold IsPushoutSquare NativePullback.IsPullbackSquare
  apply forall_congr'
  intro n
  calc
    HasLiftingProperty (boundary n).ι (sliceUnder.restrict X q spanInclusion) ↔
        HasLiftingProperty (boundary n).ι
          (opFunctor.map (sliceUnder.restrict X q spanInclusion)) :=
      (hasLiftingProperty_boundary_op_iff n (sliceUnder.restrict X q spanInclusion)).symm
    _ ↔ HasLiftingProperty (boundary n).ι
        (sliceOver.restrict X.op (opFunctor.map q) (opFunctor.map spanInclusion)) :=
      HasLiftingProperty.iff_of_arrow_iso_right (boundary n).ι
        (sliceUnderOppositeRestrictionArrowIso X q spanInclusion)
    _ ↔ HasLiftingProperty (boundary n).ι
        (sliceOver.restrict X.op (oppositeSquare q) NativePullback.cospanInclusion) :=
      sliceOver.hasLiftingProperty_restrictionIndex_iff X.op (opFunctor.map q)
        (opFunctor.map spanInclusion) NativePullback.cospanInclusion
        pullbackToOppositeSquareIso cospanToOppositeSpanIso
        cospanInclusion_comp_pullbackToOppositeSquareIso_hom (boundary n).ι

end SSet.NativePushout

namespace SSet.NativePullback

variable {X : SSet.{u}}

/-- The reversed entire original pullback square, on the actual native pushout shape. -/
def oppositeSquare (q : squareShape.{u} ⟶ X) : NativePushout.squareShape.{u} ⟶ X.op :=
  NativePushout.squareOppositeIso.inv ≫ opFunctor.map q

/-- Reversal of the entire original pullback square is natural in the ambient map. -/
theorem oppositeSquare_comp {Y : SSet.{u}} (q : squareShape.{u} ⟶ X) (f : X ⟶ Y) :
    oppositeSquare (q ≫ f) = oppositeSquare q ≫ opFunctor.map f := by
  unfold oppositeSquare
  rw [CategoryTheory.Functor.map_comp, Category.assoc]

/-- Reversing the same whole square twice recovers it through the actual opposite unit. -/
theorem oppositeSquare_oppositeSquare (q : squareShape.{u} ⟶ X) :
    NativePushout.oppositeSquare (oppositeSquare q) =
      q ≫ (opEquivalence.unitIso.app X).hom := by
  have hi : opFunctor.map NativePushout.squareOppositeIso.hom ≫
      opFunctor.map NativePushout.squareOppositeIso.inv = 𝟙 squareShape.op.op := by
    rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  let uD : squareShape ⟶ squareShape.op.op := (opEquivalence.unitIso.app squareShape).hom
  let a : squareShape.op.op ⟶ NativePushout.squareShape.op :=
    opFunctor.map NativePushout.squareOppositeIso.hom
  let b : NativePushout.squareShape.op ⟶ squareShape.op.op :=
    opFunctor.map NativePushout.squareOppositeIso.inv
  let p : squareShape.op.op ⟶ X.op.op := opFunctor.map (opFunctor.map q)
  have hab : a ≫ b = 𝟙 squareShape.op.op := hi
  have hnat : uD ≫ p = q ≫ (opEquivalence.unitIso.app X).hom :=
    opEquivalence.unitIso.hom.naturality q
  unfold NativePushout.oppositeSquare oppositeSquare
  rw [CategoryTheory.Functor.map_comp]
  change (uD ≫ a) ≫ (b ≫ p) = q ≫ (opEquivalence.unitIso.app X).hom
  rw [Category.assoc, ← Category.assoc a b p, hab, Category.id_comp]
  exact hnat

/-- Native pullback is native pushout of the reversed entire original square. -/
theorem isPullbackSquare_iff_isPushoutSquare_opposite (q : squareShape.{u} ⟶ X) :
    IsPullbackSquare q ↔ NativePushout.IsPushoutSquare (oppositeSquare q) := by
  have h := NativePushout.isPushoutSquare_iff_isPullbackSquare_opposite (oppositeSquare q)
  rw [oppositeSquare_oppositeSquare] at h
  exact (isPullbackSquare_iff_of_iso q (opEquivalence.unitIso.app X)).trans h.symm

end SSet.NativePullback
