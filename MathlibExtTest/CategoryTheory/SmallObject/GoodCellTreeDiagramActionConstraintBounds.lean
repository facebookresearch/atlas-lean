/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.DiagramActionConstraintBounds
public import MathlibExtTest.CategoryTheory.Functor.OriginalArrowBounds
public import Mathlib.CategoryTheory.WithTerminal.Basic

/-!
# Actual original pair labels with coincident composites

An infinite original category retains the two original parallel arrows at
Nat label seven. Their pairs with the same terminal arrow are different,
although their actual composites and their constant-target actions coincide.
Empty and identity-only original indices keep the full native constraint types.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w uD vD

open CategoryTheory CategoryTheory.Limits
  CategoryTheory.SmallObject.DiagramActionConstraintBounds

namespace DiagramActionConstraintBoundExamples

section IndependentUniverses

variable (D : Type uD) [Category.{vD} D]
  (chi : Cardinal.{w}) [Fact chi.IsRegular]

theorem independentOriginalBounds (hArrow : HasCardinalLT (Arrow D) chi) :
    HasCardinalLT D chi ∧ HasCardinalLT (ComposableArrows D 2) chi ∧
      ∀ e : D, HasCardinalLT (Over e) chi ∧ HasCardinalLT (IncomingPair e) chi ∧
        HasCardinalLT (Constraint e) chi := allBounds chi hArrow

theorem independentIncomingFunction (e : D) :
    (fun a : Over e => (incomingArrow e a).hom) = (fun a : Over e => a.hom) :=
  incomingArrow_hom_function e

theorem independentNativePairFunction (e : D) :
    (fun p : IncomingPair e => nativePairArrows (pairToNative e p)) = pairArrows e :=
  pairToNative_arrow_function e

end IndependentUniverses

/-- Every original natural number has its nonthin terminal-extended parallel pair. -/
abbrev OriginalIndex := Discrete ℕ × WithTerminal WalkingParallelPair

instance originalIndexInfinite : Infinite OriginalIndex :=
  Infinite.of_injective
    (fun n : ℕ => (Discrete.mk n, WithTerminal.incl.obj WalkingParallelPair.zero))
    (fun _ _ h => congrArg (fun d : OriginalIndex => d.1.as) h)

/-- The original zero object at Nat label seven. -/
def sourceSeven : OriginalIndex :=
  (Discrete.mk 7, WithTerminal.incl.obj WalkingParallelPair.zero)

/-- The original one object at that same Nat label. -/
def middleSeven : OriginalIndex :=
  (Discrete.mk 7, WithTerminal.incl.obj WalkingParallelPair.one)

/-- The actual terminal object at the original Nat label seven. -/
def targetSeven : OriginalIndex := (Discrete.mk 7, WithTerminal.star)

/-- The actual original left parallel arrow, with its unchanged discrete component. -/
def firstArrow : sourceSeven ⟶ middleSeven :=
  (𝟙 (Discrete.mk 7), WithTerminal.incl.map WalkingParallelPairHom.left)

/-- The actual original right parallel arrow, with those same endpoints. -/
def secondArrow : sourceSeven ⟶ middleSeven :=
  (𝟙 (Discrete.mk 7), WithTerminal.incl.map WalkingParallelPairHom.right)

/-- The common original arrow from the middle object to its terminal object. -/
def lastArrow : middleSeven ⟶ targetSeven :=
  (𝟙 (Discrete.mk 7), WithTerminal.homFrom WalkingParallelPair.one)

theorem firstArrow_ne_secondArrow : firstArrow ≠ secondArrow := by
  intro h
  have hh : WalkingParallelPairHom.left = WalkingParallelPairHom.right :=
    congrArg (fun g : sourceSeven ⟶ middleSeven => g.2) h
  cases hh

theorem originalArrowValuesDifferent : Arrow.mk firstArrow ≠ Arrow.mk secondArrow := by
  intro h
  exact firstArrow_ne_secondArrow ((Arrow.mk_inj sourceSeven middleSeven).1 h)

/-- The native incoming over object of the original left arrow. -/
def firstIncoming : Over middleSeven := Over.mk firstArrow

/-- The native incoming over object of the original right arrow. -/
def secondIncoming : Over middleSeven := Over.mk secondArrow

theorem originalIncomingLabelsDifferent : firstIncoming ≠ secondIncoming := by
  intro h
  exact originalArrowValuesDifferent (congrArg (incomingArrow middleSeven) h)

theorem incomingSourceSeven : firstIncoming.left = sourceSeven := rfl

theorem incomingFirstHom : firstIncoming.hom = firstArrow := rfl

theorem incomingSecondHom : secondIncoming.hom = secondArrow := rfl

/-- The original left arrow paired with the common terminal arrow. -/
def firstPair : IncomingPair targetSeven := ⟨Over.mk lastArrow, Over.mk firstArrow⟩

/-- The original right arrow paired with that same terminal arrow. -/
def secondPair : IncomingPair targetSeven := ⟨Over.mk lastArrow, Over.mk secondArrow⟩

theorem firstPairSource : firstPair.2.left = sourceSeven := rfl

theorem firstPairMiddle : firstPair.1.left = middleSeven := rfl

theorem firstPairFirstHom : firstPair.2.hom = firstArrow := rfl

theorem firstPairSecondHom : firstPair.1.hom = lastArrow := rfl

theorem secondPairFirstHom : secondPair.2.hom = secondArrow := rfl

theorem secondPairSecondHom : secondPair.1.hom = lastArrow := rfl

theorem firstPairArrowValues :
    pairArrows targetSeven firstPair = (Arrow.mk firstArrow, Arrow.mk lastArrow) := rfl

theorem secondPairArrowValues :
    pairArrows targetSeven secondPair = (Arrow.mk secondArrow, Arrow.mk lastArrow) := rfl

theorem originalPairLabelsDifferent : firstPair ≠ secondPair := by
  intro h
  have hh := congrArg Prod.fst (congrArg (pairArrows targetSeven) h)
  exact originalArrowValuesDifferent hh

/-- The native two-arrow functor of the entire original left incoming pair. -/
def firstNativePair : ComposableArrows OriginalIndex 2 := pairToNative targetSeven firstPair

/-- The native two-arrow functor of the entire original right incoming pair. -/
def secondNativePair : ComposableArrows OriginalIndex 2 := pairToNative targetSeven secondPair

theorem firstNativePairActual : firstNativePair = ComposableArrows.mk₂ firstArrow lastArrow := rfl

theorem secondNativePairActual :
    secondNativePair = ComposableArrows.mk₂ secondArrow lastArrow := rfl

theorem firstNativePairArrows :
    nativePairArrows firstNativePair = (Arrow.mk firstArrow, Arrow.mk lastArrow) :=
  nativePairArrows_mk firstArrow lastArrow

theorem secondNativePairArrows :
    nativePairArrows secondNativePair = (Arrow.mk secondArrow, Arrow.mk lastArrow) :=
  nativePairArrows_mk secondArrow lastArrow

theorem nativePairLabelsDifferent : firstNativePair ≠ secondNativePair := by
  intro h
  exact originalPairLabelsDifferent (pairToNativeInjective targetSeven h)

/-- The actual composites coincide in this original category. -/
theorem originalCompositesEqual : firstArrow ≫ lastArrow = secondArrow ≫ lastArrow := rfl

theorem originalCompositeArrowValuesEqual :
    Arrow.mk (firstArrow ≫ lastArrow) = Arrow.mk (secondArrow ≫ lastArrow) :=
  congrArg (fun g : sourceSeven ⟶ targetSeven => Arrow.mk g) originalCompositesEqual

theorem nativeCompositesEqual : firstNativePair.map' 0 2 = secondNativePair.map' 0 2 := by
  change firstArrow ≫ lastArrow = secondArrow ≫ lastArrow
  exact originalCompositesEqual

/-- Both original parallel arrows also have coincident actions in the actual target functor. -/
abbrev constantTarget : OriginalIndex ⥤ Type := (Functor.const OriginalIndex).obj PUnit.{1}

theorem constantFirstActionsEqual : constantTarget.map firstArrow = constantTarget.map secondArrow :=
  rfl

theorem constantPairActionsEqual :
    (constantTarget.map firstArrow, constantTarget.map lastArrow) =
      (constantTarget.map secondArrow, constantTarget.map lastArrow) := rfl

/-- The actual unit equality label at the original target. -/
def unitConstraint : Constraint targetSeven := .inl PUnit.unit

/-- The original identity-arrow label in the separate incoming-arrow summand. -/
def identityConstraint : Constraint targetSeven := .inr (.inl (Over.mk (𝟙 targetSeven)))

/-- The equality-family tag retaining the actual original left incoming pair. -/
def firstPairConstraint : Constraint targetSeven := .inr (.inr firstPair)

/-- The equality-family tag retaining the actual original right incoming pair. -/
def secondPairConstraint : Constraint targetSeven := .inr (.inr secondPair)

theorem pairConstraintLabelsDifferent : firstPairConstraint ≠ secondPairConstraint := by
  intro h
  exact originalPairLabelsDifferent (Sum.inr_injective (Sum.inr_injective h))

theorem unitAndIdentityLabelsDifferent : unitConstraint ≠ identityConstraint := by
  intro h
  cases h

theorem unitAndPairLabelsDifferent : unitConstraint ≠ firstPairConstraint := by
  intro h
  cases h

theorem identityAndPairLabelsDifferent : identityConstraint ≠ firstPairConstraint := by
  intro h
  have hh := Sum.inr_injective h
  cases hh

/-- The internally chosen direct rank bounds the whole infinite original constraint family. -/
theorem chosenOriginalConstraintRank :
    ∃ chi : Cardinal.{0}, chi.IsRegular ∧ Cardinal.aleph0 < chi ∧
      HasCardinalLT (Arrow OriginalIndex) chi ∧ HasCardinalLT OriginalIndex chi ∧
        HasCardinalLT (ComposableArrows OriginalIndex 2) chi ∧
          ∀ e : OriginalIndex, HasCardinalLT (Over e) chi ∧
            HasCardinalLT (IncomingPair e) chi ∧ HasCardinalLT (Constraint e) chi := by
  obtain ⟨chi, hRegular, hUncountable, _, hArrow, _, _⟩ :=
    Functor.OriginalArrowBounds.existsRegularBoundAbove (D := OriginalIndex) 0
  let : Fact chi.IsRegular := ⟨hRegular⟩
  obtain ⟨hObjects, hNativePairs, hIncoming⟩ := allBounds chi hArrow
  exact ⟨chi, hRegular, hUncountable, hArrow, hObjects, hNativePairs, hIncoming⟩

/-- The actual empty original ordinary index. -/
abbrev EmptyIndex := Discrete Empty

instance emptyNativePairs : IsEmpty (ComposableArrows EmptyIndex 2) where
  false p := IsEmpty.false (p.obj 0)

theorem actualEmptyOriginalBounds :
    ∃ chi : Cardinal.{0}, chi.IsRegular ∧ Cardinal.aleph0 < chi ∧
      HasCardinalLT (Arrow EmptyIndex) chi ∧ HasCardinalLT (ComposableArrows EmptyIndex 2) chi ∧
        ∀ e : EmptyIndex, HasCardinalLT (Constraint e) chi := by
  obtain ⟨chi, hRegular, hUncountable, _, hArrow, _, _⟩ :=
    Functor.OriginalArrowBounds.existsRegularBoundAbove (D := EmptyIndex) 0
  let : Fact chi.IsRegular := ⟨hRegular⟩
  exact ⟨chi, hRegular, hUncountable, hArrow, nativePairsLt chi hArrow,
    fun e => constraintLt chi hArrow e⟩

/-- An original category whose only arrow is its actual identity. -/
abbrev IdentityIndex := Discrete PUnit.{1}

/-- The specified original object of the identity-only category. -/
def identityObject : IdentityIndex := Discrete.mk PUnit.unit

/-- With no nonidentity incoming arrows, the actual identity arrow is still present. -/
theorem identityOnlyIncoming (a : Over identityObject) : a = Over.mk (𝟙 identityObject) := by
  obtain ⟨d, g, rfl⟩ := Over.mk_surjective a
  have hd : d = identityObject := Subsingleton.elim _ _
  subst d
  have hg : g = 𝟙 identityObject := Subsingleton.elim _ _
  subst g
  rfl

/-- The unit and the identity-arrow constructor are two different actual equality labels. -/
theorem identityOnlyUnitDistinct :
    (.inl PUnit.unit : Constraint identityObject) ≠ .inr (.inl (Over.mk (𝟙 identityObject))) := by
  intro h
  cases h

theorem identityPairRetained :
    pairToNative identityObject ⟨Over.mk (𝟙 identityObject), Over.mk (𝟙 identityObject)⟩ =
      ComposableArrows.mk₂ (𝟙 identityObject) (𝟙 identityObject) := rfl

-- The full earlier original Arrow versus representative Arrow client is an exact prior input.
#check @OriginalArrowBoundExamples.concreteOriginalArrowBoundary

end DiagramActionConstraintBoundExamples
