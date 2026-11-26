/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Functor.OriginalArrowBounds
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# Bounds on actual original diagram constraints

The original category and its original Hom dictionary are unchanged. Incoming
arrows are native over objects. Incoming pairs retain the two actual over
objects, and native two-arrow functors retain both component Arrow values.
The cardinal premise bounds the original Arrow carrier.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w uD vD

namespace CategoryTheory.SmallObject.DiagramActionConstraintBounds

variable {D : Type uD} [Category.{vD} D]

/-- An actual incoming second arrow and an actual first arrow into its source. -/
abbrev IncomingPair (e : D) := Sigma (fun h : Over e => Over h.left)

/-- Unit, every original incoming arrow, and every original incoming pair. -/
abbrev Constraint (e : D) := PUnit.{1} ⊕ (Over e ⊕ IncomingPair e)

/-- The actual Arrow value of the original over object. -/
def incomingArrow (e : D) (a : Over e) : Arrow D := Arrow.mk a.hom

/-- Both original Arrow values, ordered first arrow then second arrow. -/
def pairArrows (e : D) (p : IncomingPair e) : Arrow D × Arrow D :=
  (Arrow.mk p.2.hom, Arrow.mk p.1.hom)

/-- Both actual component Arrow values of the native two-arrow functor. -/
def nativePairArrows (p : ComposableArrows D 2) : Arrow D × Arrow D :=
  (Arrow.mk (p.map' 0 1), Arrow.mk (p.map' 1 2))

/-- The native pair uses precisely the two original incoming Hom values. -/
def pairToNative (e : D) (p : IncomingPair e) : ComposableArrows D 2 :=
  ComposableArrows.mk₂ p.2.hom p.1.hom

theorem incomingArrowInjective (e : D) : Function.Injective (incomingArrow e) := by
  intro a b hab
  obtain ⟨d, g, rfl⟩ := Over.mk_surjective a
  obtain ⟨d', g', rfl⟩ := Over.mk_surjective b
  change Arrow.mk g = Arrow.mk g' at hab
  have hd : d = d' := congrArg (fun x : Arrow D => x.left) hab
  subst d'
  have hg : g = g' := (Arrow.mk_inj d e).1 hab
  subst g'
  rfl

theorem pairArrowsInjective (e : D) : Function.Injective (pairArrows e) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ hab
  have ha : incomingArrow e a = incomingArrow e c :=
    congrArg (fun z : Arrow D × Arrow D => z.2) hab
  have hac : a = c := incomingArrowInjective e ha
  subst c
  have hb : incomingArrow a.left b = incomingArrow a.left d :=
    congrArg (fun z : Arrow D × Arrow D => z.1) hab
  have hbd : b = d := incomingArrowInjective a.left hb
  subst d
  rfl

theorem nativePairArrowsInjective :
    Function.Injective (nativePairArrows (D := D)) := by
  intro p q hpq
  apply ComposableArrows.ext₂_of_arrow
  · exact congrArg (fun z : Arrow D × Arrow D => z.1) hpq
  · exact congrArg (fun z : Arrow D × Arrow D => z.2) hpq

theorem incomingArrow_mk {d e : D} (g : d ⟶ e) :
    incomingArrow e (Over.mk g) = Arrow.mk g := rfl

theorem pairArrows_mk {d m e : D} (g : d ⟶ m) (h : m ⟶ e) :
    pairArrows e ⟨Over.mk h, Over.mk g⟩ = (Arrow.mk g, Arrow.mk h) := rfl

theorem pairToNative_mk {d m e : D} (g : d ⟶ m) (h : m ⟶ e) :
    pairToNative e ⟨Over.mk h, Over.mk g⟩ = ComposableArrows.mk₂ g h := rfl

theorem nativePairArrows_mk {d m e : D} (g : d ⟶ m) (h : m ⟶ e) :
    nativePairArrows (ComposableArrows.mk₂ g h) = (Arrow.mk g, Arrow.mk h) := by
  dsimp [nativePairArrows]

theorem nativePairArrows_pairToNative (e : D) (p : IncomingPair e) :
    nativePairArrows (pairToNative e p) = pairArrows e p := by
  dsimp [nativePairArrows, pairToNative, pairArrows]

theorem pairToNativeInjective (e : D) : Function.Injective (pairToNative e) := by
  intro p q hpq
  apply pairArrowsInjective e
  calc
    pairArrows e p = nativePairArrows (pairToNative e p) :=
      (nativePairArrows_pairToNative e p).symm
    _ = nativePairArrows (pairToNative e q) := congrArg nativePairArrows hpq
    _ = pairArrows e q := nativePairArrows_pairToNative e q

/-- The entire incoming-arrow source and Hom functions retain their original values. -/
theorem incomingArrow_source_function (e : D) :
    (fun a : Over e => (incomingArrow e a).left) = (fun a : Over e => a.left) := rfl

theorem incomingArrow_hom_function (e : D) :
    (fun a : Over e => (incomingArrow e a).hom) = (fun a : Over e => a.hom) := rfl

/-- The entire component-Arrow function retains the same native incoming pair. -/
theorem pairToNative_arrow_function (e : D) :
    (fun p : IncomingPair e => nativePairArrows (pairToNative e p)) = pairArrows e := by
  funext p
  exact nativePairArrows_pairToNative e p

theorem incomingLt (chi : Cardinal.{w})
    (hArrow : HasCardinalLT (Arrow D) chi) (e : D) : HasCardinalLT (Over e) chi :=
  hArrow.of_injective (incomingArrow e) (incomingArrowInjective e)

theorem pairLt (chi : Cardinal.{w}) [Fact chi.IsRegular]
    (hArrow : HasCardinalLT (Arrow D) chi) (e : D) : HasCardinalLT (IncomingPair e) chi :=
  (hasCardinalLT_prod (Fact.out : chi.IsRegular).aleph0_le hArrow hArrow).of_injective
    (pairArrows e) (pairArrowsInjective e)

theorem nativePairsLt (chi : Cardinal.{w}) [Fact chi.IsRegular]
    (hArrow : HasCardinalLT (Arrow D) chi) : HasCardinalLT (ComposableArrows D 2) chi :=
  (hasCardinalLT_prod (Fact.out : chi.IsRegular).aleph0_le hArrow hArrow).of_injective
    nativePairArrows nativePairArrowsInjective

theorem constraintLt (chi : Cardinal.{w}) [Fact chi.IsRegular]
    (hArrow : HasCardinalLT (Arrow D) chi) (e : D) : HasCardinalLT (Constraint e) chi := by
  have hAleph : Cardinal.aleph0 ≤ chi := (Fact.out : chi.IsRegular).aleph0_le
  apply (hasCardinalLT_sum_iff PUnit.{1} (Over e ⊕ IncomingPair e) chi hAleph).2
  refine ⟨hasCardinalLT_of_finite PUnit.{1} chi hAleph, ?_⟩
  exact (hasCardinalLT_sum_iff (Over e) (IncomingPair e) chi hAleph).2
    ⟨incomingLt chi hArrow e, pairLt chi hArrow e⟩

/-- The same original-arrow premise bounds all actual original constraint families. -/
theorem allBounds (chi : Cardinal.{w}) [Fact chi.IsRegular]
    (hArrow : HasCardinalLT (Arrow D) chi) :
    HasCardinalLT D chi ∧ HasCardinalLT (ComposableArrows D 2) chi ∧
      ∀ e : D, HasCardinalLT (Over e) chi ∧ HasCardinalLT (IncomingPair e) chi ∧
        HasCardinalLT (Constraint e) chi :=
  ⟨hasCardinalLT_of_hasCardinalLT_arrow hArrow, nativePairsLt chi hArrow,
    fun e => ⟨incomingLt chi hArrow e, pairLt chi hArrow e, constraintLt chi hArrow e⟩⟩

end CategoryTheory.SmallObject.DiagramActionConstraintBounds
