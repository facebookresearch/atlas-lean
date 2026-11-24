/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.RelativeCellComplex.FinitePartialAttachmentComposition

/-!
# Independent category universes and distinct original finite cells

The full insertion pushout works with independent category object,
Hom and occurrence universes. A concrete Type-valued attachment keeps
two occurrences of the same empty-to-point cell distinct. Its full
descender labels those actual points differently, proving that the
finite construction retains occurrence multiplicity.
-/

noncomputable section
universe u v w
open CategoryTheory Limits HomotopicalAlgebra Classical

namespace MathlibExtTest.OriginalFiniteAttachmentUniverseFixtures

/-- The same full original insertion square retains independent category and occurrence universes. -/
theorem independentInsertionPushout {C : Type u} [Category.{v} C]
    [HasColimitsOfSize.{w,w} C] {I : Type w} [DecidableEq I]
    {A B : I → C} (g : ∀ i, A i ⟶ B i) {X : C} (a : ∀ i, A i ⟶ X)
    (s : Finset I) (i : I) (hi : i ∉ s) :
    IsPushout (a i ≫ FinitePartialAttachment.root g a s) (g i)
      (FinitePartialAttachment.insertMap g a s i) (FinitePartialAttachment.newCell g a s i) :=
  FinitePartialAttachment.insert_isPushout g a s i hi

/-- Two distinct occurrences use the same full original empty-to-point Type map. -/
def pointCells : ∀ _i : Fin 2, (PEmpty.{u+1} : Type u) ⟶ PUnit.{u+1} :=
  fun _ => ↾PEmpty.elim

/-- Each complete original empty boundary attaches to the same genuinely empty root. -/
def pointAttaching : ∀ _i : Fin 2, (PEmpty.{u+1} : Type u) ⟶ PEmpty.{u+1} :=
  fun _ => 𝟙 _

/-- The actual selected original family retains both individual occurrences. -/
abbrev bothOccurrences : Finset (Fin 2) := {0,1}

/-- The same full original first selected occurrence. -/
abbrev firstOccurrence : bothOccurrences := ⟨0, by simp only [bothOccurrences, Finset.mem_insert,
  Finset.mem_singleton, true_or]⟩

/-- The same full original second selected occurrence. -/
abbrev secondOccurrence : bothOccurrences := ⟨1, by simp only [bothOccurrences, Finset.mem_insert,
  Finset.mem_singleton, or_true]⟩

/-- The actual original finite pushout contains the two full selected empty-to-point cells. -/
abbrev twoPointAttachment : Type u :=
  FinitePartialAttachment.object pointCells.{u} pointAttaching.{u} bothOccurrences

/-- The same full original first point cell in the actual finite attachment. -/
abbrev firstCell : PUnit.{u+1} ⟶ twoPointAttachment.{u} :=
  FinitePartialAttachment.cell pointCells.{u} pointAttaching.{u} bothOccurrences firstOccurrence

/-- The same full original second point cell in the actual finite attachment. -/
abbrev secondCell : PUnit.{u+1} ⟶ twoPointAttachment.{u} :=
  FinitePartialAttachment.cell pointCells.{u} pointAttaching.{u} bothOccurrences secondOccurrence

/-- The full original descender assigns every actual selected cell its own original occurrence label. -/
def labels : twoPointAttachment.{u} ⟶ ULift.{u} (Fin 2) :=
  FinitePartialAttachment.desc pointCells.{u} pointAttaching.{u} bothOccurrences (↾PEmpty.elim)
    (fun i => ↾fun _ => ULift.up i.1)
    (fun _i => by
      apply ConcreteCategory.hom_ext
      intro x
      exact PEmpty.elim x)

/-- The entire original first cell reads back its same original first label. -/
theorem firstLabel : labels.{u} (firstCell.{u} PUnit.unit) = ULift.up (0 : Fin 2) :=
  congrArg (fun h : PUnit.{u+1} ⟶ ULift.{u} (Fin 2) => h PUnit.unit)
    (FinitePartialAttachment.cell_desc pointCells.{u} pointAttaching.{u} bothOccurrences _ _ _ firstOccurrence)

/-- The entire original second cell reads back its same original second label. -/
theorem secondLabel : labels.{u} (secondCell.{u} PUnit.unit) = ULift.up (1 : Fin 2) :=
  congrArg (fun h : PUnit.{u+1} ⟶ ULift.{u} (Fin 2) => h PUnit.unit)
    (FinitePartialAttachment.cell_desc pointCells.{u} pointAttaching.{u} bothOccurrences _ _ _ secondOccurrence)

/-- The same actual two original cell points are distinct; occurrence multiplicity is not collapsed. -/
theorem distinctOriginalCells :
    firstCell.{u} PUnit.unit ≠ secondCell.{u} PUnit.unit := by
  intro he
  have h : ULift.up (0 : Fin 2) = ULift.up (1 : Fin 2) :=
    firstLabel.symm.trans ((congrArg labels he).trans secondLabel)
  have h' : (0 : Fin 2) = 1 := congrArg ULift.down h
  exact (by decide : (0 : Fin 2) ≠ 1) h'

end MathlibExtTest.OriginalFiniteAttachmentUniverseFixtures
