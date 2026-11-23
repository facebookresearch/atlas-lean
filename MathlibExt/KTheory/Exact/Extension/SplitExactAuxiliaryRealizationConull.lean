/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.ProjectiveAuxiliaryConull
public import MathlibExt.CategoryTheory.ExactCategory.Split
public import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# The original auxiliary realization of a split exact category

The exact structure on the original category is retained. Its splitness
means that every admissible short complex admits a splitting. A splitting
of each actual row produces a unit-to-row arrow in the original auxiliary
category. The existing native diagonal theorem gives trivial positive
homotopy groups at the unit, and actual paths and the native-to-ordinary
isomorphism transport that conclusion to every original realized point.

Object and morphism universes are independent. Splitness of the original
admissible rows is the extra input to the abstract construction.
-/

public section

universe u v w

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.ExactCategory CategoryTheory.Limits
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory Simplicial Topology

namespace AlgebraicKTheory.AuxiliaryExtension

attribute [local instance] AlgebraicKTheory.FixedTargetExtension.leftSumAction

section OriginalExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

private def originalRowSplitting
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting)
    {X : C} (E : FixedTargetExtension C X) : E.toExtension.row.Splitting := by
  have hE : IsAdmissibleExact E.toExtension.row := E.admissible
  exact Classical.choice (hSplit E.toExtension.row hE)

private def originalUnitToRow
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting)
    {X : C} (E : FixedTargetExtension C X) :
    auxiliaryUnit C X ⟶ (⟨E⟩ : Auxiliary C X) :=
  CategoryTheory.MonoidalActionCategory.Hom.mk
    (splitUnitRaw E (originalRowSplitting hSplit E))

private def originalUnitToObject
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting)
    (X : C) (a : Auxiliary C X) : auxiliaryUnit C X ⟶ a :=
  originalUnitToRow hSplit a.of

private def originalUnitEdge
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting)
    (X : C) (a : Auxiliary C X) :
    (nerve (Auxiliary C X)).Edge
      (nerveEquiv.symm (auxiliaryUnit C X)) (nerveEquiv.symm a) :=
  CategoryTheory.nerve.edgeMk (originalUnitToObject hSplit X a)

private def originalUnitPath
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting)
    (X : C) (a : Auxiliary C X) :
    Path (SSet.realizedVertex (X := nerve (Auxiliary C X))
      (nerveEquiv.symm (auxiliaryUnit C X)))
      (SSet.realizedVertex (X := nerve (Auxiliary C X)) (nerveEquiv.symm a)) :=
  TopCat.pathEquiv (SSet.realizedEdgePath (originalUnitEdge hSplit X a))

private theorem originalAuxiliary_piZero_subsingleton
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting)
    (X : C) : Subsingleton (SSet.π₀ (nerve (Auxiliary C X))) := by
  constructor
  intro a b
  obtain ⟨p, rfl⟩ := SSet.π₀.mk_surjective a
  obtain ⟨q, rfl⟩ := SSet.π₀.mk_surjective b
  obtain ⟨E, rfl⟩ := (nerveEquiv (C := Auxiliary C X)).symm.surjective p
  obtain ⟨F, rfl⟩ := (nerveEquiv (C := Auxiliary C X)).symm.surjective q
  exact (SSet.π₀.sound (originalUnitEdge hSplit X E)).symm.trans
    (SSet.π₀.sound (originalUnitEdge hSplit X F))

private theorem originalAuxiliary_nerve_isConnected
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting)
    (X : C) : (nerve (Auxiliary C X)).IsConnected := by
  exact (SSet.isConnected_iff _).mpr
    ⟨originalAuxiliary_piZero_subsingleton hSplit X,
      ⟨nerveEquiv.symm (auxiliaryUnit C X)⟩⟩

/-- Splitness of the original admissible rows gives path connectedness of
the same ordinary auxiliary realization, including all nonvertex points. -/
theorem splitExactAuxiliary_realization_pathConnected
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting)
    (X : C) : PathConnectedSpace (SSet.toTop.obj (nerve (Auxiliary C X))) := by
  exact @SSet.pathConnectedSpace_realization_of_isConnected _
    (originalAuxiliary_nerve_isConnected hSplit X)

private theorem originalAuxiliaryCGWH_pathConnected
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting)
    (X : C) : PathConnectedSpace (auxiliaryCGWH.{w} C X) := by
  let d := auxiliaryCGWHToTopIso.{w} (C := C) (X := X)
  exact @Homeomorph.pathConnectedSpace _ _ _ _
    (splitExactAuxiliary_realization_pathConnected hSplit X)
    (TopCat.homeoOfIso d.symm)

private theorem originalAuxiliary_positiveGroup_eq_one_at
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting)
    (X : C) (n : ℕ) (y : auxiliaryCGWH.{w} C X)
    (a : HomotopyGroup.Pi (n + 1) (auxiliaryCGWH.{w} C X) y) : a = 1 := by
  let Y := auxiliaryCGWH.{w} C X
  let H := auxiliaryWeakHSpaceData.{w} (C := C) (X := X)
  have hConn : PathConnectedSpace Y := originalAuxiliaryCGWH_pathConnected.{u, v, w} hSplit X
  let p : Path H.e y := Classical.choice (@PathConnectedSpace.joined _ _ hConn H.e y)
  let E : HomotopyGroup.Pi (n + 1) Y H.e ≃* HomotopyGroup.Pi (n + 1) Y y :=
    TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) p
  have hOne : E.symm a = 1 :=
    auxiliary_positiveGroup_eq_one.{w} (C := C) (X := X) n (E.symm a)
  have h1 : a = E (E.symm a) := (E.apply_symm_apply a).symm
  have h2 : E (E.symm a) = E 1 := congrArg E hOne
  have h3 : E 1 = 1 := E.map_one
  exact h1.trans (h2.trans h3)

private theorem originalAuxiliary_positiveGroup_subsingleton_at
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting)
    (X : C) (n : ℕ) (y : auxiliaryCGWH.{w} C X) :
    Subsingleton (HomotopyGroup.Pi (n + 1) (auxiliaryCGWH.{w} C X) y) := by
  constructor
  intro a b
  exact (originalAuxiliary_positiveGroup_eq_one_at.{u, v, w} hSplit X n y a).trans
    (originalAuxiliary_positiveGroup_eq_one_at.{u, v, w} hSplit X n y b).symm

/-- Every positive homotopy group at every point of the original ordinary
realization is trivial; its topology and given quotient object are retained. -/
theorem splitExactAuxiliary_realization_positiveGroup_subsingleton_at
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting)
    (X : C) (n : ℕ) (y : SSet.toTop.obj (nerve (Auxiliary C X))) :
    Subsingleton (HomotopyGroup.Pi (n + 1)
      (SSet.toTop.obj (nerve (Auxiliary C X))) y) := by
  let Y := auxiliaryCGWH.{max u v} C X
  let Z : TopCat.{max u v} := TopCat.of Y
  let d : Z ≅ SSet.toTop.obj (nerve (Auxiliary C X)) :=
    auxiliaryCGWHToTopIso.{max u v} (C := C) (X := X)
  have h : ∀ z : Z, Subsingleton (HomotopyGroup.Pi (n + 1) Z z) :=
    fun z => originalAuxiliary_positiveGroup_subsingleton_at.{u, v, max u v} hSplit X n z
  exact TopCat.positiveGroup_subsingleton_of_iso n d h y

/-- The literal terminal map of the original auxiliary TopCat realization
is weak for an arbitrary split exact category, with independent universes. -/
theorem splitExactAuxiliary_realization_conull
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting)
    (X : C) : TopCat.weakHomotopyEquivalences
      (terminal.from (SSet.toTop.obj (nerve (Auxiliary C X)))) := by
  let B : TopCat.{max u v} := SSet.toTop.obj (nerve (Auxiliary C X))
  let e : (⊤_ TopCat.{max u v}) ≅ TopCat.of PUnit.{max u v + 1} :=
    TopCat.terminalIsoPUnit
  have hTarget : Subsingleton (⊤_ TopCat.{max u v}) := by
    constructor
    intro a b
    apply (TopCat.homeoOfIso e).injective
    exact Subsingleton.elim _ _
  have hConn : PathConnectedSpace B := splitExactAuxiliary_realization_pathConnected hSplit X
  have hPositive : ∀ (n : ℕ) (x : B),
      Subsingleton (HomotopyGroup.Pi (n + 1) B x) :=
    fun n x => splitExactAuxiliary_realization_positiveGroup_subsingleton_at hSplit X n x
  exact TopCat.map_mem_weakHomotopyEquivalences_to_singleton
    (terminal.from B) hTarget hConn hPositive

/-- All three conclusions of the abstract split-exact auxiliary assertion,
on the original realization and its exact terminal map. -/
theorem splitExactAuxiliary_realization_full
    (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting)
    (X : C) :
    PathConnectedSpace (SSet.toTop.obj (nerve (Auxiliary C X))) ∧
      (∀ (n : ℕ) (y : SSet.toTop.obj (nerve (Auxiliary C X))),
        Subsingleton (HomotopyGroup.Pi (n + 1)
          (SSet.toTop.obj (nerve (Auxiliary C X))) y)) ∧
      TopCat.weakHomotopyEquivalences
        (terminal.from (SSet.toTop.obj (nerve (Auxiliary C X)))) := by
  exact ⟨splitExactAuxiliary_realization_pathConnected hSplit X,
    splitExactAuxiliary_realization_positiveGroup_subsingleton_at hSplit X,
    splitExactAuxiliary_realization_conull hSplit X⟩

end OriginalExactStructure

section CanonicalSplitStructure

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- For the canonical split exact structure, its actual admissibility
predicate derives the splitness input and hence the full original result. -/
theorem canonicalSplitAuxiliary_realization_full (X : C) :
    letI : ExactCategory C := CategoryTheory.ExactCategory.splitExactCategory
    PathConnectedSpace (SSet.toTop.obj (nerve (Auxiliary C X))) ∧
      (∀ (n : ℕ) (y : SSet.toTop.obj (nerve (Auxiliary C X))),
        Subsingleton (HomotopyGroup.Pi (n + 1)
          (SSet.toTop.obj (nerve (Auxiliary C X))) y)) ∧
      TopCat.weakHomotopyEquivalences
        (terminal.from (SSet.toTop.obj (nerve (Auxiliary C X)))) := by
  let : ExactCategory C := CategoryTheory.ExactCategory.splitExactCategory
  have hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting := by
    intro S hS
    change Nonempty S.Splitting at hS
    exact hS
  exact splitExactAuxiliary_realization_full hSplit X

end CanonicalSplitStructure

end AlgebraicKTheory.AuxiliaryExtension

end
