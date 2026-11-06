/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal finite numbering of original C322 source equations and auxiliary definitions. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationEquationContextChains
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Rename the literal letters on both sides of a signed word equation. -/
def y322WordEquationMap {alphabet target : Type*} (f : alphabet → target)
    (equation : Y322WordEquation alphabet) : Y322WordEquation target :=
  ⟨equation.left.map (fun letter => (f letter.1, letter.2)),
    equation.right.map (fun letter => (f letter.1, letter.2))⟩

/-- Renaming literal letters agrees with the corresponding actual generator interpretation. -/
theorem y322EquationWordValue_map {alphabet target G : Type*} [Group G]
    (f : alphabet → target) (values : target → G) (word : List (alphabet × Bool)) :
    y322EquationWordValue values (word.map (fun letter => (f letter.1, letter.2))) =
      y322EquationWordValue (fun a => values (f a)) word := by
  unfold y322EquationWordValue
  rw [← FreeGroup.map.mk]
  have hm : (FreeGroup.lift values).comp (FreeGroup.map f) =
      FreeGroup.lift (fun a => values (f a)) := by
    apply FreeGroup.ext_hom
    intro a
    simp
  change ((FreeGroup.lift values).comp (FreeGroup.map f)) (FreeGroup.mk word) = _
  rw [hm]

/-- A letter renaming preserves every actual interpreted source equation. -/
theorem y322WordEquationMap_valid {alphabet target G : Type*} [Group G]
    (f : alphabet → target) (values : target → G) (equation : Y322WordEquation alphabet)
    (h : equation.Valid (fun a => values (f a))) :
    (y322WordEquationMap f equation).Valid values := by
  unfold Y322WordEquation.Valid y322WordEquationMap
  simp only [y322EquationWordValue_map]
  exact h

/-- Number all 73 indexed source relators before the explicitly defined auxiliary words. -/
def y322FiniteEquationSourceIndex {size : ℕ} (index : Fin (73 + size)) :
    Y322EquationSource size :=
  if h0 : index.val < 8 then .inl (.inl ⟨index.val, h0⟩)
  else if h1 : index.val < 72 then
    .inl (.inr (.inl (⟨((index.val - 8) / 8) % 8, Nat.mod_lt _ (by decide)⟩,
      ⟨(index.val - 8) % 8, Nat.mod_lt _ (by decide)⟩)))
  else if h2 : index.val = 72 then .inl (.inr (.inr ()))
  else .inr ⟨index.val - 73, by omega⟩

/-- Actual values of the finitely numbered source and acyclic auxiliary letters. -/
noncomputable def y322FiniteAuxiliaryValue {size : ℕ} (program : Y322WordProgram size) :
    Fin (8 + size) → Y322Presentation :=
  fun v => y322AuxiliaryValue program (finSumFinEquiv.symm v)

/-- Renumbering a literal source letter leaves its actual declared word value unchanged. -/
theorem y322FiniteAuxiliaryValue_number {size : ℕ} (program : Y322WordProgram size)
    (v : Y322AuxiliaryAlphabet size) :
    y322FiniteAuxiliaryValue program (finSumFinEquiv v) = y322AuxiliaryValue program v := by
  simp [y322FiniteAuxiliaryValue]

/-- The finite source family consists exactly of literal relators and acyclic definitions. -/
def y322FiniteEquationSource {size : ℕ} (program : Y322WordProgram size)
    (index : Fin (73 + size)) : Y322WordEquation (Fin (8 + size)) :=
  y322WordEquationMap finSumFinEquiv
    (y322EquationSource program (y322FiniteEquationSourceIndex index))

/-- Every finitely numbered source equation holds in the actual original C322 presentation. -/
theorem y322FiniteEquationSource_valid {size : ℕ} (program : Y322WordProgram size)
    (index : Fin (73 + size)) :
    (y322FiniteEquationSource program index).Valid (y322FiniteAuxiliaryValue program) := by
  apply y322WordEquationMap_valid
  simpa only [y322FiniteAuxiliaryValue_number] using
    y322EquationSource_valid program (y322FiniteEquationSourceIndex index)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
