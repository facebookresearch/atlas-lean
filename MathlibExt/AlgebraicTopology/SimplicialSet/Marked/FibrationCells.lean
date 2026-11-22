/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.InnerCells
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EndpointCells
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CartesianCriticalCells
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CocartesianCriticalCells
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CompositionCell
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EquivalenceDetector
import Mathlib.CategoryTheory.MorphismProperty.IsSmall
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-!
# A genuinely small family of native marked fibration cells

The index consists of the original inner horns, the critical outer horns,
and three fixed cells: the endpoint, composition marking and the one Kan
marking detector. This is a countable index in Type 0, independently of
the value universe. Its corresponding morphism property is genuinely
small in that original universe. Every underlying cell is monic.
This proves index smallness and the exact testing class; source
presentability and the marked model structure are separate prerequisites.
-/

noncomputable section
universe u
open CategoryTheory MorphismProperty
open scoped Simplicial

namespace SSet.Marked

/-- The genuine countable index of the original inner, critical and three fixed marked cells. -/
abbrev FibrationCellIndex :=
  (Σ n : ℕ, {i : Fin (n + 3) // 0 < i ∧ i < Fin.last (n + 2)}) ⊕ (ℕ ⊕ Fin 3)

/-- The same cell index is countable, regardless of the simplicial value universe. -/
theorem fibrationCellIndex_countable : Countable FibrationCellIndex := inferInstance

/-- This original Type 0 index is small in every original value universe. -/
theorem fibrationCellIndex_small : Small.{u} FibrationCellIndex := small_zero _

/-- The actual original Cartesian cell at the supplied countable index. -/
def cartesianCell (s : FibrationCellIndex) : Arrow Marked.{u} :=
  match s with
  | Sum.inl a => Arrow.mk (innerCell.{u} a.1 a.2.val)
  | Sum.inr a =>
      match a with
      | Sum.inl n => Arrow.mk (cartesianCriticalCell.{u} n)
      | Sum.inr i =>
          if i = 0 then Arrow.mk cartesianEndpointCell.{u}
          else if i = 1 then Arrow.mk compositionCell.{u}
          else Arrow.mk equivalenceMarkCell.{u}

/-- The exact dual native cells use the same countable index. -/
def cocartesianCell (s : FibrationCellIndex) : Arrow Marked.{u} :=
  match s with
  | Sum.inl a => Arrow.mk (innerCell.{u} a.1 a.2.val)
  | Sum.inr a =>
      match a with
      | Sum.inl n => Arrow.mk (cocartesianCriticalCell.{u} n)
      | Sum.inr i =>
          if i = 0 then Arrow.mk cocartesianEndpointCell.{u}
          else if i = 1 then Arrow.mk compositionCell.{u}
          else Arrow.mk equivalenceMarkCell.{u}

/-- The morphism property consisting of precisely these supplied original Cartesian cells. -/
def cartesianCells : MorphismProperty Marked.{u} :=
  .ofHoms (fun s : FibrationCellIndex => (cartesianCell.{u} s).hom)

/-- The corresponding actual cocartesian testing family. -/
def cocartesianCells : MorphismProperty Marked.{u} :=
  .ofHoms (fun s : FibrationCellIndex => (cocartesianCell.{u} s).hom)

/-- The actual Cartesian testing family is small at the original value universe. -/
theorem cartesianCells_isSmall : MorphismProperty.IsSmall.{u} cartesianCells.{u} := by
  let _ : Small.{u} FibrationCellIndex := fibrationCellIndex_small
  exact MorphismProperty.isSmall_ofHoms (fun s : FibrationCellIndex => (cartesianCell.{u} s).hom)

/-- The actual cocartesian family has the same proven smallness. -/
theorem cocartesianCells_isSmall : MorphismProperty.IsSmall.{u} cocartesianCells.{u} := by
  let _ : Small.{u} FibrationCellIndex := fibrationCellIndex_small
  exact MorphismProperty.isSmall_ofHoms (fun s : FibrationCellIndex => (cocartesianCell.{u} s).hom)

/-- Every Cartesian cell is monic on its whole original marked carrier. -/
theorem cartesianCell_mono (s : FibrationCellIndex) : Mono (cartesianCell.{u} s).hom := by
  rcases s with ⟨n, i⟩ | n | i
  · exact innerCell_mono n i.val
  · exact cartesianCriticalCell_mono n
  · fin_cases i
    · change Mono cartesianEndpointCell.{u}
      let _ : Mono cartesianEndpointCell.{u}.hom :=
        inferInstanceAs (Mono (stdSimplex.δ.{u} (0 : Fin 2)))
      exact Hom.mono_of_underlying _
    · exact compositionCell_mono
    · exact equivalenceMarkCell_mono

/-- The dual native cells are also genuine monomorphisms. -/
theorem cocartesianCell_mono (s : FibrationCellIndex) : Mono (cocartesianCell.{u} s).hom := by
  rcases s with ⟨n, i⟩ | n | i
  · exact innerCell_mono n i.val
  · exact cocartesianCriticalCell_mono n
  · fin_cases i
    · change Mono cocartesianEndpointCell.{u}
      let _ : Mono cocartesianEndpointCell.{u}.hom :=
        inferInstanceAs (Mono (stdSimplex.δ.{u} (1 : Fin 2)))
      exact Hom.mono_of_underlying _
    · exact compositionCell_mono
    · exact equivalenceMarkCell_mono

/-- The small Cartesian family contains only actual marked monomorphisms. -/
theorem cartesianCells_le_monomorphisms : cartesianCells.{u} ≤ monomorphisms Marked.{u} :=
  (MorphismProperty.ofHoms_le_iff
    (fun s : FibrationCellIndex => (cartesianCell.{u} s).hom) (monomorphisms Marked.{u})).mpr
      cartesianCell_mono

/-- Every map in the dual testing family is monic. -/
theorem cocartesianCells_le_monomorphisms : cocartesianCells.{u} ≤ monomorphisms Marked.{u} :=
  (MorphismProperty.ofHoms_le_iff
    (fun s : FibrationCellIndex => (cocartesianCell.{u} s).hom) (monomorphisms Marked.{u})).mpr
      cocartesianCell_mono

/-- The Cartesian right class consists exactly of lifts against each original indexed cell. -/
theorem cartesianCells_rlp_iff_all {X Y : Marked.{u}} (p : X ⟶ Y) :
    cartesianCells.{u}.rlp p ↔ ∀ s : FibrationCellIndex,
      HasLiftingProperty (cartesianCell.{u} s).hom p := by
  constructor
  · intro hp s
    exact hp _ (MorphismProperty.ofHoms.mk s)
  · intro hp A D i hi
    obtain ⟨s⟩ := hi
    exact hp s

/-- The dual right class is tested on the same actual countable index. -/
theorem cocartesianCells_rlp_iff_all {X Y : Marked.{u}} (p : X ⟶ Y) :
    cocartesianCells.{u}.rlp p ↔ ∀ s : FibrationCellIndex,
      HasLiftingProperty (cocartesianCell.{u} s).hom p := by
  constructor
  · intro hp s
    exact hp _ (MorphismProperty.ofHoms.mk s)
  · intro hp A D i hi
    obtain ⟨s⟩ := hi
    exact hp s

/-- The actual small Cartesian right class is the five native original lifting conditions. -/
theorem cartesianCells_rlp_iff {X Y : Marked.{u}} (p : X ⟶ Y) :
    cartesianCells.{u}.rlp p ↔
      (∀ (n : ℕ) (i : Fin (n + 3)), 0 < i → i < Fin.last (n + 2) →
        HasLiftingProperty (innerCell.{u} n i) p) ∧
      (∀ n : ℕ, HasLiftingProperty (cartesianCriticalCell.{u} n) p) ∧
      HasLiftingProperty cartesianEndpointCell.{u} p ∧
      HasLiftingProperty compositionCell.{u} p ∧ HasLiftingProperty equivalenceMarkCell.{u} p := by
  rw [cartesianCells_rlp_iff_all]
  constructor
  · intro hp
    exact ⟨fun n i hi hi' => hp (.inl ⟨n, ⟨i, hi, hi'⟩⟩),
      fun n => hp (.inr (.inl n)),
      hp (.inr (.inr 0)), hp (.inr (.inr 1)), hp (.inr (.inr 2))⟩
  · rintro ⟨hi, hc, he, ht, hk⟩ s
    rcases s with ⟨n, i⟩ | n | i
    · exact hi n i.val i.property.1 i.property.2
    · exact hc n
    · fin_cases i
      · exact he
      · exact ht
      · exact hk

/-- The small cocartesian family has the exact dual five-condition right class. -/
theorem cocartesianCells_rlp_iff {X Y : Marked.{u}} (p : X ⟶ Y) :
    cocartesianCells.{u}.rlp p ↔
      (∀ (n : ℕ) (i : Fin (n + 3)), 0 < i → i < Fin.last (n + 2) →
        HasLiftingProperty (innerCell.{u} n i) p) ∧
      (∀ n : ℕ, HasLiftingProperty (cocartesianCriticalCell.{u} n) p) ∧
      HasLiftingProperty cocartesianEndpointCell.{u} p ∧
      HasLiftingProperty compositionCell.{u} p ∧ HasLiftingProperty equivalenceMarkCell.{u} p := by
  rw [cocartesianCells_rlp_iff_all]
  constructor
  · intro hp
    exact ⟨fun n i hi hi' => hp (.inl ⟨n, ⟨i, hi, hi'⟩⟩),
      fun n => hp (.inr (.inl n)),
      hp (.inr (.inr 0)), hp (.inr (.inr 1)), hp (.inr (.inr 2))⟩
  · rintro ⟨hi, hc, he, ht, hk⟩ s
    rcases s with ⟨n, i⟩ | n | i
    · exact hi n i.val i.property.1 i.property.2
    · exact hc n
    · fin_cases i
      · exact he
      · exact ht
      · exact hk

end SSet.Marked
