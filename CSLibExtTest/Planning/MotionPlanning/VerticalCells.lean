/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Planning.MotionPlanning.VerticalCells
public meta import CSLibExt.Planning.MotionPlanning.VerticalCells

/-!
# Vertical cell decomposition tests

Concrete fixtures (unit trapezoid, split square, sloped trapezoid, triangle),
carrier evaluations, incidence and neighborhood examples, and axiom probes for
`CSLibExt.Planning.MotionPlanning.VerticalCells`.
-/

open scoped Topology

namespace Cslib.Planning.MotionPlanning.VerticalCellsTests

open Cslib.Planning.MotionPlanning Cslib.Planning.MotionPlanning.VerticalCells

/-- Unit square as a trapezoid: `x₁ = 0`, `x₂ = 1`, `bot = 0`, `top = 1`. -/
def unitTrap : VTrap where
  x₁ := 0
  x₂ := 1
  bot := AffineMap.const ℝ ℝ 0
  top := AffineMap.const ℝ ℝ 1
  x₁_lt_x₂ := zero_lt_one
  bot_le_top₁ := zero_le_one
  bot_le_top₂ := zero_le_one
  nondegenerate := Or.inl zero_lt_one

/-- The center point lies in the unit-square carrier. -/
lemma center_mem : (!₂[(1 / 2 : ℝ), 1 / 2] : plane) ∈ unitTrap.carrier := by
  simp only [unitTrap, VTrap.carrier, Set.mem_ofPred_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one, AffineMap.const_apply]
  norm_num

/-- A boundary point is excluded from the unit-square carrier. -/
example : (!₂[(0 : ℝ), 1 / 2] : plane) ∉ unitTrap.carrier := by
  simp only [unitTrap, VTrap.carrier, Set.mem_ofPred_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one, AffineMap.const_apply]
  intro h
  obtain ⟨h1, _, _, _⟩ := h
  norm_num at h1

/-- The `m = 1, k = 0` decomposition of the open unit square. -/
def unitDecomp : TrapDecomp unitTrap.carrier where
  m := 1
  k := 0
  trap := fun _ => unitTrap
  wall := fun j => Fin.elim0 j
  pairwise_disjoint := by
    intro c₁ c₂ hne
    cases c₁ with
    | inl i =>
      cases c₂ with
      | inl i' =>
        exfalso
        apply hne
        congr 1
        exact Subsingleton.elim _ _
      | inr j' => exact Fin.elim0 j'
    | inr j => exact Fin.elim0 j
  iUnion_eq := by
    ext p
    simp only [Set.mem_union, Set.mem_iUnion, Fin.exists_fin_one]
    constructor
    · rintro (h | ⟨j, _⟩)
      · simpa using h
      · exact Fin.elim0 j
    · intro h
      exact Or.inl h

/-- Unique cell at the center of the unit-square decomposition. -/
example : ∃! c : unitDecomp.Cell,
    (!₂[(1 / 2 : ℝ), 1 / 2] : plane) ∈ unitDecomp.carrier c :=
  unitDecomp.existsUnique_cell _ center_mem

/-- Left unit square of the `(0, 2) × (0, 1)` rectangle. -/
def leftTrap : VTrap where
  x₁ := 0
  x₂ := 1
  bot := AffineMap.const ℝ ℝ 0
  top := AffineMap.const ℝ ℝ 1
  x₁_lt_x₂ := zero_lt_one
  bot_le_top₁ := zero_le_one
  bot_le_top₂ := zero_le_one
  nondegenerate := Or.inl zero_lt_one

/-- Right unit square of the `(0, 2) × (0, 1)` rectangle. -/
def rightTrap : VTrap where
  x₁ := 1
  x₂ := 2
  bot := AffineMap.const ℝ ℝ 0
  top := AffineMap.const ℝ ℝ 1
  x₁_lt_x₂ := one_lt_two
  bot_le_top₁ := zero_le_one
  bot_le_top₂ := zero_le_one
  nondegenerate := Or.inl zero_lt_one

/-- The shared wall `x = 1`, `y ∈ (0, 1)`. -/
def midWall : VSeg where
  x := 1
  y₁ := 0
  y₂ := 1
  y₁_lt_y₂ := zero_lt_one

def twoTrap : Fin 2 → VTrap := ![leftTrap, rightTrap]

def twoWall : Fin 1 → VSeg := fun _ => midWall

lemma left_right_disjoint : Disjoint leftTrap.carrier rightTrap.carrier := by
  rw [Set.disjoint_iff]
  intro p h
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, leftTrap, rightTrap, VTrap.carrier,
    AffineMap.const_apply] at h
  obtain ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩⟩ := h
  linarith

lemma left_wall_disjoint : Disjoint leftTrap.carrier midWall.carrier := by
  rw [Set.disjoint_iff]
  intro p h
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, leftTrap, midWall, VTrap.carrier,
    VSeg.carrier, AffineMap.const_apply] at h
  obtain ⟨⟨a1, a2, a3, a4⟩, ⟨c0, c1, c2⟩⟩ := h
  linarith

lemma right_wall_disjoint : Disjoint rightTrap.carrier midWall.carrier := by
  rw [Set.disjoint_iff]
  intro p h
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, rightTrap, midWall, VTrap.carrier,
    VSeg.carrier, AffineMap.const_apply] at h
  obtain ⟨⟨b1, b2, b3, b4⟩, ⟨c0, c1, c2⟩⟩ := h
  linarith

/-- The open rectangle `(0, 2) × (0, 1)`. -/
def F2 : Set plane := {p | 0 < p 0 ∧ p 0 < 2 ∧ 0 < p 1 ∧ p 1 < 1}

/-- The `m = 2, k = 1` decomposition of `(0, 2) × (0, 1)` split at `x = 1`. -/
def twoDecomp : TrapDecomp F2 where
  m := 2
  k := 1
  trap := twoTrap
  wall := twoWall
  pairwise_disjoint := by
    intro c₁ c₂ hne
    cases c₁ with
    | inl i =>
      cases c₂ with
      | inl i' =>
        fin_cases i <;> fin_cases i'
        · exact absurd rfl hne
        · simpa [twoTrap, twoWall, Function.onFun, Matrix.cons_val_zero,
            Matrix.cons_val_one] using left_right_disjoint
        · simpa [twoTrap, twoWall, Function.onFun, Matrix.cons_val_zero,
            Matrix.cons_val_one] using left_right_disjoint.symm
        · exact absurd rfl hne
      | inr j' =>
        fin_cases i <;> fin_cases j'
        · simpa [twoTrap, twoWall, Function.onFun, Matrix.cons_val_zero,
            Matrix.cons_val_one] using left_wall_disjoint
        · simpa [twoTrap, twoWall, Function.onFun, Matrix.cons_val_zero,
            Matrix.cons_val_one] using right_wall_disjoint
    | inr j =>
      cases c₂ with
      | inl i' =>
        fin_cases j
        fin_cases i'
        · simpa [twoTrap, twoWall, Function.onFun, Matrix.cons_val_zero,
            Matrix.cons_val_one] using left_wall_disjoint.symm
        · simpa [twoTrap, twoWall, Function.onFun, Matrix.cons_val_zero,
            Matrix.cons_val_one] using right_wall_disjoint.symm
      | inr j' =>
        fin_cases j
        fin_cases j'
        exact absurd rfl hne
  iUnion_eq := by
    ext p
    simp only [Set.mem_union, Set.mem_iUnion, Fin.exists_fin_two, Fin.exists_fin_one,
      twoTrap, twoWall, Matrix.cons_val_zero, Matrix.cons_val_one, leftTrap, rightTrap,
      midWall, F2, VTrap.carrier, VSeg.carrier, Set.mem_ofPred_eq, AffineMap.const_apply]
    constructor
    · intro h
      cases h with
      | inl hAB =>
        cases hAB with
        | inl hA => exact ⟨hA.1, lt_trans hA.2.1 one_lt_two, hA.2.2.1, hA.2.2.2⟩
        | inr hB => exact ⟨lt_trans zero_lt_one hB.1, hB.2.1, hB.2.2.1, hB.2.2.2⟩
      | inr hC =>
        rw [hC.1]
        exact ⟨zero_lt_one, one_lt_two, hC.2.1, hC.2.2⟩
    · rintro ⟨d1, d2, d3, d4⟩
      have htri : p 0 < 1 ∨ p 0 = 1 ∨ 1 < p 0 := lt_trichotomy _ _
      cases htri with
      | inl h => exact Or.inl (Or.inl ⟨d1, h, d3, d4⟩)
      | inr h =>
        cases h with
        | inl h => exact Or.inr ⟨h, d3, d4⟩
        | inr h => exact Or.inl (Or.inr ⟨h, d2, d3, d4⟩)

lemma left_hasR : leftTrap.HasOnRight midWall := by
  simp only [VTrap.HasOnRight, leftTrap, midWall, AffineMap.const_apply]
  exact ⟨trivial, le_rfl, le_rfl⟩

lemma right_hasL : rightTrap.HasOnLeft midWall := by
  simp only [VTrap.HasOnLeft, rightTrap, midWall, AffineMap.const_apply]
  exact ⟨trivial, le_rfl, le_rfl⟩

lemma wallpt_mem : (!₂[(1 : ℝ), 1 / 2] : plane) ∈ midWall.carrier := by
  simp only [midWall, VSeg.carrier, Set.mem_ofPred_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num

/-- The wall point lies in the closure of the left trapezoid. -/
example : (!₂[(1 : ℝ), 1 / 2] : plane) ∈ closure leftTrap.carrier :=
  twoDecomp.wall_subset_closure_of_hasOnRight (i := (0 : Fin 2)) (j := (0 : Fin 1))
    left_hasR wallpt_mem

/-- The wall point lies in the closure of the right trapezoid. -/
example : (!₂[(1 : ℝ), 1 / 2] : plane) ∈ closure rightTrap.carrier :=
  twoDecomp.wall_subset_closure_of_hasOnLeft (i := (1 : Fin 2)) (j := (0 : Fin 1))
    right_hasL wallpt_mem

#print axioms TrapDecomp.existsUnique_cell
#print axioms TrapDecomp.wall_subset_closure_of_hasOnRight

/-- Left half of the `(0, 2) × (0, 2)` square. -/
def sqLeftTrap : VTrap where
  x₁ := 0
  x₂ := 1
  bot := AffineMap.const ℝ ℝ 0
  top := AffineMap.const ℝ ℝ 2
  x₁_lt_x₂ := zero_lt_one
  bot_le_top₁ := zero_le_two
  bot_le_top₂ := zero_le_two
  nondegenerate := Or.inl zero_lt_two

/-- Right half of the `(0, 2) × (0, 2)` square. -/
def sqRightTrap : VTrap where
  x₁ := 1
  x₂ := 2
  bot := AffineMap.const ℝ ℝ 0
  top := AffineMap.const ℝ ℝ 2
  x₁_lt_x₂ := one_lt_two
  bot_le_top₁ := zero_le_two
  bot_le_top₂ := zero_le_two
  nondegenerate := Or.inl zero_lt_two

/-- The shared wall `x = 1`, `y ∈ (0, 2)`. -/
def sqMidWall : VSeg where
  x := 1
  y₁ := 0
  y₂ := 2
  y₁_lt_y₂ := zero_lt_two

def sqTwoTrap : Fin 2 → VTrap := ![sqLeftTrap, sqRightTrap]

def sqTwoWall : Fin 1 → VSeg := fun _ => sqMidWall

lemma sq_left_right_disjoint : Disjoint sqLeftTrap.carrier sqRightTrap.carrier := by
  rw [Set.disjoint_iff]
  intro p h
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, sqLeftTrap, sqRightTrap, VTrap.carrier,
    AffineMap.const_apply] at h
  obtain ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩⟩ := h
  linarith

lemma sq_left_wall_disjoint : Disjoint sqLeftTrap.carrier sqMidWall.carrier := by
  rw [Set.disjoint_iff]
  intro p h
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, sqLeftTrap, sqMidWall, VTrap.carrier,
    VSeg.carrier, AffineMap.const_apply] at h
  obtain ⟨⟨a1, a2, a3, a4⟩, ⟨c0, c1, c2⟩⟩ := h
  linarith

lemma sq_right_wall_disjoint : Disjoint sqRightTrap.carrier sqMidWall.carrier := by
  rw [Set.disjoint_iff]
  intro p h
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, sqRightTrap, sqMidWall, VTrap.carrier,
    VSeg.carrier, AffineMap.const_apply] at h
  obtain ⟨⟨b1, b2, b3, b4⟩, ⟨c0, c1, c2⟩⟩ := h
  linarith

/-- The open square `(0, 2) × (0, 2)`. -/
def Fsq : Set plane := {p | 0 < p 0 ∧ p 0 < 2 ∧ 0 < p 1 ∧ p 1 < 2}

/-- The `m = 2, k = 1` decomposition of `(0, 2) × (0, 2)` split at `x = 1`. -/
def sqDecomp : TrapDecomp Fsq where
  m := 2
  k := 1
  trap := sqTwoTrap
  wall := sqTwoWall
  pairwise_disjoint := by
    intro c₁ c₂ hne
    cases c₁ with
    | inl i =>
      cases c₂ with
      | inl i' =>
        fin_cases i <;> fin_cases i'
        · exact absurd rfl hne
        · simpa [sqTwoTrap, sqTwoWall, Function.onFun, Matrix.cons_val_zero,
            Matrix.cons_val_one] using sq_left_right_disjoint
        · simpa [sqTwoTrap, sqTwoWall, Function.onFun, Matrix.cons_val_zero,
            Matrix.cons_val_one] using sq_left_right_disjoint.symm
        · exact absurd rfl hne
      | inr j' =>
        fin_cases i <;> fin_cases j'
        · simpa [sqTwoTrap, sqTwoWall, Function.onFun, Matrix.cons_val_zero,
            Matrix.cons_val_one] using sq_left_wall_disjoint
        · simpa [sqTwoTrap, sqTwoWall, Function.onFun, Matrix.cons_val_zero,
            Matrix.cons_val_one] using sq_right_wall_disjoint
    | inr j =>
      cases c₂ with
      | inl i' =>
        fin_cases j
        fin_cases i'
        · simpa [sqTwoTrap, sqTwoWall, Function.onFun, Matrix.cons_val_zero,
            Matrix.cons_val_one] using sq_left_wall_disjoint.symm
        · simpa [sqTwoTrap, sqTwoWall, Function.onFun, Matrix.cons_val_zero,
            Matrix.cons_val_one] using sq_right_wall_disjoint.symm
      | inr j' =>
        fin_cases j
        fin_cases j'
        exact absurd rfl hne
  iUnion_eq := by
    ext p
    simp only [Set.mem_union, Set.mem_iUnion, Fin.exists_fin_two, Fin.exists_fin_one,
      sqTwoTrap, sqTwoWall, Matrix.cons_val_zero, Matrix.cons_val_one, sqLeftTrap, sqRightTrap,
      sqMidWall, Fsq, VTrap.carrier, VSeg.carrier, Set.mem_ofPred_eq, AffineMap.const_apply]
    constructor
    · intro h
      cases h with
      | inl hAB =>
        cases hAB with
        | inl hA => exact ⟨hA.1, lt_trans hA.2.1 one_lt_two, hA.2.2.1, hA.2.2.2⟩
        | inr hB => exact ⟨lt_trans zero_lt_one hB.1, hB.2.1, hB.2.2.1, hB.2.2.2⟩
      | inr hC =>
        rw [hC.1]
        exact ⟨zero_lt_one, one_lt_two, hC.2.1, hC.2.2⟩
    · rintro ⟨d1, d2, d3, d4⟩
      have htri : p 0 < 1 ∨ p 0 = 1 ∨ 1 < p 0 := lt_trichotomy _ _
      cases htri with
      | inl h => exact Or.inl (Or.inl ⟨d1, h, d3, d4⟩)
      | inr h =>
        cases h with
        | inl h => exact Or.inr ⟨h, d3, d4⟩
        | inr h => exact Or.inl (Or.inr ⟨h, d2, d3, d4⟩)

lemma sq_left_hasR : sqLeftTrap.HasOnRight sqMidWall := by
  simp only [VTrap.HasOnRight, sqLeftTrap, sqMidWall, AffineMap.const_apply]
  exact ⟨trivial, le_rfl, le_rfl⟩

lemma sq_right_hasL : sqRightTrap.HasOnLeft sqMidWall := by
  simp only [VTrap.HasOnLeft, sqRightTrap, sqMidWall, AffineMap.const_apply]
  exact ⟨trivial, le_rfl, le_rfl⟩

/-- The open square is open. -/
lemma isOpen_Fsq : IsOpen Fsq := by
  have hc0 : Continuous (fun p : plane => p 0) := PiLp.continuous_apply 2 _ 0
  have hc1 : Continuous (fun p : plane => p 1) := PiLp.continuous_apply 2 _ 1
  have e : Fsq = (fun p : plane => p 0) ⁻¹' Set.Ioo (0 : ℝ) 2 ∩
      (fun p : plane => p 1) ⁻¹' Set.Ioo (0 : ℝ) 2 := by
    ext p
    simp only [Fsq, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_inter_iff, Set.mem_Ioo]
    tauto
  rw [e]
  exact (isOpen_Ioo.preimage hc0).inter (isOpen_Ioo.preimage hc1)

/-- The wall midpoint lies in the wall carrier. -/
lemma sq_wallpt_mem : (!₂[(1 : ℝ), 1] : plane) ∈ sqMidWall.carrier := by
  simp only [sqMidWall, VSeg.carrier, Set.mem_ofPred_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num

/-- The wall midpoint lies in the closure of the left trapezoid. -/
lemma sq_mid_mem_closure_left : (!₂[(1 : ℝ), 1] : plane) ∈ closure sqLeftTrap.carrier :=
  sqDecomp.wall_subset_closure_of_hasOnRight (i := (0 : Fin 2)) (j := (0 : Fin 1))
    sq_left_hasR sq_wallpt_mem

/-- The wall midpoint lies in the open square. -/
lemma sq_mid_mem_Fsq : (!₂[(1 : ℝ), 1] : plane) ∈ Fsq := by
  simp only [Fsq, Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- The wall midpoint lies in the closure of the left cell, intersected with `F`. -/
lemma sq_mid_mem_closure_inter :
    (!₂[(1 : ℝ), 1] : plane) ∈ closure (sqDecomp.trap (0 : Fin 2)).carrier ∩ Fsq :=
  ⟨sq_mid_mem_closure_left, sq_mid_mem_Fsq⟩

/-- The closure characterization applies at the wall midpoint. -/
example : (!₂[(1 : ℝ), 1] : plane) ∈ (sqDecomp.trap (0 : Fin 2)).carrier ∨
    ∃ j : Fin sqDecomp.k,
      ∃ _ : (sqDecomp.trap (0 : Fin 2)).HasOnRight (sqDecomp.wall j) ∨
        (sqDecomp.trap (0 : Fin 2)).HasOnLeft (sqDecomp.wall j),
        (!₂[(1 : ℝ), 1] : plane) ∈ (sqDecomp.wall j).carrier := by
  have h := sqDecomp.closure_carrier_inter_subset isOpen_Fsq (0 : Fin 2)
    sq_mid_mem_closure_inter
  simpa [Set.mem_union, Set.mem_iUnion] using h

/-- A lower-side point of the left trapezoid. -/
lemma sq_lowerpt_mem : (!₂[(1 / 2 : ℝ), 0] : plane) ∈ sqLeftTrap.lowerSide := by
  simp only [sqLeftTrap, VTrap.lowerSide, Set.mem_ofPred_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one, AffineMap.const_apply]
  norm_num

/-- The lower-side point is outside `F`, by disjointness of lower sides from `F`. -/
example : (!₂[(1 / 2 : ℝ), 0] : plane) ∉ Fsq := by
  have hdisj := sqDecomp.lowerSide_disjoint isOpen_Fsq (0 : Fin 2)
  have hmem : (!₂[(1 / 2 : ℝ), 0] : plane) ∈ (sqDecomp.trap (0 : Fin 2)).lowerSide :=
    sq_lowerpt_mem
  exact (Set.disjoint_left.mp hdisj) hmem

/-- The wall endpoints are outside `F`. -/
example : (!₂[(1 : ℝ), 0] : plane) ∉ Fsq ∧ (!₂[(1 : ℝ), 2] : plane) ∉ Fsq :=
  sqDecomp.wall_endpoints_not_mem (0 : Fin 1)

#print axioms TrapDecomp.lowerSide_disjoint
#print axioms TrapDecomp.closure_carrier_inter_subset
#print axioms TrapDecomp.wall_endpoints_not_mem

/-- The left trapezoid borders the middle wall on the right. -/
lemma hasRight_0 :
    (sqDecomp.trap (0 : Fin 2)).HasOnRight (sqDecomp.wall (0 : Fin 1)) := by
  have hT : sqDecomp.trap (0 : Fin 2) = sqLeftTrap := by
    simp only [sqDecomp, sqTwoTrap, Matrix.cons_val_zero]
  have hW : sqDecomp.wall (0 : Fin 1) = sqMidWall := rfl
  rw [hT, hW]
  simp only [VTrap.HasOnRight, sqLeftTrap, sqMidWall, AffineMap.const_apply]
  exact ⟨trivial, le_rfl, le_rfl⟩

/-- The right trapezoid borders the middle wall on the left. -/
lemma hasLeft_1 :
    (sqDecomp.trap (1 : Fin 2)).HasOnLeft (sqDecomp.wall (0 : Fin 1)) := by
  have hT : sqDecomp.trap (1 : Fin 2) = sqRightTrap := by

    simp only [sqDecomp, sqTwoTrap, Matrix.cons_val_one, Matrix.cons_val_zero]
  have hW : sqDecomp.wall (0 : Fin 1) = sqMidWall := rfl
  rw [hT, hW]
  simp only [VTrap.HasOnLeft, sqRightTrap, sqMidWall, AffineMap.const_apply]
  exact ⟨trivial, le_rfl, le_rfl⟩

/-- The middle wall's unique left neighbor is trapezoid `0`: `sqLeftTrap` lies
left of the wall (`x ∈ (0, 1)`) and satisfies `HasOnRight`. -/
theorem right_idx (i : Fin 2)
    (hi : (sqDecomp.trap i).HasOnRight (sqDecomp.wall (0 : Fin 1))) : i = 0 := by
  have huniq :=
    Cslib.Planning.MotionPlanning.VerticalCells.TrapDecomp.existsUnique_hasOnRight
      sqDecomp isOpen_Fsq (0 : Fin 1)
  exact ExistsUnique.unique huniq hi sq_left_hasR

/-- The middle wall's unique right neighbor is trapezoid `1`: `sqRightTrap` lies
right of the wall (`x ∈ (1, 2)`) and satisfies `HasOnLeft`. -/
theorem left_idx (i : Fin 2)
    (hi : (sqDecomp.trap i).HasOnLeft (sqDecomp.wall (0 : Fin 1))) : i = 1 := by
  have huniq :=
    Cslib.Planning.MotionPlanning.VerticalCells.TrapDecomp.existsUnique_hasOnLeft
      sqDecomp isOpen_Fsq (0 : Fin 1)
  exact ExistsUnique.unique huniq hi sq_right_hasL

/-- The wall midpoint `!₂[1, 1]` lies in the middle wall. -/
lemma mid_mem :
    (!₂[(1 : ℝ), (1 : ℝ)] : plane) ∈ (sqDecomp.wall (0 : Fin 1)).carrier := by
  have hW : sqDecomp.wall (0 : Fin 1) = sqMidWall := rfl
  rw [hW]
  simp only [sqMidWall, VSeg.carrier, Set.mem_ofPred_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num

/-- The wall midpoint has the neighborhood property. -/
theorem nhds_mid :
    ∃ U ∈ 𝓝 (!₂[(1 : ℝ), (1 : ℝ)] : plane),
      U ⊆ (sqDecomp.wall (0 : Fin 1)).carrier ∪
        ⋃ (i : Fin 2) (_ : (sqDecomp.trap i).HasOnRight (sqDecomp.wall (0 : Fin 1)) ∨
          (sqDecomp.trap i).HasOnLeft (sqDecomp.wall (0 : Fin 1))),
          (sqDecomp.trap i).carrier := by
  exact Cslib.Planning.MotionPlanning.VerticalCells.TrapDecomp.wall_neighborhood
    sqDecomp isOpen_Fsq _ _ mid_mem

/-- A point just left of the wall lies in the neighborhood union. -/
theorem nhds_mid_union_mem :
    (!₂[(1 / 2 : ℝ), (1 : ℝ)] : plane) ∈
      (sqDecomp.wall (0 : Fin 1)).carrier ∪
        ⋃ (i : Fin 2) (_ : (sqDecomp.trap i).HasOnRight (sqDecomp.wall (0 : Fin 1)) ∨
          (sqDecomp.trap i).HasOnLeft (sqDecomp.wall (0 : Fin 1))),
          (sqDecomp.trap i).carrier := by
  refine Or.inr (Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨Or.inl hasRight_0, ?_⟩⟩)
  have hT : sqDecomp.trap (0 : Fin 2) = sqLeftTrap := by
    simp only [sqDecomp, sqTwoTrap, Matrix.cons_val_zero]
  rw [hT]
  simp only [sqLeftTrap, VTrap.carrier, Set.mem_ofPred_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one, AffineMap.const_apply]
  norm_num

noncomputable def slopeBot : ℝ →ᵃ[ℝ] ℝ := (1/2 : ℝ) • AffineMap.id ℝ ℝ
noncomputable def slopeTop : ℝ →ᵃ[ℝ] ℝ := AffineMap.const ℝ ℝ 2 - (1/2 : ℝ) • AffineMap.id ℝ ℝ

theorem slopeBot_apply (x : ℝ) : slopeBot x = x / 2 := by
  simp only [slopeBot, AffineMap.coe_smul, Pi.smul_apply, AffineMap.id_apply, smul_eq_mul]
  ring

theorem slopeTop_apply (x : ℝ) : slopeTop x = 2 - x / 2 := by
  simp only [slopeTop, AffineMap.coe_sub, Pi.sub_apply, AffineMap.const_apply,
    AffineMap.coe_smul, Pi.smul_apply, AffineMap.id_apply, smul_eq_mul]
  ring

noncomputable def slopeTrap : Cslib.Planning.MotionPlanning.VerticalCells.VTrap where
  x₁ := 0
  x₂ := 1
  bot := slopeBot
  top := slopeTop
  x₁_lt_x₂ := by norm_num
  bot_le_top₁ := by rw [slopeBot_apply, slopeTop_apply]; norm_num
  bot_le_top₂ := by rw [slopeBot_apply, slopeTop_apply]; norm_num
  nondegenerate := Or.inl (by rw [slopeBot_apply, slopeTop_apply]; norm_num)

theorem slopeTrap_mem :
    (!₂[1/2, 1] : plane) ∈
      Cslib.Planning.MotionPlanning.VerticalCells.VTrap.carrier slopeTrap := by
  show (0:ℝ) < 1/2 ∧ (1/2:ℝ) < 1 ∧ slopeBot (1/2) < 1 ∧ (1:ℝ) < slopeTop (1/2)
  rw [slopeBot_apply, slopeTop_apply]
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem slopeTrap_outside :
    (slopeBot (3/2) < 1 ∧ (1:ℝ) < slopeTop (3/2)) ∧
    (!₂[3/2, 1] : plane) ∉
      Cslib.Planning.MotionPlanning.VerticalCells.VTrap.carrier slopeTrap := by
  constructor
  · rw [slopeBot_apply, slopeTop_apply]
    refine ⟨by norm_num, by norm_num⟩
  · intro h
    have h' : (0:ℝ) < 3/2 ∧ (3/2:ℝ) < 1 ∧ slopeBot (3/2) < 1 ∧
      (1:ℝ) < slopeTop (3/2) := h
    norm_num at h'

theorem slopeTrap_side :
    (!₂[1/2, 1/4] : plane) ∈
      Cslib.Planning.MotionPlanning.VerticalCells.VTrap.lowerSide slopeTrap ∧
    (!₂[1/2, 1/4] : plane) ∉
      Cslib.Planning.MotionPlanning.VerticalCells.VTrap.carrier slopeTrap := by
  constructor
  · show (0:ℝ) ≤ 1/2 ∧ (1/2:ℝ) ≤ 1 ∧ (1/4:ℝ) = slopeBot (1/2)
    rw [slopeBot_apply]
    refine ⟨by norm_num, by norm_num, by norm_num⟩
  · intro h
    have h' : (0:ℝ) < 1/2 ∧ (1/2:ℝ) < 1 ∧ slopeBot (1/2) < 1/4 ∧
      (1/4:ℝ) < slopeTop (1/2) := h
    rw [slopeBot_apply] at h'
    norm_num at h'

theorem slopeTrap_upper_notmem :
    (!₂[1/2, 15/8] : plane) ∉
      Cslib.Planning.MotionPlanning.VerticalCells.VTrap.carrier slopeTrap := by
  intro h
  have h' : (0:ℝ) < 1/2 ∧ (1/2:ℝ) < 1 ∧ slopeBot (1/2) < 15/8 ∧
    (15/8:ℝ) < slopeTop (1/2) := h
  rw [slopeBot_apply, slopeTop_apply] at h'
  norm_num at h'

def triBot : ℝ →ᵃ[ℝ] ℝ := AffineMap.const ℝ ℝ 0
def triTop : ℝ →ᵃ[ℝ] ℝ := AffineMap.id ℝ ℝ

theorem triBot_apply (x : ℝ) : triBot x = 0 := rfl
theorem triTop_apply (x : ℝ) : triTop x = x := rfl

def triTrap : Cslib.Planning.MotionPlanning.VerticalCells.VTrap where
  x₁ := 0
  x₂ := 1
  bot := triBot
  top := triTop
  x₁_lt_x₂ := by norm_num
  bot_le_top₁ := by simp [triBot_apply, triTop_apply]
  bot_le_top₂ := by rw [triBot_apply, triTop_apply]; norm_num
  nondegenerate := Or.inr (by rw [triBot_apply, triTop_apply]; norm_num)

theorem triTrap_eq_left :
    triTrap.bot triTrap.x₁ = triTrap.top triTrap.x₁ := by
  show triBot (0:ℝ) = triTop (0:ℝ)
  rw [triBot_apply, triTop_apply]

theorem triTrap_lt_right :
    triTrap.bot triTrap.x₂ < triTrap.top triTrap.x₂ := by
  show triBot (1:ℝ) < triTop (1:ℝ)
  rw [triBot_apply, triTop_apply]
  norm_num

theorem triTrap_nonempty :
    Set.Nonempty
      (Cslib.Planning.MotionPlanning.VerticalCells.VTrap.carrier triTrap) := by
  refine ⟨(!₂[1/2, 1/4] : plane), ?_⟩
  show (0:ℝ) < 1/2 ∧ (1/2:ℝ) < 1 ∧ triBot (1/2) < 1/4 ∧ (1/4:ℝ) < triTop (1/2)
  rw [triBot_apply, triTop_apply]
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem triTrap_apex_notmem :
    (!₂[0, 0] : plane) ∉
      Cslib.Planning.MotionPlanning.VerticalCells.VTrap.carrier triTrap := by
  intro h
  have h' : (0:ℝ) < 0 ∧ (0:ℝ) < 1 ∧ triBot (0:ℝ) < 0 ∧ (0:ℝ) < triTop (0:ℝ) := h
  norm_num at h'

theorem triTrap_upper_notmem :
    (!₂[1/2, 3/4] : plane) ∉
      Cslib.Planning.MotionPlanning.VerticalCells.VTrap.carrier triTrap := by
  intro h
  have h' : (0:ℝ) < 1/2 ∧ (1/2:ℝ) < 1 ∧ triBot (1/2) < 3/4 ∧
    (3/4:ℝ) < triTop (1/2) := h
  rw [triBot_apply, triTop_apply] at h'
  norm_num at h'

theorem sqDecomp_carrier_left_eq :
    Cslib.Planning.MotionPlanning.VerticalCells.TrapDecomp.carrier sqDecomp
      (Sum.inl ⟨0, by decide⟩) =
      {p | (0:ℝ) < p 0 ∧ p 0 < 1 ∧ (0:ℝ) < p 1 ∧ p 1 < 2} := rfl

theorem sqDecomp_carrier_left_mem :
    (!₂[1/2, 1] : plane) ∈
      Cslib.Planning.MotionPlanning.VerticalCells.TrapDecomp.carrier sqDecomp
        (Sum.inl ⟨0, by decide⟩) := by
  show (0:ℝ) < 1/2 ∧ (1/2:ℝ) < 1 ∧ (0:ℝ) < 1 ∧ (1:ℝ) < 2
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem sqDecomp_carrier_left_notmem :
    (!₂[3/2, 1] : plane) ∉
      Cslib.Planning.MotionPlanning.VerticalCells.TrapDecomp.carrier sqDecomp
        (Sum.inl ⟨0, by decide⟩) := by
  intro h
  have h' : (0:ℝ) < 3/2 ∧ (3/2:ℝ) < 1 ∧ (0:ℝ) < 1 ∧ (1:ℝ) < 2 := h
  norm_num at h'

theorem sqDecomp_carrier_right_eq :
    Cslib.Planning.MotionPlanning.VerticalCells.TrapDecomp.carrier sqDecomp
      (Sum.inl ⟨1, by decide⟩) =
      {p | (1:ℝ) < p 0 ∧ p 0 < 2 ∧ (0:ℝ) < p 1 ∧ p 1 < 2} := rfl

theorem sqDecomp_carrier_right_mem :
    (!₂[3/2, 1] : plane) ∈
      Cslib.Planning.MotionPlanning.VerticalCells.TrapDecomp.carrier sqDecomp
        (Sum.inl ⟨1, by decide⟩) := by
  show (1:ℝ) < 3/2 ∧ (3/2:ℝ) < 2 ∧ (0:ℝ) < 1 ∧ (1:ℝ) < 2
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem sqDecomp_carrier_wall_eq :
    Cslib.Planning.MotionPlanning.VerticalCells.TrapDecomp.carrier sqDecomp
      (Sum.inr ⟨0, by decide⟩) =
      {p | p 0 = (1:ℝ) ∧ (0:ℝ) < p 1 ∧ p 1 < 2} := rfl

theorem sqDecomp_carrier_wall_mem :
    (!₂[1, 1] : plane) ∈
      Cslib.Planning.MotionPlanning.VerticalCells.TrapDecomp.carrier sqDecomp
        (Sum.inr ⟨0, by decide⟩) := by
  show (1:ℝ) = 1 ∧ (0:ℝ) < 1 ∧ (1:ℝ) < 2
  exact ⟨rfl, one_pos, one_lt_two⟩

theorem sqDecomp_wallNbhd_left_mem :
    ∃ U ∈ 𝓝 (!₂[(1 : ℝ), (1 : ℝ)] : plane),
      U ⊆ (sqDecomp.wall (0 : Fin 1)).carrier ∪
        ⋃ (i : Fin 2) (_ : (sqDecomp.trap i).HasOnRight (sqDecomp.wall (0 : Fin 1)) ∨
          (sqDecomp.trap i).HasOnLeft (sqDecomp.wall (0 : Fin 1))),
          (sqDecomp.trap i).carrier ∧
      ∃ ε : ℝ, ∃ _ : 0 < ε, ∃ _ : ε < 1,
        Metric.ball (!₂[(1 : ℝ), (1 : ℝ)] : plane) ε ⊆ U ∧
        (!₂[(1 : ℝ) - ε/2, (1 : ℝ)] : plane) ∈ (sqDecomp.trap (0 : Fin 2)).carrier := by
  have hp : (!₂[(1 : ℝ), (1 : ℝ)] : plane) ∈
      (sqDecomp.wall ⟨0, by decide⟩).carrier := by
    show (1:ℝ) = 1 ∧ (0:ℝ) < 1 ∧ (1:ℝ) < 2
    exact ⟨rfl, one_pos, one_lt_two⟩
  obtain ⟨U, hU_mem0, hU_sub⟩ :=
    Cslib.Planning.MotionPlanning.VerticalCells.TrapDecomp.wall_neighborhood
      sqDecomp isOpen_Fsq _ _ hp
  have hU_mem_rw := hU_mem0
  rw [Metric.mem_nhds_iff] at hU_mem_rw
  obtain ⟨δ, hδpos, hballδ⟩ := hU_mem_rw
  set ε : ℝ := min δ 1 / 2 with hεdef
  have hminpos : 0 < min δ 1 := lt_min hδpos zero_lt_one
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hεlt1 : ε < 1 := by
    rw [hεdef]
    have hminle : min δ 1 ≤ 1 := min_le_right _ _
    linarith
  have hεleδ : ε ≤ δ := by
    rw [hεdef]
    have hminle : min δ 1 ≤ δ := min_le_left _ _
    linarith
  have hballε : Metric.ball (!₂[(1 : ℝ), (1 : ℝ)] : plane) ε ⊆ U :=
    Set.Subset.trans (Metric.ball_subset_ball hεleδ) hballδ
  have hpt_ball : (!₂[(1 : ℝ) - ε/2, (1 : ℝ)] : plane) ∈
      Metric.ball (!₂[(1 : ℝ), (1 : ℝ)] : plane) ε := by
    rw [Metric.mem_ball]
    have hdist : dist (!₂[(1 : ℝ) - ε/2, (1 : ℝ)] : plane)
        (!₂[(1 : ℝ), (1 : ℝ)] : plane) =
        |((!₂[(1 : ℝ) - ε/2, (1 : ℝ)] : plane)) 0 - 1| :=
      Cslib.Planning.MotionPlanning.VerticalCells.dist_mkPoint 1 _
    have hq0 : ((!₂[(1 : ℝ) - ε/2, (1 : ℝ)] : plane)) 0 = 1 - ε/2 := rfl
    rw [hq0] at hdist
    rw [hdist]
    have habs : |(1 - ε/2) - (1:ℝ)| = ε/2 := by
      have h1 : (1 - ε/2) - (1:ℝ) = -(ε/2) := by ring
      rw [h1, abs_neg]
      exact abs_of_nonneg (by linarith)
    rw [habs]
    linarith
  have hptU : (!₂[(1 : ℝ) - ε/2, (1 : ℝ)] : plane) ∈ U := hballε hpt_ball
  have hpt_union : (!₂[(1 : ℝ) - ε/2, (1 : ℝ)] : plane) ∈
      (sqDecomp.wall (0 : Fin 1)).carrier ∪
        ⋃ (i : Fin 2) (_ : (sqDecomp.trap i).HasOnRight (sqDecomp.wall (0 : Fin 1)) ∨
          (sqDecomp.trap i).HasOnLeft (sqDecomp.wall (0 : Fin 1))),
          (sqDecomp.trap i).carrier := hU_sub hptU
  have hpt_left : (!₂[(1 : ℝ) - ε/2, (1 : ℝ)] : plane) ∈
      (sqDecomp.trap (0 : Fin 2)).carrier := by
    rcases hpt_union with hwall | hu
    · have hW : sqDecomp.wall (0 : Fin 1) = sqMidWall := rfl
      rw [hW] at hwall
      have hwall' : ((!₂[(1 : ℝ) - ε/2, (1 : ℝ)] : plane)) 0 = (1:ℝ) ∧
        (0:ℝ) < ((!₂[(1 : ℝ) - ε/2, (1 : ℝ)] : plane)) 1 ∧
        ((!₂[(1 : ℝ) - ε/2, (1 : ℝ)] : plane)) 1 < 2 := hwall
      have hq0 : ((!₂[(1 : ℝ) - ε/2, (1 : ℝ)] : plane)) 0 = 1 - ε/2 := rfl
      rw [hq0] at hwall'
      linarith [hwall'.1, hεpos]
    · obtain ⟨i, hi_mem⟩ := Set.mem_iUnion.mp hu
      obtain ⟨hi, hmem⟩ := Set.mem_iUnion.mp hi_mem
      fin_cases i
      · exact hmem
      · have hmem1 : (!₂[(1 : ℝ) - ε/2, (1 : ℝ)] : plane) ∈
            (sqDecomp.trap (1 : Fin 2)).carrier := hmem
        have hT : sqDecomp.trap (1 : Fin 2) = sqRightTrap := by
          simp only [sqDecomp, sqTwoTrap, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [hT] at hmem1
        have hmem' : (1:ℝ) < ((!₂[(1 : ℝ) - ε/2, (1 : ℝ)] : plane)) 0 ∧
          ((!₂[(1 : ℝ) - ε/2, (1 : ℝ)] : plane)) 0 < 2 ∧
          (0:ℝ) < ((!₂[(1 : ℝ) - ε/2, (1 : ℝ)] : plane)) 1 ∧
          ((!₂[(1 : ℝ) - ε/2, (1 : ℝ)] : plane)) 1 < 2 := hmem1
        have hq0 : ((!₂[(1 : ℝ) - ε/2, (1 : ℝ)] : plane)) 0 = 1 - ε/2 := rfl
        rw [hq0] at hmem'
        linarith [hmem'.1, hεpos]
  exact ⟨U, hU_mem0, hU_sub, ε, hεpos, hεlt1, hballε, hpt_left⟩

#print axioms Cslib.Planning.MotionPlanning.VerticalCells.TrapDecomp.existsUnique_hasOnRight
#print axioms Cslib.Planning.MotionPlanning.VerticalCells.TrapDecomp.existsUnique_hasOnLeft
#print axioms Cslib.Planning.MotionPlanning.VerticalCells.TrapDecomp.wall_neighborhood

end Cslib.Planning.MotionPlanning.VerticalCellsTests
