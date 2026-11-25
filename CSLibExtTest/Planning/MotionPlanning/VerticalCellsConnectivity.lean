/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Planning.MotionPlanning.VerticalCellsConnectivity
public meta import CSLibExt.Planning.MotionPlanning.VerticalCellsConnectivity

/-!
# Vertical cells connectivity tests

Split-square incidence/reachability checks and a two-component separation
check for `CSLibExt.Planning.MotionPlanning.VerticalCellsConnectivity`.
-/

open scoped Topology

namespace Cslib.Planning.MotionPlanning.VerticalCellsTests

open Cslib.Planning.MotionPlanning Cslib.Planning.MotionPlanning.VerticalCells

/-!
Split-square fixture: `F` is the open square `(0,2) × (0,2)`, split by the wall
`x = 1` into two open trapezoid cells. Tests for the incidence graph and the
graph-to-path direction (LaValle, Planning Algorithms, Sec. 6.2.2).
-/

/-- The open square `(0,2) × (0,2)`. -/
def splitSquareF : Set plane :=
  {p | 0 < p 0 ∧ p 0 < 2 ∧ 0 < p 1 ∧ p 1 < 2}

def splitSquareBot : ℝ →ᵃ[ℝ] ℝ := AffineMap.const ℝ ℝ 0
def splitSquareTop : ℝ →ᵃ[ℝ] ℝ := AffineMap.const ℝ ℝ 2

/-- Left trapezoid `(0,1) × (0,2)`. -/
def splitSquareLeft : VTrap where
  x₁ := 0
  x₂ := 1
  bot := splitSquareBot
  top := splitSquareTop
  x₁_lt_x₂ := by norm_num
  bot_le_top₁ := by
    simp only [splitSquareBot, splitSquareTop, AffineMap.const_apply]
    norm_num
  bot_le_top₂ := by
    simp only [splitSquareBot, splitSquareTop, AffineMap.const_apply]
    norm_num
  nondegenerate := by
    left
    simp only [splitSquareBot, splitSquareTop, AffineMap.const_apply]
    norm_num

/-- Right trapezoid `(1,2) × (0,2)`. -/
def splitSquareRight : VTrap where
  x₁ := 1
  x₂ := 2
  bot := splitSquareBot
  top := splitSquareTop
  x₁_lt_x₂ := by norm_num
  bot_le_top₁ := by
    simp only [splitSquareBot, splitSquareTop, AffineMap.const_apply]
    norm_num
  bot_le_top₂ := by
    simp only [splitSquareBot, splitSquareTop, AffineMap.const_apply]
    norm_num
  nondegenerate := by
    left
    simp only [splitSquareBot, splitSquareTop, AffineMap.const_apply]
    norm_num

/-- The splitting wall `{1} × (0,2)`. -/
def splitSquareWall : VSeg where
  x := 1
  y₁ := 0
  y₂ := 2
  y₁_lt_y₂ := by norm_num

def splitSquareTrap : Fin 2 → VTrap := ![splitSquareLeft, splitSquareRight]
def splitSquareWallFun : Fin 1 → VSeg := fun _ => splitSquareWall

theorem mem_splitSquareLeft_carrier (p : plane) :
    p ∈ splitSquareLeft.carrier ↔ 0 < p 0 ∧ p 0 < 1 ∧ 0 < p 1 ∧ p 1 < 2 :=
  Iff.rfl

theorem mem_splitSquareRight_carrier (p : plane) :
    p ∈ splitSquareRight.carrier ↔ 1 < p 0 ∧ p 0 < 2 ∧ 0 < p 1 ∧ p 1 < 2 :=
  Iff.rfl

theorem mem_splitSquareWall_carrier (p : plane) :
    p ∈ splitSquareWall.carrier ↔ p 0 = 1 ∧ 0 < p 1 ∧ p 1 < 2 :=
  Iff.rfl

theorem splitSquareTrap_zero : splitSquareTrap 0 = splitSquareLeft := rfl
theorem splitSquareTrap_one : splitSquareTrap 1 = splitSquareRight := rfl
theorem splitSquareWallFun_zero : splitSquareWallFun 0 = splitSquareWall := rfl

theorem disjoint_splitSquareLeft_right :
    Disjoint splitSquareLeft.carrier splitSquareRight.carrier := by
  rw [Set.disjoint_left]
  rintro p hp hq
  rw [mem_splitSquareLeft_carrier] at hp
  rw [mem_splitSquareRight_carrier] at hq
  obtain ⟨-, hp2, -, -⟩ := hp
  obtain ⟨hq1, -, -, -⟩ := hq
  linarith

theorem disjoint_splitSquareLeft_wall :
    Disjoint splitSquareLeft.carrier splitSquareWall.carrier := by
  rw [Set.disjoint_left]
  rintro p hp hq
  rw [mem_splitSquareLeft_carrier] at hp
  rw [mem_splitSquareWall_carrier] at hq
  obtain ⟨-, hp2, -, -⟩ := hp
  obtain ⟨hq1, -, -⟩ := hq
  linarith

theorem disjoint_splitSquareRight_wall :
    Disjoint splitSquareRight.carrier splitSquareWall.carrier := by
  rw [Set.disjoint_left]
  rintro p hp hq
  rw [mem_splitSquareRight_carrier] at hp
  rw [mem_splitSquareWall_carrier] at hq
  obtain ⟨hq1, -, -, -⟩ := hp
  obtain ⟨hq2, -, -⟩ := hq
  linarith

def splitSquareDecomp : TrapDecomp splitSquareF where
  m := 2
  k := 1
  trap := splitSquareTrap
  wall := splitSquareWallFun
  pairwise_disjoint := by
    intro c1 c2 hne
    cases c1 with
    | inl i =>
      cases c2 with
      | inl i' =>
        fin_cases i <;> fin_cases i' <;> first
          | exact absurd rfl hne
          | exact disjoint_splitSquareLeft_right
          | exact disjoint_splitSquareLeft_right.symm
      | inr j =>
        fin_cases i <;> fin_cases j <;> first
          | exact disjoint_splitSquareLeft_wall
          | exact disjoint_splitSquareRight_wall
    | inr j =>
      cases c2 with
      | inl i =>
        fin_cases j
        fin_cases i <;> first
          | exact disjoint_splitSquareLeft_wall.symm
          | exact disjoint_splitSquareRight_wall.symm
      | inr j' =>
        fin_cases j
        fin_cases j'
        exact absurd rfl hne
  iUnion_eq := by
    ext p
    simp only [Set.mem_union, Set.mem_iUnion]
    constructor
    · rintro (⟨i, hi⟩ | ⟨j, hj⟩)
      · fin_cases i
        · have hiL : p ∈ splitSquareLeft.carrier := hi
          rw [mem_splitSquareLeft_carrier] at hiL
          simp only [splitSquareF, Set.mem_ofPred_eq]
          obtain ⟨h1, h2, h3, h4⟩ := hiL
          exact ⟨h1, by linarith, h3, h4⟩
        · have hiR : p ∈ splitSquareRight.carrier := hi
          rw [mem_splitSquareRight_carrier] at hiR
          simp only [splitSquareF, Set.mem_ofPred_eq]
          obtain ⟨h1, h2, h3, h4⟩ := hiR
          exact ⟨by linarith, h2, h3, h4⟩
      · fin_cases j
        have hjW : p ∈ splitSquareWall.carrier := hj
        rw [mem_splitSquareWall_carrier] at hjW
        simp only [splitSquareF, Set.mem_ofPred_eq]
        obtain ⟨h1, h2, h3⟩ := hjW
        rw [h1]
        exact ⟨by norm_num, by norm_num, h2, h3⟩
    · intro hp
      simp only [splitSquareF, Set.mem_ofPred_eq] at hp
      obtain ⟨h1, h2, h3, h4⟩ := hp
      rcases lt_trichotomy (p 0) 1 with h | h | h
      · exact Or.inl ⟨0, by
          rw [splitSquareTrap_zero, mem_splitSquareLeft_carrier]
          exact ⟨h1, h, h3, h4⟩⟩
      · exact Or.inr ⟨0, by
          rw [splitSquareWallFun_zero, mem_splitSquareWall_carrier]
          exact ⟨h, h3, h4⟩⟩
      · exact Or.inl ⟨1, by
          rw [splitSquareTrap_one, mem_splitSquareRight_carrier]
          exact ⟨h, h2, h3, h4⟩⟩

theorem splitSquareLeft_hasOnRight_wall :
    splitSquareLeft.HasOnRight splitSquareWall :=
  ⟨rfl, le_refl 0, le_refl 2⟩

theorem splitSquareRight_hasOnLeft_wall :
    splitSquareRight.HasOnLeft splitSquareWall :=
  ⟨rfl, le_refl 0, le_refl 2⟩

theorem splitSquare_left_adj_wall :
    splitSquareDecomp.incidenceGraph.Adj (.inl (0 : Fin 2)) (.inr (0 : Fin 1)) :=
  (splitSquareDecomp.incidenceGraph_adj_inl_inr (0 : Fin 2) (0 : Fin 1)).mpr
    (Or.inl splitSquareLeft_hasOnRight_wall)

theorem splitSquare_right_adj_wall :
    splitSquareDecomp.incidenceGraph.Adj (.inl (1 : Fin 2)) (.inr (0 : Fin 1)) :=
  (splitSquareDecomp.incidenceGraph_adj_inl_inr (1 : Fin 2) (0 : Fin 1)).mpr
    (Or.inr splitSquareRight_hasOnLeft_wall)

theorem splitSquare_traps_not_adj :
    ¬ splitSquareDecomp.incidenceGraph.Adj (.inl (0 : Fin 2)) (.inl (1 : Fin 2)) :=
  splitSquareDecomp.incidenceGraph_not_adj_inl_inl (0 : Fin 2) (1 : Fin 2)

theorem splitSquare_wall_adj_left :
    splitSquareDecomp.incidenceGraph.Adj (.inr (0 : Fin 1)) (.inl (0 : Fin 2)) :=
  splitSquare_left_adj_wall.symm

theorem splitSquare_wall_adj_right :
    splitSquareDecomp.incidenceGraph.Adj (.inr (0 : Fin 1)) (.inl (1 : Fin 2)) :=
  splitSquare_right_adj_wall.symm

theorem splitSquare_reachable_through_wall :
    splitSquareDecomp.incidenceGraph.Reachable
      (.inl (0 : Fin 2)) (.inl (1 : Fin 2)) :=
  SimpleGraph.Reachable.trans
    (SimpleGraph.Adj.reachable splitSquare_left_adj_wall)
    (SimpleGraph.Adj.reachable splitSquare_wall_adj_right)

theorem splitSquare_joined_across_wall (p q : plane)
    (hp : p ∈ splitSquareDecomp.carrier (.inl (0 : Fin 2)))
    (hq : q ∈ splitSquareDecomp.carrier (.inl (1 : Fin 2))) :
    JoinedIn splitSquareF p q :=
  splitSquareDecomp.joinedIn_of_reachable hp hq splitSquare_reachable_through_wall

theorem splitSquare_joined_wall_trap (r p : plane)
    (hr : r ∈ splitSquareDecomp.carrier (.inr (0 : Fin 1)))
    (hp : p ∈ splitSquareDecomp.carrier (.inl (0 : Fin 2))) :
    JoinedIn splitSquareF r p :=
  splitSquareDecomp.joinedIn_of_adj_mem splitSquare_wall_adj_left hr hp

#print axioms TrapDecomp.joinedIn_of_reachable

/-!
Path-to-graph tests on the split-square fixture above, and the
two-component fixture. LaValle, Planning Algorithms, Sec. 6.2.2.
-/

def splitQI : plane := !₂[(0.5 : ℝ), 1]

def splitQG : plane := !₂[(1.5 : ℝ), 1]

theorem split_QI_mem_L : splitQI ∈ splitSquareLeft.carrier := by
  rw [mem_splitSquareLeft_carrier]
  simp [splitQI]
  norm_num

theorem split_QG_mem_R : splitQG ∈ splitSquareRight.carrier := by
  rw [mem_splitSquareRight_carrier]
  simp [splitQG]
  norm_num

theorem split_QI_mem_F : splitQI ∈ splitSquareF := by
  simp [splitQI, splitSquareF]
  norm_num

theorem split_QG_mem_F : splitQG ∈ splitSquareF := by
  simp [splitQG, splitSquareF]
  norm_num

theorem split_isOpen : IsOpen splitSquareF := by
  have e : splitSquareF
      = (fun p : plane => p 0) ⁻¹' Set.Ioo 0 2 ∩ (fun p : plane => p 1) ⁻¹' Set.Ioo 0 2 := by
    ext p
    simp only [splitSquareF, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_Ioo]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      exact ⟨h1, h2, h3, h4⟩
  have hc0 : Continuous fun p : plane => p 0 := by fun_prop
  have hc1 : Continuous fun p : plane => p 1 := by fun_prop
  rw [e]
  exact (hc0.isOpen_preimage _ isOpen_Ioo).inter (hc1.isOpen_preimage _ isOpen_Ioo)

theorem split_joined : JoinedIn splitSquareF splitQI splitQG := by
  have hconv : Convex ℝ splitSquareF := by
    intro a ha b hb x y hx hy hxy
    simp only [splitSquareF, Set.mem_ofPred_eq] at ha hb ⊢
    obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
    obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
    have h0 := (convex_Ioo (0 : ℝ) 2) ⟨ha1, ha2⟩ ⟨hb1, hb2⟩ hx hy hxy
    have h1 := (convex_Ioo (0 : ℝ) 2) ⟨ha3, ha4⟩ ⟨hb3, hb4⟩ hx hy hxy
    simp only [Set.mem_Ioo] at h0 h1
    exact ⟨h0.1, h0.2, h1.1, h1.2⟩
  have hne : splitSquareF.Nonempty := ⟨splitQI, split_QI_mem_F⟩
  exact (hconv.isPathConnected hne).joinedIn splitQI split_QI_mem_F splitQG
    split_QG_mem_F

theorem split_reachable : splitSquareDecomp.incidenceGraph.Reachable (.inl (0 : Fin 2)) (.inl (1 : Fin 2)) := by
  have hF : IsOpen splitSquareF := split_isOpen
  have hcI : splitQI ∈ splitSquareDecomp.carrier (.inl (0 : Fin 2)) := split_QI_mem_L
  have hcG : splitQG ∈ splitSquareDecomp.carrier (.inl (1 : Fin 2)) := split_QG_mem_R
  exact (splitSquareDecomp.reachable_iff_joinedIn hF hcI hcG).mpr split_joined

/-- Left square of the two-component fixture (0,1)×(0,1).
LaValle, Planning Algorithms, Sec. 6.2.2. -/
def twoTrapA : VTrap where
  x₁ := 0
  x₂ := 1
  bot := AffineMap.const ℝ ℝ (0 : ℝ)
  top := AffineMap.const ℝ ℝ (1 : ℝ)
  x₁_lt_x₂ := by norm_num
  bot_le_top₁ := by simp
  bot_le_top₂ := by simp
  nondegenerate := Or.inl (by simp)

/-- Right square of the two-component fixture (2,3)×(0,1). -/
def twoTrapB : VTrap where
  x₁ := 2
  x₂ := 3
  bot := AffineMap.const ℝ ℝ (0 : ℝ)
  top := AffineMap.const ℝ ℝ (1 : ℝ)
  x₁_lt_x₂ := by norm_num
  bot_le_top₁ := by simp
  bot_le_top₂ := by simp
  nondegenerate := Or.inl (by simp)

def twoTrapFun : Fin 2 → VTrap := ![twoTrapA, twoTrapB]

def twoWallFun : Fin 0 → VSeg := fun j => Fin.elim0 j

def twoF : Set plane := (⋃ i, (twoTrapFun i).carrier) ∪ (⋃ j, (twoWallFun j).carrier)

theorem two_disjoint_AB : Disjoint twoTrapA.carrier twoTrapB.carrier := by
  rw [Set.disjoint_left]
  intro p hpA hpB
  simp [twoTrapA, twoTrapB, VTrap.carrier] at hpA hpB
  linarith

def twoDecomp : TrapDecomp twoF where
  m := 2
  k := 0
  trap := twoTrapFun
  wall := twoWallFun
  pairwise_disjoint := by
    intro x y hne
    cases x with
    | inl i =>
      cases y with
      | inl i' =>
        fin_cases i <;> fin_cases i'
        · exact absurd rfl hne
        · exact two_disjoint_AB
        · exact two_disjoint_AB.symm
        · exact absurd rfl hne
      | inr j => nomatch j
    | inr j => nomatch j
  iUnion_eq := rfl

def twoQ0 : plane := !₂[(0.5 : ℝ), 0.5]

def twoQ1 : plane := !₂[(2.5 : ℝ), 0.5]

theorem two_Q0_mem_A : twoQ0 ∈ twoTrapA.carrier := by
  simp [twoQ0, twoTrapA, VTrap.carrier]
  norm_num

theorem two_Q1_mem_B : twoQ1 ∈ twoTrapB.carrier := by
  simp [twoQ1, twoTrapB, VTrap.carrier]
  norm_num

theorem two_Q0_mem_F : twoQ0 ∈ twoF := by
  simp only [twoF, Set.mem_union, Set.mem_iUnion]
  exact Or.inl ⟨0, two_Q0_mem_A⟩

theorem two_Q1_mem_F : twoQ1 ∈ twoF := by
  simp only [twoF, Set.mem_union, Set.mem_iUnion]
  exact Or.inl ⟨1, two_Q1_mem_B⟩

theorem two_isOpen : IsOpen twoF := by
  unfold twoF
  apply IsOpen.union
  · apply isOpen_iUnion
    intro i
    fin_cases i
    · exact twoTrapA.isOpen_carrier
    · exact twoTrapB.isOpen_carrier
  · apply isOpen_iUnion
    intro j
    nomatch j

/-- Cells in different components are not reachable: with no walls, no walk
leaves its start cell. -/
theorem two_not_reachable :
    ¬ twoDecomp.incidenceGraph.Reachable (.inl (0 : Fin 2)) (.inl (1 : Fin 2)) := by
  intro hreach
  have hall : ∀ c, twoDecomp.incidenceGraph.Reachable (.inl (0 : Fin 2)) c →
      c = (.inl (0 : Fin 2)) := by
    intro c h
    obtain ⟨w⟩ := h
    cases w with
    | nil => rfl
    | cons hadj _ =>
      have hno : ∀ mid, ¬ twoDecomp.incidenceGraph.Adj (.inl (0 : Fin 2)) mid := by
        intro mid
        cases mid with
        | inl _ => exact twoDecomp.incidenceGraph_not_adj_inl_inl _ _
        | inr j => nomatch j
      exact False.elim (hno _ hadj)
  have heq := hall _ hreach
  have h10 : (1 : Fin 2) = (0 : Fin 2) := Sum.inl.inj heq
  exact absurd h10 (by decide)

/-- Points in different components are not joined, via the iff and the graph
separation above: a path would give reachability. -/
theorem two_not_joined : ¬ JoinedIn twoF twoQ0 twoQ1 := by
  intro hjoined
  have hF : IsOpen twoF := two_isOpen
  have hcI : twoQ0 ∈ twoDecomp.carrier (.inl (0 : Fin 2)) := two_Q0_mem_A
  have hcG : twoQ1 ∈ twoDecomp.carrier (.inl (1 : Fin 2)) := two_Q1_mem_B
  have hreach := twoDecomp.reachable_of_joinedIn hF hcI hcG hjoined
  exact two_not_reachable hreach

#print axioms TrapDecomp.reachable_iff_joinedIn
#print axioms TrapDecomp.reachable_of_joinedIn

end Cslib.Planning.MotionPlanning.VerticalCellsTests
