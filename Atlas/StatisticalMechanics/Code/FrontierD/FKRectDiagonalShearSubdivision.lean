/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectTorusSquareDevelopment
import Code.Lattice.JordanExteriorClosure














open SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Universality

noncomputable section



def fkRectDiagonalShearPoint (p : Int × Int) : Site 2 :=
  ![p.1 + p.2, p.1 - p.2]


def fkRectDiagonalShearMidpoint (p q : Int × Int) : Site 2 :=
  ![(fkRectDiagonalShearPoint q) 0, (fkRectDiagonalShearPoint p) 1]

theorem fkRectDiagonalShearPoint_add (p u : Int × Int) :
    fkRectDiagonalShearPoint (p.1 + u.1, p.2 + u.2) =
      ![(fkRectDiagonalShearPoint p) 0 + u.1 + u.2,
        (fkRectDiagonalShearPoint p) 1 + u.1 - u.2] := by
  funext i
  fin_cases i <;> simp [fkRectDiagonalShearPoint] <;> ring

theorem fkRectDiagonalShearPoint_develop_snd
    (p : Int × Int) :
    (fkRectDiagonalShearPoint (fkRectSquareDevelopPoint p)) 1 = p.2 := by
  simp [fkRectDiagonalShearPoint,
    fkRectSquareDevelopPoint_fst_sub_snd]

theorem fkRectDiagonalShearPoint_develop_fst
    (p : Int × Int) :
    (fkRectDiagonalShearPoint (fkRectSquareDevelopPoint p)) 0 =
      2 * p.1 + (p.2 + 1) / 2 - p.2 / 2 := by
  simp [fkRectDiagonalShearPoint, fkRectSquareDevelopPoint]
  ring




theorem fkRectDiagonalShearPoint_develop_add_period
    (R : FKRectTorus) (p u : Int × Int) :
    fkRectDiagonalShearPoint
        (fkRectSquareDevelopPoint
          (p.1 + (R.width : Int) * u.1,
            p.2 + (R.height : Int) * u.2)) =
      ![(fkRectDiagonalShearPoint (fkRectSquareDevelopPoint p)) 0 +
          2 * (R.width : Int) * u.1,
        (fkRectDiagonalShearPoint (fkRectSquareDevelopPoint p)) 1 +
          (R.height : Int) * u.2] := by
  have h := fkRectSquareDevelopPoint_add_period R p u
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  simp only [Prod.fst_sub, Prod.snd_sub,
    fkRectSquareDeckTranslation] at hx hy
  have hhNat : 2 * (R.height / 2) = R.height :=
    Nat.two_mul_div_two_of_even R.height_even
  have hh : (2 : Int) * (R.height / 2 : Nat) = R.height := by
    exact_mod_cast hhNat
  have hhu : (2 : Int) * (R.height / 2 : Nat) * u.2 =
      (R.height : Int) * u.2 := by rw [hh]
  funext i
  fin_cases i
  · simp [fkRectDiagonalShearPoint]
    linear_combination hx + hy
  · simp [fkRectDiagonalShearPoint]
    linear_combination hx - hy + hhu



theorem FKRectSquareWalkLift.closed_diagonalShearPoint_end
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x : R.Vertex} {w : G.Walk x x} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q) :
    fkRectDiagonalShearPoint (fkRectSquareDevelopPoint q) =
      ![(fkRectDiagonalShearPoint (fkRectSquareDevelopPoint p)) 0 +
          2 * (R.width : Int) * (fkRectWalkWinding R w).1,
        (fkRectDiagonalShearPoint (fkRectSquareDevelopPoint p)) 1 +
          (R.height : Int) * (fkRectWalkWinding R w).2] := by
  rw [h.closed_end_eq_period_winding R]
  exact fkRectDiagonalShearPoint_develop_add_period
    R p (fkRectWalkWinding R w)

theorem FKRectSquareWalkLift.closed_diagonalShearPoint_end_of_verticalOne
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x : R.Vertex} {w : G.Walk x x} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q)
    (hw : fkRectWalkWinding R w = (0, 1)) :
    fkRectDiagonalShearPoint (fkRectSquareDevelopPoint q) =
      ![(fkRectDiagonalShearPoint (fkRectSquareDevelopPoint p)) 0,
        (fkRectDiagonalShearPoint (fkRectSquareDevelopPoint p)) 1 +
          (R.height : Int)] := by
  rw [h.closed_diagonalShearPoint_end R, hw]
  simp




theorem FKRectSquareWalkLift.end_fst_eq_val_of_support_positiveColumnBand
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x y : R.Vertex} {w : G.Walk x y} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q) (right : Nat)
    (hsupport : ∀ v ∈ w.support,
      1 ≤ v.1.val ∧ v.1.val ≤ right)
    (hp : p.1 = (x.1.val : Int)) :
    q.1 = (y.1.val : Int) := by
  induction h with
  | nil => exact hp
  | @cons a b c hab tail p q r hpa hqb hdisp haxis hlift ih =>
      have ha := hsupport a (by simp)
      have hb := hsupport b (by simp)
      have htail : ∀ v ∈ tail.support,
          1 ≤ v.1.val ∧ v.1.val ≤ right := by
        intro v hv
        exact hsupport v (by simp [hv])
      have hnot : ¬ fkRectCrossesHorizontalSeam R s(a, b) := by
        rw [fkRectCrossesHorizontalSeam_mk]
        push Not
        constructor <;> omega
      have hinc : fkRectHorizontalSeamIncrement R a b = 0 := by
        unfold fkRectHorizontalSeamIncrement
        by_cases hab : a.1.val + 1 = R.width ∧ b.1.val = 0
        · exact (hnot (Or.inr ⟨hab.2, hab.1⟩)).elim
        · by_cases hba : a.1.val = 0 ∧ b.1.val + 1 = R.width
          · exact (hnot (Or.inl hba)).elim
          · simp [hab, hba]
      have hq : q.1 = (b.1.val : Int) := by
        have hx := congrArg Prod.fst hdisp
        simp only [Prod.fst_sub, fkRectDevelopedStep] at hx
        rw [hinc] at hx
        simp only [mul_zero, add_zero] at hx
        omega
      exact ih htail hq

theorem fkRectDiagonalShearPoint_midpoint_adj
    {p q : Int × Int} (h : FKRectSquareAxisStep p q) :
    (hypercubicLattice 2).Adj (fkRectDiagonalShearPoint p)
      (fkRectDiagonalShearMidpoint p q) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  rcases h with h | h | h | h <;>
    have hx := congrArg Prod.fst h <;>
    have hy := congrArg Prod.snd h <;>
    simp [fkRectDiagonalShearPoint, fkRectDiagonalShearMidpoint] at * <;>
    omega

theorem fkRectDiagonalShearMidpoint_point_adj
    {p q : Int × Int} (h : FKRectSquareAxisStep p q) :
    (hypercubicLattice 2).Adj (fkRectDiagonalShearMidpoint p q)
      (fkRectDiagonalShearPoint q) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  rcases h with h | h | h | h <;>
    have hx := congrArg Prod.fst h <;>
    have hy := congrArg Prod.snd h <;>
    simp [fkRectDiagonalShearPoint, fkRectDiagonalShearMidpoint] at * <;>
    omega




theorem FKRectSquareWalkLift.exists_diagonalShearWalk
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x y : R.Vertex} {w : G.Walk x y} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q) :
    ∃ V : (hypercubicLattice 2).Walk
        (fkRectDiagonalShearPoint (fkRectSquareDevelopPoint p))
        (fkRectDiagonalShearPoint (fkRectSquareDevelopPoint q)),
      ∀ z ∈ V.support,
        (∃ a ∈ w.support, ∃ u : Int × Int,
          fkRectLiftedVertex R u = a ∧
            z = fkRectDiagonalShearPoint (fkRectSquareDevelopPoint u)) ∨
        ∃ a b, s(a, b) ∈ w.edges ∧ ∃ u v : Int × Int,
          fkRectLiftedVertex R u = a ∧ fkRectLiftedVertex R v = b ∧
            z = fkRectDiagonalShearMidpoint
              (fkRectSquareDevelopPoint u)
              (fkRectSquareDevelopPoint v) := by
  induction h with
  | nil p hp =>
      refine ⟨.nil, ?_⟩
      intro z hz
      simp only [Walk.support_nil, List.mem_singleton] at hz
      exact Or.inl ⟨_, by simp, p, hp, hz⟩
  | @cons x y t hxy w p q r hp hq hdisp haxis tail ih =>
      obtain ⟨V, hV⟩ := ih
      let W := SimpleGraph.Walk.cons
        (fkRectDiagonalShearPoint_midpoint_adj haxis)
        (SimpleGraph.Walk.cons
          (fkRectDiagonalShearMidpoint_point_adj haxis) V)
      refine ⟨W, ?_⟩
      intro z hz
      simp only [W, Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact Or.inl ⟨x, by simp, p, hp, rfl⟩
      · rcases hz with rfl | hz
        · exact Or.inr ⟨x, y, by simp, p, q, hp, hq, rfl⟩
        · rcases hV z hz with hvertex | hedge
          · obtain ⟨a, ha, u, hu, rfl⟩ := hvertex
            exact Or.inl ⟨a, by simp [ha], u, hu, rfl⟩
          · obtain ⟨a, b, hab, u, v, hu, hv, rfl⟩ := hedge
            exact Or.inr ⟨a, b, by simp [hab], u, v, hu, hv, rfl⟩


noncomputable def FKRectSquareWalkLift.diagonalShearWalk
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x y : R.Vertex} {w : G.Walk x y} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q) :
    (hypercubicLattice 2).Walk
      (fkRectDiagonalShearPoint (fkRectSquareDevelopPoint p))
      (fkRectDiagonalShearPoint (fkRectSquareDevelopPoint q)) :=
  Classical.choose (h.exists_diagonalShearWalk R)



theorem FKRectSquareWalkLift.diagonalShearWalk_support_cases
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x y : R.Vertex} {w : G.Walk x y} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q) {z : Site 2}
    (hz : z ∈ (h.diagonalShearWalk R).support) :
    (∃ a ∈ w.support, ∃ u : Int × Int,
      fkRectLiftedVertex R u = a ∧
        z = fkRectDiagonalShearPoint (fkRectSquareDevelopPoint u)) ∨
    ∃ a b, s(a, b) ∈ w.edges ∧ ∃ u v : Int × Int,
      fkRectLiftedVertex R u = a ∧ fkRectLiftedVertex R v = b ∧
        z = fkRectDiagonalShearMidpoint
          (fkRectSquareDevelopPoint u) (fkRectSquareDevelopPoint v) :=
  Classical.choose_spec (h.exists_diagonalShearWalk R) z hz

end

end StatMech.FrontierD
