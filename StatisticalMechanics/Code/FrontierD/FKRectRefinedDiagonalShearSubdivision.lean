/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectDiagonalShearSubdivision
import Code.FrontierD.FKRectTorusSquareCoverIntersection



open SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section



theorem fkRectIntegralSquareDart_axisStep
    (d : FKRectIntegralSquareDart) :
    FKRectSquareAxisStep d.1 (fkRectIntegralSquareDartEnd d) := by
  rcases d with ⟨⟨x, y⟩, mu⟩
  fin_cases mu <;>
    simp [FKRectSquareAxisStep, fkRectIntegralSquareDartEnd,
      StatMech.Onsager.ons_dirExponentX,
      StatMech.Onsager.ons_dirExponentY]




theorem FKRectIntegralSquareDartPath.exists_diagonalShearWalk
    {p q : Int × Int} {l : List FKRectIntegralSquareDart}
    (h : FKRectIntegralSquareDartPath p q l) :
    ∃ V : (hypercubicLattice 2).Walk
        (fkRectDiagonalShearPoint p) (fkRectDiagonalShearPoint q),
      ∀ z ∈ V.support,
        z = fkRectDiagonalShearPoint p ∨
          ∃ d ∈ l,
            z = fkRectDiagonalShearMidpoint
                d.1 (fkRectIntegralSquareDartEnd d) ∨
              z = fkRectDiagonalShearPoint
                (fkRectIntegralSquareDartEnd d) := by
  induction h with
  | nil p =>
      refine ⟨.nil, ?_⟩
      intro z hz
      simp only [Walk.support_nil, List.mem_singleton] at hz
      exact Or.inl hz
  | @cons d q r l hend tail ih =>
      obtain ⟨V, hV⟩ := ih
      have haxis := fkRectIntegralSquareDart_axisStep d
      rw [hend] at haxis
      let W := SimpleGraph.Walk.cons
        (fkRectDiagonalShearPoint_midpoint_adj haxis)
        (SimpleGraph.Walk.cons
          (fkRectDiagonalShearMidpoint_point_adj haxis) V)
      refine ⟨W, ?_⟩
      intro z hz
      simp only [W, Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact Or.inl rfl
      · rcases hz with rfl | hz
        · exact Or.inr ⟨d, by simp,
            Or.inl (by rw [hend])⟩
        · rcases hV z hz with hzstart | hzblock
          · exact Or.inr ⟨d, by simp,
              Or.inr (by rw [hend, hzstart])⟩
          · obtain ⟨e, he, hmid | hendPoint⟩ := hzblock
            · exact Or.inr ⟨e, by simp [he], Or.inl hmid⟩
            · exact Or.inr ⟨e, by simp [he], Or.inr hendPoint⟩


noncomputable def FKRectIntegralSquareDartPath.diagonalShearWalk
    {p q : Int × Int} {l : List FKRectIntegralSquareDart}
    (h : FKRectIntegralSquareDartPath p q l) :
    (hypercubicLattice 2).Walk
      (fkRectDiagonalShearPoint p) (fkRectDiagonalShearPoint q) :=
  Classical.choose h.exists_diagonalShearWalk


theorem FKRectIntegralSquareDartPath.diagonalShearWalk_support_cases
    {p q : Int × Int} {l : List FKRectIntegralSquareDart}
    (h : FKRectIntegralSquareDartPath p q l) {z : Site 2}
    (hz : z ∈ h.diagonalShearWalk.support) :
    z = fkRectDiagonalShearPoint p ∨
      ∃ d ∈ l,
        z = fkRectDiagonalShearMidpoint
            d.1 (fkRectIntegralSquareDartEnd d) ∨
          z = fkRectDiagonalShearPoint
            (fkRectIntegralSquareDartEnd d) :=
  Classical.choose_spec h.exists_diagonalShearWalk z hz

end

end StatMech.FrontierD
