/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.AlgebraicTopology.Quasicategory.NativePullback.Shapes
import all MathlibExt.AlgebraicTopology.Quasicategory.NativePullback.Shapes
public import MathlibExt.AlgebraicTopology.SimplicialSet.NervePreorderSubtype
public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinNaturality
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.Tactic.FinCases

/-!
# The original diamond as the cone on its cospan

The cospan is the pushout of its two original edge charts over the target
vertex. The diamond is the pushout of its two original triangle charts over
the initial-to-target diagonal. These are pushouts of whole simplicial sets,
including their simplices in every degree.
-/

noncomputable section

public section

set_option autoImplicit false

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace SSet.NativePullback.Coordinate


/-- The original right branch, including its full nerve edge. -/
private def cospanRightChart : (Δ[1] : SSet.{u}) ⟶ cospanShape.{u} :=
  yonedaEquiv.symm (ComposableArrows.mk₁
    (homOfLE (show (⟨⟨(1, 0)⟩, by decide⟩ : CospanObjects.{u}) ≤
        ⟨⟨(1, 1)⟩, by decide⟩ from ⟨le_rfl, by decide⟩)))

/-- The original left branch, including its full nerve edge. -/
private def cospanLeftChart : (Δ[1] : SSet.{u}) ⟶ cospanShape.{u} :=
  yonedaEquiv.symm (ComposableArrows.mk₁
    (homOfLE (show (⟨⟨(0, 1)⟩, by decide⟩ : CospanObjects.{u}) ≤
        ⟨⟨(1, 1)⟩, by decide⟩ from ⟨by decide, le_rfl⟩)))

/-- The original shared target vertex of the cospan. -/
private def cospanTerminalPoint : (Δ[0] : SSet.{u}) ⟶ cospanShape.{u} :=
  yonedaEquiv.symm (ComposableArrows.mk₀
    (⟨⟨(1, 1)⟩, by decide⟩ : CospanObjects.{u}))

/-- The original triangle through the right branch of the diamond. -/
private def rightTriangle : (Δ[2] : SSet.{u}) ⟶ squareShape.{u} :=
  yonedaEquiv.symm (ComposableArrows.mk₂
    (homOfLE (show (⟨(0, 0)⟩ : DiamondObjects.{u}) ≤ ⟨(1, 0)⟩ from
      ⟨by decide, le_rfl⟩))
    (homOfLE (show (⟨(1, 0)⟩ : DiamondObjects.{u}) ≤ ⟨(1, 1)⟩ from
      ⟨le_rfl, by decide⟩)))

/-- The original triangle through the left branch of the diamond. -/
private def leftTriangle : (Δ[2] : SSet.{u}) ⟶ squareShape.{u} :=
  yonedaEquiv.symm (ComposableArrows.mk₂
    (homOfLE (show (⟨(0, 0)⟩ : DiamondObjects.{u}) ≤ ⟨(0, 1)⟩ from
      ⟨le_rfl, by decide⟩))
    (homOfLE (show (⟨(0, 1)⟩ : DiamondObjects.{u}) ≤ ⟨(1, 1)⟩ from
      ⟨by decide, le_rfl⟩)))

/-- The original common diagonal from the initial vertex to the target. -/
private def diagonal : (Δ[1] : SSet.{u}) ⟶ squareShape.{u} :=
  edge ⟨(0, 0)⟩ ⟨(1, 1)⟩ ⟨by decide, by decide⟩

private def rightP (v : DiamondObjects.{u}) : Prop := v.down.2 ≤ v.down.1

private def leftP (v : DiamondObjects.{u}) : Prop := v.down.1 ≤ v.down.2

private def squareRightSupport : squareShape.{u}.Subcomplex :=
  preorderSubtypeSubcomplex rightP

private def squareLeftSupport : squareShape.{u}.Subcomplex :=
  preorderSubtypeSubcomplex leftP

private def cospanRightSupport : cospanShape.{u}.Subcomplex :=
  preorderSubtypeSubcomplex (fun v : CospanObjects.{u} => rightP v.val)

private def cospanLeftSupport : cospanShape.{u}.Subcomplex :=
  preorderSubtypeSubcomplex (fun v : CospanObjects.{u} => leftP v.val)

private def supportChartIso {A : Type u} [Preorder A] {n : ℕ}
    (P : A → Prop) (e : Fin (n + 1) ≃o {a : A // P a}) :
    (Δ[n] : SSet.{u}) ≅ (preorderSubtypeSubcomplex P : SSet.{u}) :=
  stdSimplex.isoOfRepresentableBy (nerve.representableBy _ e.symm) ≪≫
    nervePreorderSubtypeIso P

private def rightTriangleVertices : Fin 3 → DiamondObjects.{u} :=
  ![⟨(0, 0)⟩, ⟨(1, 0)⟩, ⟨(1, 1)⟩]

private def leftTriangleVertices : Fin 3 → DiamondObjects.{u} :=
  ![⟨(0, 0)⟩, ⟨(0, 1)⟩, ⟨(1, 1)⟩]

private def squareRightOrderIso : Fin 3 ≃o {v : DiamondObjects.{u} // rightP v} where
  toFun i := ⟨rightTriangleVertices i, by
    fin_cases i <;> dsimp [rightP, rightTriangleVertices] <;> decide⟩
  invFun v := ⟨v.val.down.1.val + v.val.down.2.val, by
    have ha := v.val.down.1.isLt
    have hb := v.val.down.2.isLt
    omega⟩
  left_inv i := by fin_cases i <;> rfl
  right_inv v := by
    rcases v with ⟨⟨⟨a, b⟩⟩, h⟩
    change b.val ≤ a.val at h
    fin_cases a <;> fin_cases b <;>
      first | rfl | exact ((by decide : ¬ ((1 : ℕ) ≤ 0)) h).elim
  map_rel_iff' := by
    intro i j
    change ((rightTriangleVertices i).down.1 ≤ (rightTriangleVertices j).down.1 ∧
      (rightTriangleVertices i).down.2 ≤ (rightTriangleVertices j).down.2) ↔ i ≤ j
    fin_cases i <;> fin_cases j <;> dsimp [rightTriangleVertices] <;> decide

private def squareLeftOrderIso : Fin 3 ≃o {v : DiamondObjects.{u} // leftP v} where
  toFun i := ⟨leftTriangleVertices i, by
    fin_cases i <;> dsimp [leftP, leftTriangleVertices] <;> decide⟩
  invFun v := ⟨v.val.down.1.val + v.val.down.2.val, by
    have ha := v.val.down.1.isLt
    have hb := v.val.down.2.isLt
    omega⟩
  left_inv i := by fin_cases i <;> rfl
  right_inv v := by
    rcases v with ⟨⟨⟨a, b⟩⟩, h⟩
    change a.val ≤ b.val at h
    fin_cases a <;> fin_cases b <;>
      first | rfl | exact ((by decide : ¬ ((1 : ℕ) ≤ 0)) h).elim
  map_rel_iff' := by
    intro i j
    change ((leftTriangleVertices i).down.1 ≤ (leftTriangleVertices j).down.1 ∧
      (leftTriangleVertices i).down.2 ≤ (leftTriangleVertices j).down.2) ↔ i ≤ j
    fin_cases i <;> fin_cases j <;> dsimp [leftTriangleVertices] <;> decide

private def squareDiagonalOrderIso :
    Fin 2 ≃o {v : DiamondObjects.{u} // rightP v ∧ leftP v} where
  toFun i := ⟨⟨(i, i)⟩, ⟨le_rfl, le_rfl⟩⟩
  invFun v := v.val.down.1
  left_inv _ := rfl
  right_inv v := by
    apply Subtype.ext
    apply ULift.ext
    apply Prod.ext
    · rfl
    · exact le_antisymm v.property.2 v.property.1
  map_rel_iff' := by
    intro i j
    change (i ≤ j ∧ i ≤ j) ↔ i ≤ j
    simp

private def cospanRightOrderIso :
    Fin 2 ≃o {v : CospanObjects.{u} // rightP v.val} where
  toFun i := ⟨⟨⟨(1, i)⟩, by simp⟩, Fin.le_last i⟩
  invFun v := v.val.val.down.2
  left_inv _ := rfl
  right_inv v := by
    rcases v with ⟨⟨⟨⟨a, b⟩⟩, hn⟩, h⟩
    change b.val ≤ a.val at h
    change (a, b) ≠ (0, 0) at hn
    fin_cases a <;> fin_cases b <;>
      first | rfl | exact ((by decide : ¬ ((1 : ℕ) ≤ 0)) h).elim | exact (hn rfl).elim
  map_rel_iff' := by
    intro i j
    change ((1 : Fin 2) ≤ 1 ∧ i ≤ j) ↔ i ≤ j
    simp

private def cospanLeftOrderIso :
    Fin 2 ≃o {v : CospanObjects.{u} // leftP v.val} where
  toFun i := ⟨⟨⟨(i, 1)⟩, by simp⟩, Fin.le_last i⟩
  invFun v := v.val.val.down.1
  left_inv _ := rfl
  right_inv v := by
    rcases v with ⟨⟨⟨⟨a, b⟩⟩, hn⟩, h⟩
    change a.val ≤ b.val at h
    change (a, b) ≠ (0, 0) at hn
    fin_cases a <;> fin_cases b <;>
      first | rfl | exact ((by decide : ¬ ((1 : ℕ) ≤ 0)) h).elim | exact (hn rfl).elim
  map_rel_iff' := by
    intro i j
    change (i ≤ j ∧ (1 : Fin 2) ≤ 1) ↔ i ≤ j
    simp

private def cospanTerminalOrderIso :
    Fin 1 ≃o {v : CospanObjects.{u} // rightP v.val ∧ leftP v.val} where
  toFun _ := ⟨⟨⟨(1, 1)⟩, by decide⟩, ⟨le_rfl, le_rfl⟩⟩
  invFun _ := 0
  left_inv i := by fin_cases i; rfl
  right_inv v := by
    rcases v with ⟨⟨⟨⟨a, b⟩⟩, hn⟩, h⟩
    change b.val ≤ a.val ∧ a.val ≤ b.val at h
    change (a, b) ≠ (0, 0) at hn
    fin_cases a <;> fin_cases b
    all_goals
      first
      | rfl
      | exact (hn rfl).elim
      | exact ((by decide : ¬ ((1 : ℕ) ≤ 0)) h.1).elim
      | exact ((by decide : ¬ ((1 : ℕ) ≤ 0)) h.2).elim
  map_rel_iff' := by
    intro i j
    change (((1 : Fin 2) ≤ 1 ∧ (1 : Fin 2) ≤ 1) ↔ i ≤ j)
    fin_cases i
    fin_cases j
    decide

private def squareRightIso : (Δ[2] : SSet.{u}) ≅ (squareRightSupport : SSet.{u}) :=
  supportChartIso rightP squareRightOrderIso

private def squareLeftIso : (Δ[2] : SSet.{u}) ≅ (squareLeftSupport : SSet.{u}) :=
  supportChartIso leftP squareLeftOrderIso

private def cospanRightIso : (Δ[1] : SSet.{u}) ≅ (cospanRightSupport : SSet.{u}) :=
  supportChartIso (fun v : CospanObjects.{u} => rightP v.val) cospanRightOrderIso

private def cospanLeftIso : (Δ[1] : SSet.{u}) ≅ (cospanLeftSupport : SSet.{u}) :=
  supportChartIso (fun v : CospanObjects.{u} => leftP v.val) cospanLeftOrderIso

private theorem supportedNerve_inf {A : Type u} [Preorder A] (P Q : A → Prop) :
    preorderSubtypeSubcomplex (fun a => P a ∧ Q a) =
      preorderSubtypeSubcomplex P ⊓ preorderSubtypeSubcomplex Q := by
  ext q x
  exact forall_and

private def squareDiagonalIso :
    (Δ[1] : SSet.{u}) ≅ (squareRightSupport ⊓ squareLeftSupport).toSSet :=
  supportChartIso (fun v => rightP v ∧ leftP v) squareDiagonalOrderIso ≪≫
    Subcomplex.eqToIso (supportedNerve_inf rightP leftP)

private def cospanTerminalIso :
    (Δ[0] : SSet.{u}) ≅ (cospanRightSupport ⊓ cospanLeftSupport).toSSet :=
  supportChartIso (fun v : CospanObjects.{u} => rightP v.val ∧ leftP v.val)
      cospanTerminalOrderIso ≪≫
    Subcomplex.eqToIso (supportedNerve_inf
      (fun v : CospanObjects.{u} => rightP v.val)
      (fun v : CospanObjects.{u} => leftP v.val))

private theorem diamondWord_cover {n : ℕ} (x : ComposableArrows DiamondObjects.{u} n) :
    (∀ i, rightP (x.obj i)) ∨ (∀ i, leftP (x.obj i)) := by
  classical
  by_cases h : ∀ i, rightP (x.obj i)
  · exact Or.inl h
  · right
    obtain ⟨i, hi⟩ := not_forall.mp h
    change ¬ (x.obj i).down.2.val ≤ (x.obj i).down.1.val at hi
    intro j
    by_contra hj
    change ¬ (x.obj j).down.1.val ≤ (x.obj j).down.2.val at hj
    have ha := (x.obj i).down.1.isLt
    have hb := (x.obj i).down.2.isLt
    have hc := (x.obj j).down.1.isLt
    have hd := (x.obj j).down.2.isLt
    rcases le_total i j with hij | hji
    · have hle := leOfHom (x.map (homOfLE hij))
      change (x.obj i).down.1.val ≤ (x.obj j).down.1.val ∧
        (x.obj i).down.2.val ≤ (x.obj j).down.2.val at hle
      omega
    · have hle := leOfHom (x.map (homOfLE hji))
      change (x.obj j).down.1.val ≤ (x.obj i).down.1.val ∧
        (x.obj j).down.2.val ≤ (x.obj i).down.2.val at hle
      omega

private theorem squareSupport_cover :
    squareRightSupport.{u} ⊔ squareLeftSupport = ⊤ := by
  refine le_antisymm le_top ?_
  intro q x _
  exact diamondWord_cover x

private theorem cospanSupport_cover :
    cospanRightSupport.{u} ⊔ cospanLeftSupport = ⊤ := by
  refine le_antisymm le_top ?_
  intro q x _
  exact diamondWord_cover (x ⋙ cospanInclusionFunctor)

private theorem squareRightIso_inclusion :
    squareRightIso.{u}.hom ≫ squareRightSupport.ι = rightTriangle := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

private theorem squareLeftIso_inclusion :
    squareLeftIso.{u}.hom ≫ squareLeftSupport.ι = leftTriangle := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

private theorem squareDiagonalIso_inclusion :
    squareDiagonalIso.{u}.hom ≫ (squareRightSupport ⊓ squareLeftSupport).ι = diagonal := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

private theorem cospanRightIso_inclusion :
    cospanRightIso.{u}.hom ≫ cospanRightSupport.ι = cospanRightChart := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

private theorem cospanLeftIso_inclusion :
    cospanLeftIso.{u}.hom ≫ cospanLeftSupport.ι = cospanLeftChart := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

private theorem cospanTerminalIso_inclusion :
    cospanTerminalIso.{u}.hom ≫ (cospanRightSupport ⊓ cospanLeftSupport).ι =
      cospanTerminalPoint := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i
  rfl

/-- Both original cospan edges have the same original target vertex. -/
private theorem cospanRightChart_terminal :
    stdSimplex.δ (0 : Fin 2) ≫ cospanRightChart.{u} = cospanTerminalPoint := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i
  rfl

/-- The left original cospan edge ends at the original shared target. -/
private theorem cospanLeftChart_terminal :
    stdSimplex.δ (0 : Fin 2) ≫ cospanLeftChart.{u} = cospanTerminalPoint := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i
  rfl

/-- The complete right triangle restricts to the original common diagonal. -/
private theorem rightTriangle_diagonal :
    stdSimplex.δ (1 : Fin 3) ≫ rightTriangle.{u} = diagonal := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

/-- The complete left triangle restricts to the same original diagonal. -/
private theorem leftTriangle_diagonal :
    stdSimplex.δ (1 : Fin 3) ≫ leftTriangle.{u} = diagonal := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

/-- The original right cospan chart is the entire target-facing edge of its triangle. -/
private theorem cospanRightChart_inclusion :
    cospanRightChart.{u} ≫ cospanInclusion = stdSimplex.δ (0 : Fin 3) ≫ rightTriangle := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

/-- The original left cospan chart is the entire target-facing edge of its triangle. -/
private theorem cospanLeftChart_inclusion :
    cospanLeftChart.{u} ≫ cospanInclusion = stdSimplex.δ (0 : Fin 3) ≫ leftTriangle := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

/-- The right cospan chart keeps the original right vertical square edge. -/
private theorem cospanRightChart_comp_inclusion :
    cospanRightChart.{u} ≫ cospanInclusion = rightEdge := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

/-- The left cospan chart keeps the original lower horizontal square edge. -/
private theorem cospanLeftChart_comp_inclusion :
    cospanLeftChart.{u} ≫ cospanInclusion = bottomEdge := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

/-- The original shared cospan target stays the original terminal square vertex. -/
private theorem cospanTerminalPoint_comp_inclusion :
    cospanTerminalPoint.{u} ≫ cospanInclusion = point ⟨(1, 1)⟩ := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i
  rfl

/-- The source-facing edge of the right triangle is the original upper square edge. -/
private theorem rightTriangle_topEdge :
    stdSimplex.δ (2 : Fin 3) ≫ rightTriangle.{u} = topEdge := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

/-- The source-facing edge of the left triangle is the original left square edge. -/
private theorem leftTriangle_leftEdge :
    stdSimplex.δ (2 : Fin 3) ≫ leftTriangle.{u} = leftEdge := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

/-- The initial vertex of the original right triangle is the initial diamond vertex. -/
private theorem rightTriangle_initial :
    stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋2⦌ 0) ≫ rightTriangle.{u} =
      point ⟨(0, 0)⟩ := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i
  rfl

/-- The whole original cospan is the pushout of its two edge charts at their target. -/
private theorem cospanShape_isPushout :
    IsPushout (stdSimplex.δ (0 : Fin 2)) (stdSimplex.δ (0 : Fin 2))
      cospanRightChart.{u} cospanLeftChart := by
  have h := Subcomplex.BicartSq.isPushout
    (show Subcomplex.BicartSq (cospanRightSupport ⊓ cospanLeftSupport)
      cospanRightSupport cospanLeftSupport (⊤ : cospanShape.{u}.Subcomplex) from
        { sup_eq := cospanSupport_cover, inf_eq := rfl })
  apply h.of_iso' cospanTerminalIso cospanRightIso cospanLeftIso
    (Subcomplex.topIso cospanShape).symm
  · apply (cancel_mono cospanRightSupport.ι).1
    simp only [Category.assoc, Subcomplex.homOfLE_ι, cospanTerminalIso_inclusion,
      cospanRightIso_inclusion, cospanRightChart_terminal]
  · apply (cancel_mono cospanLeftSupport.ι).1
    simp only [Category.assoc, Subcomplex.homOfLE_ι, cospanTerminalIso_inclusion,
      cospanLeftIso_inclusion, cospanLeftChart_terminal]
  · apply (cancel_mono (Subcomplex.topIso cospanShape).hom).1
    simp only [Category.assoc, Iso.symm_hom, Subcomplex.topIso_hom,
      Subcomplex.homOfLE_ι, Subcomplex.topIso_inv_ι, Category.comp_id,
      cospanRightIso_inclusion]
  · apply (cancel_mono (Subcomplex.topIso cospanShape).hom).1
    simp only [Category.assoc, Iso.symm_hom, Subcomplex.topIso_hom,
      Subcomplex.homOfLE_ι, Subcomplex.topIso_inv_ι, Category.comp_id,
      cospanLeftIso_inclusion]

/-- The whole original diamond is the pushout of its two triangle charts along the diagonal. -/
private theorem squareShape_isPushout :
    IsPushout (stdSimplex.δ (1 : Fin 3)) (stdSimplex.δ (1 : Fin 3))
      rightTriangle.{u} leftTriangle := by
  have h := Subcomplex.BicartSq.isPushout
    (show Subcomplex.BicartSq (squareRightSupport ⊓ squareLeftSupport)
      squareRightSupport squareLeftSupport (⊤ : squareShape.{u}.Subcomplex) from
        { sup_eq := squareSupport_cover, inf_eq := rfl })
  apply h.of_iso' squareDiagonalIso squareRightIso squareLeftIso
    (Subcomplex.topIso squareShape).symm
  · apply (cancel_mono squareRightSupport.ι).1
    simp only [Category.assoc, Subcomplex.homOfLE_ι, squareDiagonalIso_inclusion,
      squareRightIso_inclusion, rightTriangle_diagonal]
  · apply (cancel_mono squareLeftSupport.ι).1
    simp only [Category.assoc, Subcomplex.homOfLE_ι, squareDiagonalIso_inclusion,
      squareLeftIso_inclusion, leftTriangle_diagonal]
  · apply (cancel_mono (Subcomplex.topIso squareShape).hom).1
    simp only [Category.assoc, Iso.symm_hom, Subcomplex.topIso_hom,
      Subcomplex.homOfLE_ι, Subcomplex.topIso_inv_ι, Category.comp_id,
      squareRightIso_inclusion]
  · apply (cancel_mono (Subcomplex.topIso squareShape).hom).1
    simp only [Category.assoc, Iso.symm_hom, Subcomplex.topIso_hom,
      Subcomplex.homOfLE_ι, Subcomplex.topIso_inv_ι, Category.comp_id,
      squareLeftIso_inclusion]

/-- The original cospan inclusion is degreewise injective on complete nerve words. -/
private instance cospanInclusion_mono : Mono cospanInclusion.{u} := by
  rw [NatTrans.mono_iff_mono_app]
  intro q
  rw [mono_iff_injective]
  intro x y h
  apply nerve.ext_of_isThin
  funext i
  apply Subtype.ext
  exact congrArg (fun z : squareShape.{u}.obj q => z.obj i) h

private def rightJoinedChart :
    (Δ[2] : SSet.{u}) ⟶ (Δ[0] : SSet.{u}) ⋆ cospanShape.{u} :=
  (joinStdSimplexIso 0 1).inv ≫ (join.obj (Δ[0] : SSet.{u})).map cospanRightChart

private def leftJoinedChart :
    (Δ[2] : SSet.{u}) ⟶ (Δ[0] : SSet.{u}) ⋆ cospanShape.{u} :=
  (joinStdSimplexIso 0 1).inv ≫ (join.obj (Δ[0] : SSet.{u})).map cospanLeftChart

private theorem join_terminalFace :
    (join.obj (Δ[0] : SSet.{u})).map (stdSimplex.δ (0 : Fin 2)) ≫
        (joinStdSimplexIso 0 1).hom =
      (joinStdSimplexIso 0 0).hom ≫ stdSimplex.δ (1 : Fin 3) := by
  have he : AugmentedSimplexCategory.tensorHomOf (𝟙 ⦋0⦌)
      (SimplexCategory.δ (0 : Fin 2)) = SimplexCategory.δ (1 : Fin 3) := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext i
    fin_cases i <;> rfl
  have h := joinStdSimplexIso_natural_right.{u} (m := 0)
    (SimplexCategory.δ (0 : Fin 2))
  rw [he] at h
  exact h

private theorem joinedShape_isPushout :
    IsPushout (stdSimplex.δ (1 : Fin 3)) (stdSimplex.δ (1 : Fin 3))
      rightJoinedChart.{u} leftJoinedChart := by
  have h := (join.obj (Δ[0] : SSet.{u})).map_isPushout cospanShape_isPushout
  apply h.of_iso (joinStdSimplexIso 0 0) (joinStdSimplexIso 0 1)
    (joinStdSimplexIso 0 1) (Iso.refl _)
  · exact join_terminalFace
  · exact join_terminalFace
  · simp only [Iso.refl_hom, Category.comp_id, rightJoinedChart, Iso.hom_inv_id_assoc]
  · simp only [Iso.refl_hom, Category.comp_id, leftJoinedChart, Iso.hom_inv_id_assoc]

/-- The complete original diamond is the simplicial join of its initial point and its cospan. -/
private def shapeJoinIso : squareShape.{u} ≅ (Δ[0] : SSet.{u}) ⋆ cospanShape.{u} :=
  squareShape_isPushout.isoIsPushout _ _ joinedShape_isPushout

/-- The join comparison retains the complete original right triangle chart. -/
private theorem rightTriangle_comp_shapeJoinIso_hom :
    rightTriangle.{u} ≫ shapeJoinIso.hom =
      (joinStdSimplexIso 0 1).inv ≫ (join.obj (Δ[0] : SSet.{u})).map cospanRightChart :=
  squareShape_isPushout.inl_isoIsPushout_hom _ _ joinedShape_isPushout

/-- The join comparison retains the complete original left triangle chart. -/
private theorem leftTriangle_comp_shapeJoinIso_hom :
    leftTriangle.{u} ≫ shapeJoinIso.hom =
      (joinStdSimplexIso 0 1).inv ≫ (join.obj (Δ[0] : SSet.{u})).map cospanLeftChart :=
  squareShape_isPushout.inr_isoIsPushout_hom _ _ joinedShape_isPushout

private theorem triangleRightFace_inv :
    stdSimplex.δ (0 : Fin 3) ≫ (joinStdSimplexIso.{u} 0 1).inv =
      joinInr (Δ[0] : SSet.{u}) Δ[1] := by
  have he : AugmentedSimplexCategory.inr' ⦋0⦌ ⦋1⦌ =
      SimplexCategory.δ (0 : Fin 3) := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext i
    fin_cases i <;> rfl
  have h := joinInr_comp_joinStdSimplexIso_hom.{u} 0 1
  rw [he] at h
  rw [stdSimplex_δ_eq_map, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem triangleInitialVertex_inv :
    stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋2⦌ 0) ≫
        (joinStdSimplexIso.{u} 0 1).inv =
      joinInl (Δ[0] : SSet.{u}) Δ[1] := by
  have he : AugmentedSimplexCategory.inl' ⦋0⦌ ⦋1⦌ =
      SimplexCategory.const ⦋0⦌ ⦋2⦌ 0 := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext i
    fin_cases i
    rfl
  have h := joinInl_comp_joinStdSimplexIso_hom.{u} 0 1
  rw [he] at h
  rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The original whole cospan inclusion is exactly the right join inclusion. -/
private theorem cospanInclusion_comp_shapeJoinIso_hom :
    cospanInclusion.{u} ≫ shapeJoinIso.hom = joinInr (Δ[0] : SSet.{u}) cospanShape := by
  apply cospanShape_isPushout.hom_ext
  · calc
      cospanRightChart ≫ (cospanInclusion ≫ shapeJoinIso.hom) =
          stdSimplex.δ (0 : Fin 3) ≫ (rightTriangle ≫ shapeJoinIso.hom) := by
        rw [← Category.assoc, cospanRightChart_inclusion, Category.assoc]
      _ = stdSimplex.δ (0 : Fin 3) ≫
          ((joinStdSimplexIso 0 1).inv ≫
            (join.obj (Δ[0] : SSet.{u})).map cospanRightChart) := by
        rw [rightTriangle_comp_shapeJoinIso_hom]
      _ = joinInr (Δ[0] : SSet.{u}) Δ[1] ≫
          (join.obj (Δ[0] : SSet.{u})).map cospanRightChart := by
        rw [← Category.assoc, triangleRightFace_inv]
      _ = cospanRightChart ≫ joinInr (Δ[0] : SSet.{u}) cospanShape :=
        (map_comp_joinInr cospanRightChart (Δ[0] : SSet.{u})).symm
  · calc
      cospanLeftChart ≫ (cospanInclusion ≫ shapeJoinIso.hom) =
          stdSimplex.δ (0 : Fin 3) ≫ (leftTriangle ≫ shapeJoinIso.hom) := by
        rw [← Category.assoc, cospanLeftChart_inclusion, Category.assoc]
      _ = stdSimplex.δ (0 : Fin 3) ≫
          ((joinStdSimplexIso 0 1).inv ≫
            (join.obj (Δ[0] : SSet.{u})).map cospanLeftChart) := by
        rw [leftTriangle_comp_shapeJoinIso_hom]
      _ = joinInr (Δ[0] : SSet.{u}) Δ[1] ≫
          (join.obj (Δ[0] : SSet.{u})).map cospanLeftChart := by
        rw [← Category.assoc, triangleRightFace_inv]
      _ = cospanLeftChart ≫ joinInr (Δ[0] : SSet.{u}) cospanShape :=
        (map_comp_joinInr cospanLeftChart (Δ[0] : SSet.{u})).symm

/-- The original initial vertex is exactly the left join inclusion. -/
private theorem initialPoint_comp_shapeJoinIso_hom :
    point (ULift.up (0, 0)) ≫ shapeJoinIso.{u}.hom =
      joinInl (Δ[0] : SSet.{u}) cospanShape := by
  calc
    point (ULift.up (0, 0)) ≫ shapeJoinIso.hom =
        stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋2⦌ 0) ≫
          (rightTriangle ≫ shapeJoinIso.hom) := by
      rw [← Category.assoc, rightTriangle_initial]
    _ = stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋2⦌ 0) ≫
        ((joinStdSimplexIso 0 1).inv ≫
          (join.obj (Δ[0] : SSet.{u})).map cospanRightChart) := by
      rw [rightTriangle_comp_shapeJoinIso_hom]
    _ = joinInl (Δ[0] : SSet.{u}) Δ[1] ≫
        (join.obj (Δ[0] : SSet.{u})).map cospanRightChart := by
      rw [← Category.assoc, triangleInitialVertex_inv]
    _ = joinInl (Δ[0] : SSet.{u}) cospanShape :=
      joinInl_comp_map (Δ[0] : SSet.{u}) cospanRightChart


end SSet.NativePullback.Coordinate

namespace SSet.NativePullback

/-- The whole first arrow of the standard walking cospan. -/
@[expose] def cospanRightChart : (Δ[1] : SSet.{u}) ⟶ cospanShape.{u} :=
  yonedaEquiv.symm (ComposableArrows.mk₁
    (show (ULift.up WalkingCospan.left : CospanObjects.{u}) ⟶ ULift.up WalkingCospan.one from
      WalkingCospan.Hom.inl))

/-- The whole second arrow of the standard walking cospan. -/
@[expose] def cospanLeftChart : (Δ[1] : SSet.{u}) ⟶ cospanShape.{u} :=
  yonedaEquiv.symm (ComposableArrows.mk₁
    (show (ULift.up WalkingCospan.right : CospanObjects.{u}) ⟶ ULift.up WalkingCospan.one from
      WalkingCospan.Hom.inr))

/-- The common target point of the standard walking cospan. -/
@[expose] def cospanTerminalPoint : (Δ[0] : SSet.{u}) ⟶ cospanShape.{u} :=
  yonedaEquiv.symm (ComposableArrows.mk₀ (ULift.up WalkingCospan.one : CospanObjects.{u}))

/-- The full triangle through the first branch and the common diagonal. -/
@[expose] def rightTriangle : (Δ[2] : SSet.{u}) ⟶ squareShape.{u} :=
  yonedaEquiv.symm (ComposableArrows.mk₂
    (WithInitial.homTo (ULift.up WalkingCospan.left))
    (WithInitial.incl.map (show (ULift.up WalkingCospan.left : CospanObjects.{u}) ⟶
      ULift.up WalkingCospan.one from WalkingCospan.Hom.inl)))

/-- The full triangle through the second branch and the same common diagonal. -/
@[expose] def leftTriangle : (Δ[2] : SSet.{u}) ⟶ squareShape.{u} :=
  yonedaEquiv.symm (ComposableArrows.mk₂
    (WithInitial.homTo (ULift.up WalkingCospan.right))
    (WithInitial.incl.map (show (ULift.up WalkingCospan.right : CospanObjects.{u}) ⟶
      ULift.up WalkingCospan.one from WalkingCospan.Hom.inr)))

/-- The unique native arrow from the adjoined initial object to the common target. -/
@[expose] def diagonal : (Δ[1] : SSet.{u}) ⟶ squareShape.{u} :=
  edge (WithInitial.homTo (ULift.up WalkingCospan.one))

/-- The full standard cospan embeds in its initial-object completion. -/
instance cospanInclusion_mono : Mono cospanInclusion.{u} := by
  rw [NatTrans.mono_iff_mono_app]
  intro q
  rw [mono_iff_injective]
  intro x y h
  apply nerve.ext_of_isThin
  funext i
  exact WithInitial.of.inj (congrArg (fun s => s.obj i) h)

private theorem cospanRightChart_toCanonical :
    Coordinate.cospanRightChart.{u} ≫ Coordinate.cospanIso.hom = cospanRightChart := by
  erw [Coordinate.cospanRightChart, yonedaEquiv_symm_comp, cospanRightChart]
  apply congrArg yonedaEquiv.symm
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

private theorem cospanLeftChart_toCanonical :
    Coordinate.cospanLeftChart.{u} ≫ Coordinate.cospanIso.hom = cospanLeftChart := by
  erw [Coordinate.cospanLeftChart, yonedaEquiv_symm_comp, cospanLeftChart]
  apply congrArg yonedaEquiv.symm
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

private theorem cospanTerminalPoint_toCanonical :
    Coordinate.cospanTerminalPoint.{u} ≫ Coordinate.cospanIso.hom = cospanTerminalPoint := by
  erw [Coordinate.cospanTerminalPoint, yonedaEquiv_symm_comp, cospanTerminalPoint]
  apply congrArg yonedaEquiv.symm
  apply nerve.ext_of_isThin
  funext i
  fin_cases i; rfl

private theorem rightTriangle_toCanonical :
    Coordinate.rightTriangle.{u} ≫ Coordinate.squareIso.hom = rightTriangle := by
  erw [Coordinate.rightTriangle, yonedaEquiv_symm_comp, rightTriangle]
  apply congrArg yonedaEquiv.symm
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

private theorem leftTriangle_toCanonical :
    Coordinate.leftTriangle.{u} ≫ Coordinate.squareIso.hom = leftTriangle := by
  erw [Coordinate.leftTriangle, yonedaEquiv_symm_comp, leftTriangle]
  apply congrArg yonedaEquiv.symm
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

private theorem diagonal_toCanonical :
    Coordinate.diagonal.{u} ≫ Coordinate.squareIso.hom = diagonal := by
  erw [Coordinate.diagonal, Coordinate.edge, yonedaEquiv_symm_comp, diagonal, edge]
  apply congrArg yonedaEquiv.symm
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

private theorem topEdge_toCanonical :
    Coordinate.topEdge.{u} ≫ Coordinate.squareIso.hom = topEdge := by
  erw [Coordinate.topEdge, Coordinate.edge, yonedaEquiv_symm_comp, topEdge, edge]
  apply congrArg yonedaEquiv.symm
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

private theorem leftEdge_toCanonical :
    Coordinate.leftEdge.{u} ≫ Coordinate.squareIso.hom = leftEdge := by
  erw [Coordinate.leftEdge, Coordinate.edge, yonedaEquiv_symm_comp, leftEdge, edge]
  apply congrArg yonedaEquiv.symm
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

private theorem rightEdge_toCanonical :
    Coordinate.rightEdge.{u} ≫ Coordinate.squareIso.hom = rightEdge := by
  erw [Coordinate.rightEdge, Coordinate.edge, yonedaEquiv_symm_comp, rightEdge, edge]
  apply congrArg yonedaEquiv.symm
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

private theorem bottomEdge_toCanonical :
    Coordinate.bottomEdge.{u} ≫ Coordinate.squareIso.hom = bottomEdge := by
  erw [Coordinate.bottomEdge, Coordinate.edge, yonedaEquiv_symm_comp, bottomEdge, edge]
  apply congrArg yonedaEquiv.symm
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

private theorem point_toCanonical (v : Coordinate.DiamondObjects.{u}) :
    Coordinate.point v ≫ Coordinate.squareIso.hom = point (Coordinate.squareObjectEquiv v) := by
  erw [Coordinate.point, yonedaEquiv_symm_comp, point]
  apply congrArg yonedaEquiv.symm
  apply nerve.ext_of_isThin
  rfl

/-- Both standard cospan charts share their actual target vertex. -/
theorem cospanRightChart_terminal :
    stdSimplex.δ (0 : Fin 2) ≫ cospanRightChart.{u} = cospanTerminalPoint := by
  rw [← cospanRightChart_toCanonical, ← cospanTerminalPoint_toCanonical,
    ← Category.assoc, Coordinate.cospanRightChart_terminal]

/-- The second cospan chart has the same target vertex. -/
theorem cospanLeftChart_terminal :
    stdSimplex.δ (0 : Fin 2) ≫ cospanLeftChart.{u} = cospanTerminalPoint := by
  rw [← cospanLeftChart_toCanonical, ← cospanTerminalPoint_toCanonical,
    ← Category.assoc, Coordinate.cospanLeftChart_terminal]

/-- The first complete triangle contains the canonical common diagonal. -/
theorem rightTriangle_diagonal :
    stdSimplex.δ (1 : Fin 3) ≫ rightTriangle.{u} = diagonal := by
  rw [← rightTriangle_toCanonical, ← diagonal_toCanonical,
    ← Category.assoc, Coordinate.rightTriangle_diagonal]

/-- The second complete triangle contains the same canonical common diagonal. -/
theorem leftTriangle_diagonal :
    stdSimplex.δ (1 : Fin 3) ≫ leftTriangle.{u} = diagonal := by
  rw [← leftTriangle_toCanonical, ← diagonal_toCanonical,
    ← Category.assoc, Coordinate.leftTriangle_diagonal]

/-- The first cospan chart is the target-facing edge of its full triangle. -/
theorem cospanRightChart_inclusion :
    cospanRightChart.{u} ≫ cospanInclusion = stdSimplex.δ (0 : Fin 3) ≫ rightTriangle := by
  rw [← cospanRightChart_toCanonical, ← rightTriangle_toCanonical,
    Category.assoc, ← Coordinate.inclusion_squareIso, ← Category.assoc,
    Coordinate.cospanRightChart_inclusion, Category.assoc]

/-- The second cospan chart is the target-facing edge of its full triangle. -/
theorem cospanLeftChart_inclusion :
    cospanLeftChart.{u} ≫ cospanInclusion = stdSimplex.δ (0 : Fin 3) ≫ leftTriangle := by
  rw [← cospanLeftChart_toCanonical, ← leftTriangle_toCanonical,
    Category.assoc, ← Coordinate.inclusion_squareIso, ← Category.assoc,
    Coordinate.cospanLeftChart_inclusion, Category.assoc]

/-- The first standard cospan chart is the original right square side. -/
theorem cospanRightChart_comp_inclusion :
    cospanRightChart.{u} ≫ cospanInclusion = rightEdge := by
  rw [← cospanRightChart_toCanonical, ← rightEdge_toCanonical,
    Category.assoc, ← Coordinate.inclusion_squareIso, ← Category.assoc,
    Coordinate.cospanRightChart_comp_inclusion]

/-- The second standard cospan chart is the original bottom square side. -/
theorem cospanLeftChart_comp_inclusion :
    cospanLeftChart.{u} ≫ cospanInclusion = bottomEdge := by
  rw [← cospanLeftChart_toCanonical, ← bottomEdge_toCanonical,
    Category.assoc, ← Coordinate.inclusion_squareIso, ← Category.assoc,
    Coordinate.cospanLeftChart_comp_inclusion]

/-- The standard cospan target is the adjoined square's common target vertex. -/
theorem cospanTerminalPoint_comp_inclusion :
    cospanTerminalPoint.{u} ≫ cospanInclusion = point (WithInitial.of (ULift.up WalkingCospan.one)) := by
  rw [← cospanTerminalPoint_toCanonical, Category.assoc, ← Coordinate.inclusion_squareIso,
    ← Category.assoc, Coordinate.cospanTerminalPoint_comp_inclusion, point_toCanonical]
  rfl

/-- The first full triangle contains the original top edge. -/
theorem rightTriangle_topEdge :
    stdSimplex.δ (2 : Fin 3) ≫ rightTriangle.{u} = topEdge := by
  rw [← rightTriangle_toCanonical, ← topEdge_toCanonical,
    ← Category.assoc, Coordinate.rightTriangle_topEdge]

/-- The second full triangle contains the original left edge. -/
theorem leftTriangle_leftEdge :
    stdSimplex.δ (2 : Fin 3) ≫ leftTriangle.{u} = leftEdge := by
  rw [← leftTriangle_toCanonical, ← leftEdge_toCanonical,
    ← Category.assoc, Coordinate.leftTriangle_leftEdge]

/-- The initial vertex of the first triangle is the actual adjoined initial object. -/
theorem rightTriangle_initial :
    stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋2⦌ 0) ≫ rightTriangle.{u} =
      point WithInitial.star := by
  rw [← rightTriangle_toCanonical, ← Category.assoc,
    Coordinate.rightTriangle_initial, point_toCanonical]
  rfl

/-- The standard cospan nerve is the pushout of its full two edge charts over their common target. -/
theorem cospanShape_isPushout :
    IsPushout (stdSimplex.δ (0 : Fin 2)) (stdSimplex.δ (0 : Fin 2))
      cospanRightChart.{u} cospanLeftChart := by
  apply Coordinate.cospanShape_isPushout.of_iso (Iso.refl _) (Iso.refl _)
    (Iso.refl _) Coordinate.cospanIso
  · simp
  · simp
  · simpa only [Iso.refl_hom, Category.id_comp] using cospanRightChart_toCanonical
  · simpa only [Iso.refl_hom, Category.id_comp] using cospanLeftChart_toCanonical

/-- The canonical coherent diamond is the pushout of both full triangles over their common diagonal. -/
theorem squareShape_isPushout :
    IsPushout (stdSimplex.δ (1 : Fin 3)) (stdSimplex.δ (1 : Fin 3))
      rightTriangle.{u} leftTriangle := by
  apply Coordinate.squareShape_isPushout.of_iso (Iso.refl _) (Iso.refl _)
    (Iso.refl _) Coordinate.squareIso
  · simp
  · simp
  · simpa only [Iso.refl_hom, Category.id_comp] using rightTriangle_toCanonical
  · simpa only [Iso.refl_hom, Category.id_comp] using leftTriangle_toCanonical

/-- The whole canonical diamond is the simplicial cone on its standard walking cospan. -/
def shapeJoinIso : squareShape.{u} ≅ (Δ[0] : SSet.{u}) ⋆ cospanShape.{u} :=
  Coordinate.squareIso.symm ≪≫ Coordinate.shapeJoinIso ≪≫
    (join.obj (Δ[0] : SSet.{u})).mapIso Coordinate.cospanIso

/-- The canonical join comparison preserves the complete first triangle chart. -/
theorem rightTriangle_comp_shapeJoinIso_hom :
    rightTriangle.{u} ≫ shapeJoinIso.hom =
      (joinStdSimplexIso 0 1).inv ≫ (join.obj (Δ[0] : SSet.{u})).map cospanRightChart := by
  change rightTriangle ≫ (Coordinate.squareIso.inv ≫
    (Coordinate.shapeJoinIso.hom ≫ (join.obj (Δ[0] : SSet.{u})).map Coordinate.cospanIso.hom)) = _
  calc
    _ = (Coordinate.rightTriangle ≫ Coordinate.shapeJoinIso.hom) ≫
        (join.obj (Δ[0] : SSet.{u})).map Coordinate.cospanIso.hom := by
      rw [← rightTriangle_toCanonical]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = ((joinStdSimplexIso 0 1).inv ≫ (join.obj (Δ[0] : SSet.{u})).map
        Coordinate.cospanRightChart) ≫ (join.obj (Δ[0] : SSet.{u})).map Coordinate.cospanIso.hom :=
      congrArg (fun f => f ≫ (join.obj (Δ[0] : SSet.{u})).map Coordinate.cospanIso.hom)
        Coordinate.rightTriangle_comp_shapeJoinIso_hom
    _ = _ := by
      rw [Category.assoc, ← CategoryTheory.Functor.map_comp, cospanRightChart_toCanonical]

/-- The canonical join comparison preserves the complete second triangle chart. -/
theorem leftTriangle_comp_shapeJoinIso_hom :
    leftTriangle.{u} ≫ shapeJoinIso.hom =
      (joinStdSimplexIso 0 1).inv ≫ (join.obj (Δ[0] : SSet.{u})).map cospanLeftChart := by
  change leftTriangle ≫ (Coordinate.squareIso.inv ≫
    (Coordinate.shapeJoinIso.hom ≫ (join.obj (Δ[0] : SSet.{u})).map Coordinate.cospanIso.hom)) = _
  calc
    _ = (Coordinate.leftTriangle ≫ Coordinate.shapeJoinIso.hom) ≫
        (join.obj (Δ[0] : SSet.{u})).map Coordinate.cospanIso.hom := by
      rw [← leftTriangle_toCanonical]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = ((joinStdSimplexIso 0 1).inv ≫ (join.obj (Δ[0] : SSet.{u})).map
        Coordinate.cospanLeftChart) ≫ (join.obj (Δ[0] : SSet.{u})).map Coordinate.cospanIso.hom :=
      congrArg (fun f => f ≫ (join.obj (Δ[0] : SSet.{u})).map Coordinate.cospanIso.hom)
        Coordinate.leftTriangle_comp_shapeJoinIso_hom
    _ = _ := by
      rw [Category.assoc, ← CategoryTheory.Functor.map_comp, cospanLeftChart_toCanonical]

/-- The actual standard WithInitial inclusion becomes the right join inclusion. -/
theorem cospanInclusion_comp_shapeJoinIso_hom :
    cospanInclusion.{u} ≫ shapeJoinIso.hom = joinInr (Δ[0] : SSet.{u}) cospanShape := by
  have hi : cospanInclusion ≫ Coordinate.squareIso.inv =
      Coordinate.cospanIso.inv ≫ Coordinate.cospanInclusion := by
    have h := congrArg (fun f => Coordinate.cospanIso.inv ≫ f ≫ Coordinate.squareIso.inv)
      Coordinate.inclusion_squareIso
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] using h.symm
  change cospanInclusion ≫ (Coordinate.squareIso.inv ≫
    (Coordinate.shapeJoinIso.hom ≫ (join.obj (Δ[0] : SSet.{u})).map Coordinate.cospanIso.hom)) = _
  calc
    _ = Coordinate.cospanIso.inv ≫ ((Coordinate.cospanInclusion ≫ Coordinate.shapeJoinIso.hom) ≫
        (join.obj (Δ[0] : SSet.{u})).map Coordinate.cospanIso.hom) := by
      rw [← Category.assoc, hi]
      simp only [Category.assoc]
    _ = Coordinate.cospanIso.inv ≫ (joinInr (Δ[0] : SSet.{u}) Coordinate.cospanShape ≫
        (join.obj (Δ[0] : SSet.{u})).map Coordinate.cospanIso.hom) :=
      congrArg (fun f => Coordinate.cospanIso.inv ≫
        (f ≫ (join.obj (Δ[0] : SSet.{u})).map Coordinate.cospanIso.hom))
        Coordinate.cospanInclusion_comp_shapeJoinIso_hom
    _ = Coordinate.cospanIso.inv ≫ (Coordinate.cospanIso.hom ≫
        joinInr (Δ[0] : SSet.{u}) cospanShape) :=
      congrArg (fun f => Coordinate.cospanIso.inv ≫ f)
        (map_comp_joinInr Coordinate.cospanIso.hom (Δ[0] : SSet.{u})).symm
    _ = _ := by rw [Iso.inv_hom_id_assoc]

/-- The actual adjoined initial object becomes the left join inclusion. -/
theorem initialPoint_comp_shapeJoinIso_hom :
    point WithInitial.star ≫ shapeJoinIso.{u}.hom =
      joinInl (Δ[0] : SSet.{u}) cospanShape := by
  have hp : point WithInitial.star =
      Coordinate.point (ULift.up (0, 0)) ≫ Coordinate.squareIso.hom :=
    (point_toCanonical (ULift.up (0, 0))).symm
  change point WithInitial.star ≫ (Coordinate.squareIso.inv ≫
    (Coordinate.shapeJoinIso.hom ≫ (join.obj (Δ[0] : SSet.{u})).map Coordinate.cospanIso.hom)) = _
  calc
    _ = (Coordinate.point (ULift.up (0, 0)) ≫ Coordinate.shapeJoinIso.hom) ≫
        (join.obj (Δ[0] : SSet.{u})).map Coordinate.cospanIso.hom := by
      rw [hp]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = joinInl (Δ[0] : SSet.{u}) Coordinate.cospanShape ≫
        (join.obj (Δ[0] : SSet.{u})).map Coordinate.cospanIso.hom :=
      congrArg (fun f => f ≫ (join.obj (Δ[0] : SSet.{u})).map Coordinate.cospanIso.hom)
        Coordinate.initialPoint_comp_shapeJoinIso_hom
    _ = _ := joinInl_comp_map (Δ[0] : SSet.{u}) Coordinate.cospanIso.hom

end SSet.NativePullback
