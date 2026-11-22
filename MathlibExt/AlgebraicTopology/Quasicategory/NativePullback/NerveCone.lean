/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Quasicategory.NativePullback.JoinShape
import all MathlibExt.AlgebraicTopology.Quasicategory.NativePullback.JoinShape
import all MathlibExt.AlgebraicTopology.Quasicategory.NativePullback.Shapes
public import MathlibExt.AlgebraicTopology.SimplicialSet.GeneralJoinSlice
public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinSliceIndexIso
public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveMax
public import MathlibExt.CategoryTheory.NerveHomotopy
public import Mathlib.CategoryTheory.Limits.Cones
public import Mathlib.Order.Sum.Order
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Original cones in an ordinary nerve

The source fixed diagram is the literal original cospan inclusion followed
by the nerve of the original square functor. Free ordinal vertices retain
their ordinary apex arrows, including arrows which are not invertible.

The original coefficient category has independent object and Hom universes.
The native indexing and value universes use their maximum; the original
category, cone points and arrows are retained.
-/

noncomputable section

public section

set_option autoImplicit false

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u uObj uHom

namespace SSet.NativePullback.Coordinate


variable {C : Type uObj} [Category.{uHom} C]

open CategoryTheory.NerveUniverses (nerveMapMax nerveMapMax_comp)

/-- The ordinary cone supplied by the original initial diamond object. -/
private def ordinaryCone (Q : DiamondObjects.{u} ⥤ C) : Cone (cospanInclusionFunctor ⋙ Q) where
  pt := Q.obj ⟨(0, 0)⟩
  π :=
    { app v := Q.map (homOfLE ⟨Fin.zero_le _, Fin.zero_le _⟩)
      naturality a b f := by
        dsimp
        rw [Category.id_comp, ← Q.map_comp]
        congr 1 }

/-- The ordinary right branch component is the original initial-to-right arrow. -/
private theorem ordinaryCone_right (Q : DiamondObjects.{u} ⥤ C) :
    (ordinaryCone Q).π.app ⟨⟨(1, 0)⟩, by decide⟩ =
      Q.map (homOfLE (show (⟨(0, 0)⟩ : DiamondObjects.{u}) ≤ ⟨(1, 0)⟩ from
        ⟨by decide, le_rfl⟩)) := rfl

/-- The ordinary left branch component is the original initial-to-left arrow. -/
private theorem ordinaryCone_left (Q : DiamondObjects.{u} ⥤ C) :
    (ordinaryCone Q).π.app ⟨⟨(0, 1)⟩, by decide⟩ =
      Q.map (homOfLE (show (⟨(0, 0)⟩ : DiamondObjects.{u}) ≤ ⟨(0, 1)⟩ from
        ⟨le_rfl, by decide⟩)) := rfl

/-- The ordinary target component is the original whole diagonal arrow. -/
private theorem ordinaryCone_target (Q : DiamondObjects.{u} ⥤ C) :
    (ordinaryCone Q).π.app ⟨⟨(1, 1)⟩, by decide⟩ =
      Q.map (homOfLE (show (⟨(0, 0)⟩ : DiamondObjects.{u}) ≤ ⟨(1, 1)⟩ from
        ⟨by decide, by decide⟩)) := rfl

/-- The right branch of the fixed ordinary diagram is the original right square arrow. -/
private theorem ordinaryDiagram_right (Q : DiamondObjects.{u} ⥤ C) :
    (cospanInclusionFunctor ⋙ Q).map
      (homOfLE (show (⟨⟨(1, 0)⟩, by decide⟩ : CospanObjects.{u}) ≤
        ⟨⟨(1, 1)⟩, by decide⟩ from ⟨le_rfl, by decide⟩)) =
      Q.map (homOfLE (show (⟨(1, 0)⟩ : DiamondObjects.{u}) ≤ ⟨(1, 1)⟩ from
        ⟨le_rfl, by decide⟩)) := rfl

/-- The left branch of the fixed ordinary diagram is the original bottom square arrow. -/
private theorem ordinaryDiagram_bottom (Q : DiamondObjects.{u} ⥤ C) :
    (cospanInclusionFunctor ⋙ Q).map
      (homOfLE (show (⟨⟨(0, 1)⟩, by decide⟩ : CospanObjects.{u}) ≤
        ⟨⟨(1, 1)⟩, by decide⟩ from ⟨by decide, le_rfl⟩)) =
      Q.map (homOfLE (show (⟨(0, 1)⟩ : DiamondObjects.{u}) ≤ ⟨(1, 1)⟩ from
        ⟨by decide, le_rfl⟩)) := rfl

/-- The original whole coherent cone map, fixed on its original right cospan. -/
private def squareConeSimplex (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    (sliceOver (nerve C) (cospanInclusion ≫ nerveMapMax Q)).obj (op ⦋0⦌) :=
  ⟨shapeJoinIso.inv ≫ nerveMapMax Q, by
    rw [← cospanInclusion_comp_shapeJoinIso_hom]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]⟩

/-- The original whole cone as an actual point in the original over-slice. -/
private def squareConePoint (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    (Δ[0] : SSet.{max uObj uHom}) ⟶ sliceOver (nerve C) (cospanInclusion ≫ nerveMapMax Q) :=
  yonedaEquiv.symm (squareConeSimplex Q)

private abbrev ConeIndex (n : ℕ) := ULift.{u} (Fin (n + 1)) ⊕ₗ CospanObjects.{u}

private def rightTailP (v : CospanObjects.{u}) : Prop := v.val.down.1 = 1

private def leftTailP (v : CospanObjects.{u}) : Prop := v.val.down.2 = 1

private def extendP (n : ℕ) (P : CospanObjects.{u} → Prop) : ConeIndex.{u} n → Prop := fun x =>
  match x with
  | .inl _ => True
  | .inr v => P v

private def sumFinOrderIso (m k : ℕ) : (Fin m ⊕ₗ Fin k) ≃o Fin (m + k) where
  toEquiv := ofLex.trans finSumFinEquiv
  map_rel_iff' := by
    rintro (i | i) (j | j)
    · change Fin.castAdd k i ≤ Fin.castAdd k j ↔
        Sum.Lex (· ≤ ·) (· ≤ ·) (Sum.inl i) (Sum.inl j)
      rw [Sum.lex_inl_inl]
      rfl
    · change i.val ≤ m + j.val ↔ Sum.Lex (· ≤ ·) (· ≤ ·) (Sum.inl i) (Sum.inr j)
      constructor
      · intro _
        exact Sum.Lex.sep _ _
      · intro _
        have hi := i.isLt
        omega
    · change m + i.val ≤ j.val ↔ Sum.Lex (· ≤ ·) (· ≤ ·) (Sum.inr i) (Sum.inl j)
      constructor
      · intro h
        have hj := j.isLt
        omega
      · intro h
        cases h
    · change m + i.val ≤ m + j.val ↔
        Sum.Lex (· ≤ ·) (· ≤ ·) (Sum.inr i) (Sum.inr j)
      rw [Sum.lex_inr_inr]
      omega

private def supportedSumOrderIso (n : ℕ) (P : CospanObjects.{u} → Prop) :
    (ULift.{u} (Fin (n + 1)) ⊕ₗ {v : CospanObjects.{u} // P v}) ≃o
      {v : ConeIndex.{u} n // extendP n P v} where
  toFun
    | Sum.inlₗ i => ⟨Sum.inlₗ i, True.intro⟩
    | Sum.inrₗ v => ⟨Sum.inrₗ v.val, v.property⟩
  invFun
    | ⟨Sum.inlₗ i, _⟩ => Sum.inlₗ i
    | ⟨Sum.inrₗ v, h⟩ => Sum.inrₗ ⟨v, h⟩
  left_inv := by rintro (i | v) <;> rfl
  right_inv := by rintro ⟨i | v, h⟩ <;> rfl
  map_rel_iff' := by
    rintro (i | v) (j | w)
    · change (Sum.inlₗ i : ConeIndex n) ≤ Sum.inlₗ j ↔
        (Sum.inlₗ i : ULift (Fin (n + 1)) ⊕ₗ {v : CospanObjects // P v}) ≤ Sum.inlₗ j
      simp only [Sum.Lex.inl_le_inl_iff]
    · change (Sum.inlₗ i : ConeIndex n) ≤ Sum.inrₗ w.val ↔
        (Sum.inlₗ i : ULift (Fin (n + 1)) ⊕ₗ {v : CospanObjects // P v}) ≤ Sum.inrₗ w
      exact ⟨fun _ => Sum.Lex.sep _ _, fun _ => Sum.Lex.sep _ _⟩
    · change (Sum.inrₗ v.val : ConeIndex n) ≤ Sum.inlₗ j ↔
        (Sum.inrₗ v : ULift (Fin (n + 1)) ⊕ₗ {v : CospanObjects // P v}) ≤ Sum.inlₗ j
      simp only [Sum.Lex.not_inr_le_inl]
    · change (Sum.inrₗ v.val : ConeIndex n) ≤ Sum.inrₗ w.val ↔
        (Sum.inrₗ v : ULift (Fin (n + 1)) ⊕ₗ {v : CospanObjects // P v}) ≤ Sum.inrₗ w
      simp only [Sum.Lex.inr_le_inr_iff]
      rfl

private def rightTailOrderIso : Fin 2 ≃o {v : CospanObjects.{u} // rightTailP v} where
  toFun i := ⟨⟨⟨(1, i)⟩, by simp⟩, rfl⟩
  invFun v := v.val.val.down.2
  left_inv _ := rfl
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    apply ULift.ext
    apply Prod.ext
    · exact v.property.symm
    · rfl
  map_rel_iff' := by
    intro i j
    change ((1 : Fin 2) ≤ 1 ∧ i ≤ j) ↔ i ≤ j
    simp

private def leftTailOrderIso : Fin 2 ≃o {v : CospanObjects.{u} // leftTailP v} where
  toFun i := ⟨⟨⟨(i, 1)⟩, by simp⟩, rfl⟩
  invFun v := v.val.val.down.1
  left_inv _ := rfl
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    apply ULift.ext
    apply Prod.ext
    · rfl
    · exact v.property.symm
  map_rel_iff' := by
    intro i j
    change (i ≤ j ∧ (1 : Fin 2) ≤ 1) ↔ i ≤ j
    simp

private def targetTailOrderIso :
    Fin 1 ≃o {v : CospanObjects.{u} // rightTailP v ∧ leftTailP v} where
  toFun _ := ⟨⟨⟨(1, 1)⟩, by decide⟩, ⟨rfl, rfl⟩⟩
  invFun _ := 0
  left_inv i := by fin_cases i; rfl
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    apply ULift.ext
    apply Prod.ext
    · exact v.property.1.symm
    · exact v.property.2.symm
  map_rel_iff' := by
    intro i j
    change (((1 : Fin 2) ≤ 1 ∧ (1 : Fin 2) ≤ 1) ↔ i ≤ j)
    fin_cases i
    fin_cases j
    decide

private def rightIndexOrderIso (n : ℕ) :
    Fin (n + 3) ≃o {v : ConeIndex.{u} n // extendP n rightTailP v} :=
  (sumFinOrderIso (n + 1) 2).symm.trans
    ((OrderIso.sumLexCongr ULift.orderIso.symm rightTailOrderIso).trans
      (supportedSumOrderIso n rightTailP))

private def leftIndexOrderIso (n : ℕ) :
    Fin (n + 3) ≃o {v : ConeIndex.{u} n // extendP n leftTailP v} :=
  (sumFinOrderIso (n + 1) 2).symm.trans
    ((OrderIso.sumLexCongr ULift.orderIso.symm leftTailOrderIso).trans
      (supportedSumOrderIso n leftTailP))

private def targetIndexOrderIso (n : ℕ) :
    Fin (n + 2) ≃o {v : ConeIndex.{u} n // extendP n (fun v => rightTailP v ∧ leftTailP v) v} :=
  (sumFinOrderIso (n + 1) 1).symm.trans
    ((OrderIso.sumLexCongr ULift.orderIso.symm targetTailOrderIso).trans
      (supportedSumOrderIso n (fun v => rightTailP v ∧ leftTailP v)))

private def indexChartIso (n : ℕ) (P : CospanObjects.{u} → Prop) {k : ℕ}
    (e : Fin (k + 1) ≃o {v : ConeIndex.{u} n // extendP n P v}) :
    (Δ[k] : SSet.{u}) ≅ (preorderSubtypeSubcomplex (extendP n P) : SSet.{u}) :=
  SSet.stdSimplex.isoOfRepresentableBy (nerve.representableBy _ e.symm) ≪≫
    nervePreorderSubtypeIso (extendP n P)

private theorem rightIndexOrderIso_prefix (n : ℕ) (i : Fin (n + 1)) :
    ((rightIndexOrderIso.{u} n) (Fin.castAdd 2 i)).val = Sum.inlₗ (ULift.up i) := by
  change ((supportedSumOrderIso n rightTailP)
    ((OrderIso.sumLexCongr ULift.orderIso.symm rightTailOrderIso)
      (toLex (finSumFinEquiv.symm (Fin.castAdd 2 i))))).val = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

private theorem leftIndexOrderIso_prefix (n : ℕ) (i : Fin (n + 1)) :
    ((leftIndexOrderIso.{u} n) (Fin.castAdd 2 i)).val = Sum.inlₗ (ULift.up i) := by
  change ((supportedSumOrderIso n leftTailP)
    ((OrderIso.sumLexCongr ULift.orderIso.symm leftTailOrderIso)
      (toLex (finSumFinEquiv.symm (Fin.castAdd 2 i))))).val = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

private theorem rightIndexOrderIso_tail (n : ℕ) (i : Fin 2) :
    ((rightIndexOrderIso.{u} n) (Fin.natAdd (n + 1) i)).val =
      Sum.inrₗ (⟨⟨(1, i)⟩, by simp⟩ : CospanObjects.{u}) := by
  change ((supportedSumOrderIso n rightTailP)
    ((OrderIso.sumLexCongr ULift.orderIso.symm rightTailOrderIso)
      (toLex (finSumFinEquiv.symm (Fin.natAdd (n + 1) i))))).val = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

private theorem leftIndexOrderIso_tail (n : ℕ) (i : Fin 2) :
    ((leftIndexOrderIso.{u} n) (Fin.natAdd (n + 1) i)).val =
      Sum.inrₗ (⟨⟨(i, 1)⟩, by simp⟩ : CospanObjects.{u}) := by
  change ((supportedSumOrderIso n leftTailP)
    ((OrderIso.sumLexCongr ULift.orderIso.symm leftTailOrderIso)
      (toLex (finSumFinEquiv.symm (Fin.natAdd (n + 1) i))))).val = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

private theorem targetIndexOrderIso_prefix (n : ℕ) (i : Fin (n + 1)) :
    ((targetIndexOrderIso.{u} n) i.castSucc).val = Sum.inlₗ (ULift.up i) := by
  change ((supportedSumOrderIso n (fun v => rightTailP v ∧ leftTailP v))
    ((OrderIso.sumLexCongr ULift.orderIso.symm targetTailOrderIso)
      (toLex (finSumFinEquiv.symm i.castSucc)))).val = _
  rw [finSumFinEquiv_symm_apply_castSucc]
  rfl

private theorem targetIndexOrderIso_tail (n : ℕ) (i : Fin 1) :
    ((targetIndexOrderIso.{u} n) (Fin.natAdd (n + 1) i)).val =
      Sum.inrₗ (⟨⟨(1, 1)⟩, by decide⟩ : CospanObjects.{u}) := by
  change ((supportedSumOrderIso n (fun v => rightTailP v ∧ leftTailP v))
    ((OrderIso.sumLexCongr ULift.orderIso.symm targetTailOrderIso)
      (toLex (finSumFinEquiv.symm (Fin.natAdd (n + 1) i))))).val = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

private def indexRightSupport (n : ℕ) : (nerve (ConeIndex.{u} n)).Subcomplex :=
  preorderSubtypeSubcomplex (extendP n rightTailP)

private def indexLeftSupport (n : ℕ) : (nerve (ConeIndex.{u} n)).Subcomplex :=
  preorderSubtypeSubcomplex (extendP n leftTailP)

private def indexRightIso (n : ℕ) :
    (Δ[n + 2] : SSet.{u}) ≅ (indexRightSupport n : SSet.{u}) :=
  indexChartIso n rightTailP (rightIndexOrderIso n)

private def indexLeftIso (n : ℕ) :
    (Δ[n + 2] : SSet.{u}) ≅ (indexLeftSupport n : SSet.{u}) :=
  indexChartIso n leftTailP (leftIndexOrderIso n)

private theorem extendP_and (n : ℕ) (P Q : CospanObjects.{u} → Prop) :
    extendP n (fun v => P v ∧ Q v) = fun v => extendP n P v ∧ extendP n Q v := by
  funext v
  rcases v with i | v <;> simp [extendP]

private def indexTargetIso (n : ℕ) :
    (Δ[n + 1] : SSet.{u}) ≅ (indexRightSupport n ⊓ indexLeftSupport n).toSSet :=
  indexChartIso n (fun v => rightTailP v ∧ leftTailP v) (targetIndexOrderIso n) ≪≫
    Subcomplex.eqToIso (by
      ext q x
      change (∀ i, extendP n (fun v => rightTailP v ∧ leftTailP v) (x.obj i)) ↔
        ((∀ i, extendP n rightTailP (x.obj i)) ∧ ∀ i, extendP n leftTailP (x.obj i))
      rw [extendP_and]
      exact forall_and)

private def indexRightChart (n : ℕ) : (Δ[n + 2] : SSet.{u}) ⟶ nerve (ConeIndex.{u} n) :=
  (indexRightIso n).hom ≫ (indexRightSupport n).ι

private def indexLeftChart (n : ℕ) : (Δ[n + 2] : SSet.{u}) ⟶ nerve (ConeIndex.{u} n) :=
  (indexLeftIso n).hom ≫ (indexLeftSupport n).ι

private def indexTargetChart (n : ℕ) : (Δ[n + 1] : SSet.{u}) ⟶ nerve (ConeIndex.{u} n) :=
  (indexTargetIso n).hom ≫ (indexRightSupport n ⊓ indexLeftSupport n).ι

private theorem tailSupport_of_comparable (v w : CospanObjects.{u})
    (hv : ¬ rightTailP v) (h : v ≤ w ∨ w ≤ v) : leftTailP w := by
  rcases v with ⟨⟨⟨a, b⟩⟩, hn⟩
  rcases w with ⟨⟨⟨c, d⟩⟩, hm⟩
  change ¬ a = 1 at hv
  change (a, b) ≠ (0, 0) at hn
  change (c, d) ≠ (0, 0) at hm
  change (a.val ≤ c.val ∧ b.val ≤ d.val) ∨ (c.val ≤ a.val ∧ d.val ≤ b.val) at h
  change d = 1
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  all_goals
    try
      first
      | rfl
      | exact (hv rfl).elim
      | exact (hn rfl).elim
      | exact (hm rfl).elim
  rcases h with h | h
  · exact ((by decide : ¬ ((1 : ℕ) ≤ 0)) h.2).elim
  · exact ((by decide : ¬ ((1 : ℕ) ≤ 0)) h.1).elim

private theorem indexWord_cover (n : ℕ) {d : ℕ} (x : ComposableArrows (ConeIndex.{u} n) d) :
    (∀ i, extendP n rightTailP (x.obj i)) ∨ (∀ i, extendP n leftTailP (x.obj i)) := by
  classical
  by_cases h : ∀ i, extendP n rightTailP (x.obj i)
  · exact Or.inl h
  · right
    obtain ⟨i, hi⟩ := not_forall.mp h
    obtain ⟨v, hv⟩ : ∃ v, x.obj i = Sum.inrₗ v := by
      rcases hx : ofLex (x.obj i) with a | v
      · have hx' : x.obj i = Sum.inlₗ a := ofLex.injective hx
        rw [hx'] at hi
        exact (hi True.intro).elim
      · exact ⟨v, ofLex.injective hx⟩
    rw [hv] at hi
    change ¬ rightTailP v at hi
    intro j
    rcases hj : ofLex (x.obj j) with a | w
    · have hj' : x.obj j = Sum.inlₗ a := ofLex.injective hj
      rw [hj']
      trivial
    · have hj' : x.obj j = Sum.inrₗ w := ofLex.injective hj
      rw [hj']
      apply tailSupport_of_comparable v w hi
      · rcases le_total i j with hij | hji
        · left
          have hle := leOfHom (x.map (homOfLE hij))
          rw [hv, hj'] at hle
          exact Sum.Lex.inr_le_inr_iff.mp hle
        · right
          have hle := leOfHom (x.map (homOfLE hji))
          rw [hv, hj'] at hle
          exact Sum.Lex.inr_le_inr_iff.mp hle

private theorem indexSupport_cover (n : ℕ) :
    indexRightSupport.{u} n ⊔ indexLeftSupport n = ⊤ := by
  refine le_antisymm le_top ?_
  intro q x _
  exact indexWord_cover n x

private def gluingOperator (n : ℕ) : ⦋n + 1⦌ ⟶ ⦋n + 2⦌ :=
  AugmentedSimplexCategory.tensorHomOf (𝟙 ⦋n⦌) (SimplexCategory.δ (0 : Fin 2))

private theorem gluingOperator_prefix (n : ℕ) (i : Fin (n + 1)) :
    (gluingOperator n).toOrderHom i.castSucc = Fin.castAdd 2 i := by
  apply Fin.ext
  simp only [Fin.val_castAdd]
  exact congrArg Fin.val (Fin.addCases_left (n := 1) (motive := fun _ => Fin (n + 3))
    (left := fun j : Fin (n + 1) => Fin.castAdd 2 j)
    (right := fun j : Fin 1 => Fin.natAdd (n + 1) ((SimplexCategory.δ 0).toOrderHom j)) i)

private theorem gluingOperator_tail (n : ℕ) (i : Fin 1) :
    (gluingOperator n).toOrderHom (Fin.natAdd (n + 1) i) =
      Fin.natAdd (n + 1) i.succ := by
  apply Fin.ext
  simp only [gluingOperator, AugmentedSimplexCategory.tensorHomOf, Nat.add_zero,
    Nat.succ_eq_add_one, Nat.reduceAdd, eqToHom_refl, Nat.add_eq, SimplexCategory.mkHom,
    SimplexCategory.id_toOrderHom, OrderHom.id_coe, id_eq, Fin.isValue, Category.comp_id,
    Category.id_comp, SimplexCategory.Hom.toOrderHom_mk, OrderHom.coe_mk, Fin.addCases_right,
    Fin.val_natAdd, Fin.val_succ, Fin.val_eq_zero, zero_add, Nat.add_left_cancel_iff]
  fin_cases i
  rfl

private theorem indexRightChart_gluing (n : ℕ) :
    SSet.stdSimplex.map (gluingOperator n) ≫ indexRightChart.{u} n = indexTargetChart n := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  refine Fin.addCases (m := n + 1) (n := 1) (fun i => ?_) (fun i => ?_) i
  · change ((rightIndexOrderIso n) ((gluingOperator n).toOrderHom i.castSucc)).val =
      ((targetIndexOrderIso n) i.castSucc).val
    rw [gluingOperator_prefix, rightIndexOrderIso_prefix, targetIndexOrderIso_prefix]
  · change ((rightIndexOrderIso n)
        ((gluingOperator n).toOrderHom (Fin.natAdd (n + 1) i))).val =
      ((targetIndexOrderIso n) (Fin.natAdd (n + 1) i)).val
    rw [gluingOperator_tail, rightIndexOrderIso_tail, targetIndexOrderIso_tail]
    fin_cases i
    rfl

private theorem indexLeftChart_gluing (n : ℕ) :
    SSet.stdSimplex.map (gluingOperator n) ≫ indexLeftChart.{u} n = indexTargetChart n := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  refine Fin.addCases (m := n + 1) (n := 1) (fun i => ?_) (fun i => ?_) i
  · change ((leftIndexOrderIso n) ((gluingOperator n).toOrderHom i.castSucc)).val =
      ((targetIndexOrderIso n) i.castSucc).val
    rw [gluingOperator_prefix, leftIndexOrderIso_prefix, targetIndexOrderIso_prefix]
  · change ((leftIndexOrderIso n)
        ((gluingOperator n).toOrderHom (Fin.natAdd (n + 1) i))).val =
      ((targetIndexOrderIso n) (Fin.natAdd (n + 1) i)).val
    rw [gluingOperator_tail, leftIndexOrderIso_tail, targetIndexOrderIso_tail]
    fin_cases i
    rfl

private theorem indexShape_isPushout (n : ℕ) :
    IsPushout (SSet.stdSimplex.map (gluingOperator n)) (SSet.stdSimplex.map (gluingOperator n))
      (indexRightChart.{u} n) (indexLeftChart n) := by
  have h := Subcomplex.BicartSq.isPushout
    (show Subcomplex.BicartSq (indexRightSupport n ⊓ indexLeftSupport n)
      (indexRightSupport n) (indexLeftSupport n) (⊤ : (nerve (ConeIndex.{u} n)).Subcomplex) from
        { sup_eq := indexSupport_cover n, inf_eq := rfl })
  apply h.of_iso' (indexTargetIso n) (indexRightIso n) (indexLeftIso n)
    (Subcomplex.topIso (nerve (ConeIndex n))).symm
  · apply (cancel_mono (indexRightSupport n).ι).1
    simpa only [indexTargetChart, indexRightChart, Category.assoc, Subcomplex.homOfLE_ι]
      using (indexRightChart_gluing n).symm
  · apply (cancel_mono (indexLeftSupport n).ι).1
    simpa only [indexTargetChart, indexLeftChart, Category.assoc, Subcomplex.homOfLE_ι]
      using (indexLeftChart_gluing n).symm
  · apply (cancel_mono (Subcomplex.topIso (nerve (ConeIndex n))).hom).1
    simp only [indexRightChart, Category.assoc, Iso.symm_hom, Subcomplex.topIso_hom,
      Subcomplex.homOfLE_ι, Subcomplex.topIso_inv_ι, Category.comp_id]
  · apply (cancel_mono (Subcomplex.topIso (nerve (ConeIndex n))).hom).1
    simp only [indexLeftChart, Category.assoc, Iso.symm_hom, Subcomplex.topIso_hom,
      Subcomplex.homOfLE_ι, Subcomplex.topIso_inv_ι, Category.comp_id]

private def joinedRightChart (n : ℕ) :
    (Δ[n + 2] : SSet.{u}) ⟶ (Δ[n] : SSet.{u}) ⋆ cospanShape.{u} :=
  (joinStdSimplexIso n 1).inv ≫ (join.obj (Δ[n] : SSet.{u})).map cospanRightChart

private def joinedLeftChart (n : ℕ) :
    (Δ[n + 2] : SSet.{u}) ⟶ (Δ[n] : SSet.{u}) ⋆ cospanShape.{u} :=
  (joinStdSimplexIso n 1).inv ≫ (join.obj (Δ[n] : SSet.{u})).map cospanLeftChart

private theorem nativeJoinedShape_isPushout (n : ℕ) :
    IsPushout (SSet.stdSimplex.map (gluingOperator n)) (SSet.stdSimplex.map (gluingOperator n))
      (joinedRightChart.{u} n) (joinedLeftChart n) := by
  have h := (join.obj (Δ[n] : SSet.{u})).map_isPushout cospanShape_isPushout
  apply h.of_iso (joinStdSimplexIso n 0) (joinStdSimplexIso n 1)
    (joinStdSimplexIso n 1) (Iso.refl _)
  · exact joinStdSimplexIso_natural_right (m := n) (SimplexCategory.δ (0 : Fin 2))
  · exact joinStdSimplexIso_natural_right (m := n) (SimplexCategory.δ (0 : Fin 2))
  · simp only [Iso.refl_hom, Category.comp_id, joinedRightChart, Iso.hom_inv_id_assoc]
  · simp only [Iso.refl_hom, Category.comp_id, joinedLeftChart, Iso.hom_inv_id_assoc]

private def indexJoinIso (n : ℕ) :
    (Δ[n] : SSet.{u}) ⋆ cospanShape.{u} ≅ nerve (ConeIndex.{u} n) :=
  (nativeJoinedShape_isPushout n).isoIsPushout _ _ (indexShape_isPushout n)

private theorem joinedRightChart_indexJoinIso (n : ℕ) :
    joinedRightChart.{u} n ≫ (indexJoinIso n).hom = indexRightChart n :=
  (nativeJoinedShape_isPushout n).inl_isoIsPushout_hom _ _ (indexShape_isPushout n)

private theorem joinedLeftChart_indexJoinIso (n : ℕ) :
    joinedLeftChart.{u} n ≫ (indexJoinIso n).hom = indexLeftChart n :=
  (nativeJoinedShape_isPushout n).inr_isoIsPushout_hom _ _ (indexShape_isPushout n)

private def indexRightFunctor (n : ℕ) : CospanObjects.{u} ⥤ ConeIndex.{u} n :=
  (show Monotone (fun v : CospanObjects.{u} => (Sum.inrₗ v : ConeIndex n)) from
    fun _ _ h => Sum.Lex.inr h).functor

private def indexLeftFunctor (n : ℕ) : Fin (n + 1) ⥤ ConeIndex.{u} n :=
  (show Monotone (fun i : Fin (n + 1) => (Sum.inlₗ (ULift.up i) : ConeIndex n)) from
    fun _ _ h => Sum.Lex.inl h).functor

private theorem inrOne_apply (n : ℕ) (i : Fin 2) :
    (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋1⦌).toOrderHom i = Fin.natAdd (n + 1) i := by
  apply Fin.ext
  simp [AugmentedSimplexCategory.inr'_eval]

private theorem inlOne_apply (n : ℕ) (i : Fin (n + 1)) :
    (AugmentedSimplexCategory.inl' ⦋n⦌ ⦋1⦌).toOrderHom i = Fin.castAdd 2 i := by
  apply Fin.ext
  simp [AugmentedSimplexCategory.inl'_eval]

private theorem indexRightChart_tail (n : ℕ) :
    SSet.stdSimplex.map (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋1⦌) ≫ indexRightChart.{u} n =
      cospanRightChart ≫ nerveMap (indexRightFunctor n) := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  change ((rightIndexOrderIso n)
    ((AugmentedSimplexCategory.inr' ⦋n⦌ ⦋1⦌).toOrderHom i)).val = _
  rw [inrOne_apply, rightIndexOrderIso_tail]
  fin_cases i <;> rfl

private theorem indexLeftChart_tail (n : ℕ) :
    SSet.stdSimplex.map (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋1⦌) ≫ indexLeftChart.{u} n =
      cospanLeftChart ≫ nerveMap (indexRightFunctor n) := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  change ((leftIndexOrderIso n)
    ((AugmentedSimplexCategory.inr' ⦋n⦌ ⦋1⦌).toOrderHom i)).val = _
  rw [inrOne_apply, leftIndexOrderIso_tail]
  fin_cases i <;> rfl

private theorem indexRightChart_prefix (n : ℕ) :
    SSet.stdSimplex.map (AugmentedSimplexCategory.inl' ⦋n⦌ ⦋1⦌) ≫ indexRightChart.{u} n =
      yonedaEquiv.symm (indexLeftFunctor n) := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  change ((rightIndexOrderIso n)
    ((AugmentedSimplexCategory.inl' ⦋n⦌ ⦋1⦌).toOrderHom i)).val = Sum.inlₗ (ULift.up i)
  rw [inlOne_apply, rightIndexOrderIso_prefix]

private theorem joinInr_one_eq (n : ℕ) :
    joinInr (Δ[n] : SSet.{u}) Δ[1] =
      SSet.stdSimplex.map (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋1⦌) ≫
        (joinStdSimplexIso n 1).inv := by
  rw [← joinInr_comp_joinStdSimplexIso_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem joinInl_one_eq (n : ℕ) :
    joinInl (Δ[n] : SSet.{u}) Δ[1] =
      SSet.stdSimplex.map (AugmentedSimplexCategory.inl' ⦋n⦌ ⦋1⦌) ≫
        (joinStdSimplexIso n 1).inv := by
  rw [← joinInl_comp_joinStdSimplexIso_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem indexJoinIso_right (n : ℕ) :
    joinInr (Δ[n] : SSet.{u}) cospanShape ≫ (indexJoinIso n).hom =
      nerveMap (indexRightFunctor n) := by
  apply cospanShape_isPushout.hom_ext
  · calc
      cospanRightChart ≫ (joinInr Δ[n] cospanShape ≫ (indexJoinIso n).hom) =
          (joinInr Δ[n] Δ[1] ≫ (join.obj Δ[n]).map cospanRightChart) ≫ (indexJoinIso n).hom := by
        rw [← Category.assoc, map_comp_joinInr]
      _ = SSet.stdSimplex.map (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋1⦌) ≫
          (joinedRightChart n ≫ (indexJoinIso n).hom) := by
        rw [joinInr_one_eq]
        simp only [joinedRightChart, Category.assoc]
      _ = cospanRightChart ≫ nerveMap (indexRightFunctor n) := by
        rw [joinedRightChart_indexJoinIso, indexRightChart_tail]
  · calc
      cospanLeftChart ≫ (joinInr Δ[n] cospanShape ≫ (indexJoinIso n).hom) =
          (joinInr Δ[n] Δ[1] ≫ (join.obj Δ[n]).map cospanLeftChart) ≫ (indexJoinIso n).hom := by
        rw [← Category.assoc, map_comp_joinInr]
      _ = SSet.stdSimplex.map (AugmentedSimplexCategory.inr' ⦋n⦌ ⦋1⦌) ≫
          (joinedLeftChart n ≫ (indexJoinIso n).hom) := by
        rw [joinInr_one_eq]
        simp only [joinedLeftChart, Category.assoc]
      _ = cospanLeftChart ≫ nerveMap (indexRightFunctor n) := by
        rw [joinedLeftChart_indexJoinIso, indexLeftChart_tail]

private theorem indexJoinIso_left (n : ℕ) :
    joinInl (Δ[n] : SSet.{u}) cospanShape ≫ (indexJoinIso n).hom =
      yonedaEquiv.symm (indexLeftFunctor n) := by
  calc
    joinInl Δ[n] cospanShape ≫ (indexJoinIso n).hom =
        (joinInl Δ[n] Δ[1] ≫ (join.obj Δ[n]).map cospanRightChart) ≫ (indexJoinIso n).hom := by
      rw [joinInl_comp_map]
    _ = SSet.stdSimplex.map (AugmentedSimplexCategory.inl' ⦋n⦌ ⦋1⦌) ≫
        (joinedRightChart n ≫ (indexJoinIso n).hom) := by
      rw [joinInl_one_eq]
      simp only [joinedRightChart, Category.assoc]
    _ = yonedaEquiv.symm (indexLeftFunctor n) := by
      rw [joinedRightChart_indexJoinIso, indexRightChart_prefix]

private def indexMap {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) : ConeIndex.{u} n →o ConeIndex.{u} m where
  toFun
    | Sum.inlₗ i => Sum.inlₗ (ULift.up (f.toOrderHom i.down))
    | Sum.inrₗ v => Sum.inrₗ v
  monotone' := by
    rintro (i | v) (j | w) h
    · have hi : i ≤ j := Sum.Lex.inl_le_inl_iff.mp h
      exact Sum.Lex.inl (f.toOrderHom.monotone hi)
    · exact Sum.Lex.sep _ _
    · exact (Sum.Lex.not_inr_le_inl h).elim
    · exact Sum.Lex.inr (Sum.Lex.inr_le_inr_iff.mp h)

private theorem tensorOne_prefix {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) (i : Fin (n + 1)) :
    (AugmentedSimplexCategory.tensorHomOf f (𝟙 ⦋1⦌)).toOrderHom (Fin.castAdd 2 i) =
      Fin.castAdd 2 (f.toOrderHom i) := by
  apply Fin.ext
  simp [AugmentedSimplexCategory.tensorHomOf]

private theorem tensorOne_tail {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) (i : Fin 2) :
    (AugmentedSimplexCategory.tensorHomOf f (𝟙 ⦋1⦌)).toOrderHom (Fin.natAdd (n + 1) i) =
      Fin.natAdd (m + 1) i := by
  apply Fin.ext
  simp [AugmentedSimplexCategory.tensorHomOf]

private theorem indexRightChart_natural {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    indexRightChart.{u} n ≫ nerveMap (indexMap f).monotone.functor =
      SSet.stdSimplex.map (AugmentedSimplexCategory.tensorHomOf f (𝟙 ⦋1⦌)) ≫ indexRightChart m := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  refine Fin.addCases (m := n + 1) (n := 2) (fun i => ?_) (fun i => ?_) i
  · change indexMap f (((rightIndexOrderIso n) (Fin.castAdd 2 i)).val) =
      ((rightIndexOrderIso m)
        ((AugmentedSimplexCategory.tensorHomOf f (𝟙 ⦋1⦌)).toOrderHom (Fin.castAdd 2 i))).val
    rw [rightIndexOrderIso_prefix, tensorOne_prefix, rightIndexOrderIso_prefix]
    rfl
  · change indexMap f (((rightIndexOrderIso n) (Fin.natAdd (n + 1) i)).val) =
      ((rightIndexOrderIso m)
        ((AugmentedSimplexCategory.tensorHomOf f (𝟙 ⦋1⦌)).toOrderHom (Fin.natAdd (n + 1) i))).val
    rw [rightIndexOrderIso_tail, tensorOne_tail, rightIndexOrderIso_tail]
    rfl

private theorem indexLeftChart_natural {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    indexLeftChart.{u} n ≫ nerveMap (indexMap f).monotone.functor =
      SSet.stdSimplex.map (AugmentedSimplexCategory.tensorHomOf f (𝟙 ⦋1⦌)) ≫ indexLeftChart m := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  refine Fin.addCases (m := n + 1) (n := 2) (fun i => ?_) (fun i => ?_) i
  · change indexMap f (((leftIndexOrderIso n) (Fin.castAdd 2 i)).val) =
      ((leftIndexOrderIso m)
        ((AugmentedSimplexCategory.tensorHomOf f (𝟙 ⦋1⦌)).toOrderHom (Fin.castAdd 2 i))).val
    rw [leftIndexOrderIso_prefix, tensorOne_prefix, leftIndexOrderIso_prefix]
    rfl
  · change indexMap f (((leftIndexOrderIso n) (Fin.natAdd (n + 1) i)).val) =
      ((leftIndexOrderIso m)
        ((AugmentedSimplexCategory.tensorHomOf f (𝟙 ⦋1⦌)).toOrderHom (Fin.natAdd (n + 1) i))).val
    rw [leftIndexOrderIso_tail, tensorOne_tail, leftIndexOrderIso_tail]
    rfl

private theorem joinedRightChart_natural {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    joinedRightChart.{u} n ≫ (join.map (SSet.stdSimplex.map f)).app cospanShape =
      SSet.stdSimplex.map (AugmentedSimplexCategory.tensorHomOf f (𝟙 ⦋1⦌)) ≫ joinedRightChart m := by
  simp only [joinedRightChart, Category.assoc]
  rw [(join.map (SSet.stdSimplex.map f)).naturality cospanRightChart]
  rw [← Category.assoc, joinStdSimplexIso_inv_comp_join_map_app]
  rfl

private theorem joinedLeftChart_natural {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    joinedLeftChart.{u} n ≫ (join.map (SSet.stdSimplex.map f)).app cospanShape =
      SSet.stdSimplex.map (AugmentedSimplexCategory.tensorHomOf f (𝟙 ⦋1⦌)) ≫ joinedLeftChart m := by
  simp only [joinedLeftChart, Category.assoc]
  rw [(join.map (SSet.stdSimplex.map f)).naturality cospanLeftChart]
  rw [← Category.assoc, joinStdSimplexIso_inv_comp_join_map_app]
  rfl

private theorem indexJoinIso_natural {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) :
    (join.map (SSet.stdSimplex.map f)).app cospanShape ≫ (indexJoinIso.{u} m).hom =
      (indexJoinIso n).hom ≫ nerveMap (indexMap f).monotone.functor := by
  apply (nativeJoinedShape_isPushout n).hom_ext
  · rw [← Category.assoc, joinedRightChart_natural, Category.assoc,
      joinedRightChart_indexJoinIso, ← Category.assoc, joinedRightChart_indexJoinIso]
    exact (indexRightChart_natural f).symm
  · rw [← Category.assoc, joinedLeftChart_natural, Category.assoc,
      joinedLeftChart_indexJoinIso, ← Category.assoc, joinedLeftChart_indexJoinIso]
    exact (indexLeftChart_natural f).symm

private def indexFunctorOfSimplex (Q : DiamondObjects.{max uObj uHom} ⥤ C) (n : ℕ)
    (g : (sliceOver (nerve C) (cospanInclusion ≫ nerveMapMax Q)).obj (op ⦋n⦌)) :
    ConeIndex.{max uObj uHom} n ⥤ C :=
  NerveUniverses.functorOfMapMax.{uObj, uHom} ((indexJoinIso n).inv ≫ g.val)

private theorem indexFunctorOfSimplex_right (Q : DiamondObjects.{max uObj uHom} ⥤ C) (n : ℕ)
    (g : (sliceOver (nerve C) (cospanInclusion ≫ nerveMapMax Q)).obj (op ⦋n⦌)) :
    indexRightFunctor n ⋙ indexFunctorOfSimplex Q n g = cospanInclusionFunctor ⋙ Q := by
  have hmap : nerveMapMax (indexRightFunctor n ⋙ indexFunctorOfSimplex Q n g) =
      nerveMapMax (cospanInclusionFunctor ⋙ Q) := by
    rw [← nerveMapMax_comp, indexFunctorOfSimplex, NerveUniverses.nerveMapMax_functorOfMapMax]
    rw [← indexJoinIso_right, Category.assoc, Iso.hom_inv_id_assoc, g.property]
    exact nerveMapMax_comp cospanInclusionFunctor Q
  have h := congrArg NerveUniverses.functorOfMapMax.{uObj, uHom} hmap
  simpa only [NerveUniverses.functorOfMapMax_nerveMapMax] using h

private def mixedArrow (n : ℕ) (i : Fin (n + 1)) (v : CospanObjects.{u}) :
    (indexLeftFunctor n).obj i ⟶ (indexRightFunctor n).obj v :=
  homOfLE (Sum.Lex.sep (ULift.up i) v)

private def coneChainOfIndexFunctor (F : CospanObjects.{max uObj uHom} ⥤ C) {n : ℕ}
    (G : ConeIndex.{max uObj uHom} n ⥤ C) (h : indexRightFunctor n ⋙ G = F) :
    ComposableArrows (Cone F) n where
  obj i :=
    { pt := (indexLeftFunctor n ⋙ G).obj i
      π :=
        { app v := G.map (mixedArrow n i v) ≫ eqToHom (Functor.congr_obj h v)
          naturality a b f := by
            change (𝟙 _) ≫ (G.map (mixedArrow n i b) ≫ eqToHom (Functor.congr_obj h b)) =
              (G.map (mixedArrow n i a) ≫ eqToHom (Functor.congr_obj h a)) ≫
                F.map f
            rw [Category.id_comp]
            have hh : G.map ((indexRightFunctor n).map f) ≫
                eqToHom (Functor.congr_obj h b) =
                eqToHom (Functor.congr_obj h a) ≫ F.map f := by
              have hh := Functor.congr_hom h f
              change G.map ((indexRightFunctor n).map f) = _ at hh
              rw [hh]
              simp
            calc
              _ = (G.map (mixedArrow n i a) ≫
                  G.map ((indexRightFunctor n).map f)) ≫ eqToHom (Functor.congr_obj h b) := by
                rw [← G.map_comp]
                rfl
              _ = _ := by rw [Category.assoc, hh, ← Category.assoc] } }
  map {i j} f :=
    { hom := (indexLeftFunctor n ⋙ G).map f
      w v := by
        change G.map ((indexLeftFunctor n).map f) ≫
          (G.map (mixedArrow n j v) ≫ eqToHom (Functor.congr_obj h v)) =
            G.map (mixedArrow n i v) ≫ eqToHom (Functor.congr_obj h v)
        rw [← Category.assoc, ← G.map_comp]
        rfl }
  map_id i := ConeMorphism.ext _ _ ((indexLeftFunctor n ⋙ G).map_id i)
  map_comp f g := ConeMorphism.ext _ _ ((indexLeftFunctor n ⋙ G).map_comp f g)

private def coneChainIndexObj (F : CospanObjects.{max uObj uHom} ⥤ C) {n : ℕ}
    (A : ComposableArrows (Cone F) n) : ConeIndex.{max uObj uHom} n → C := fun x =>
  match x with
  | .inl i => (A.obj i.down).pt
  | .inr v => F.obj v

private def coneChainIndexMap (F : CospanObjects.{max uObj uHom} ⥤ C) {n : ℕ}
    (A : ComposableArrows (Cone F) n) :
    ∀ (x y : ConeIndex.{max uObj uHom} n), x ≤ y → (coneChainIndexObj F A x ⟶ coneChainIndexObj F A y) := fun x y h =>
  match x, y, h with
  | .inl i, .inl j, h => by
      have hij : i ≤ j := Sum.Lex.inl_le_inl_iff.mp h
      exact (A.map (homOfLE hij)).hom
  | .inl i, .inr v, _ => (A.obj i.down).π.app v
  | .inr v, .inl i, h => (Sum.Lex.not_inr_le_inl h).elim
  | .inr v, .inr w, h =>
      F.map (homOfLE (Sum.Lex.inr_le_inr_iff.mp h))

private theorem coneChainIndexMap_id (F : CospanObjects.{max uObj uHom} ⥤ C) {n : ℕ}
    (A : ComposableArrows (Cone F) n) (x : ConeIndex.{max uObj uHom} n) :
    coneChainIndexMap F A x x le_rfl = 𝟙 (coneChainIndexObj F A x) := by
  rcases x with i | v
  · change (A.map (𝟙 i.down)).hom = 𝟙 (A.obj i.down).pt
    rw [A.map_id]
    rfl
  · exact F.map_id v

private theorem coneChainIndexMap_comp (F : CospanObjects.{max uObj uHom} ⥤ C) {n : ℕ}
    (A : ComposableArrows (Cone F) n)
    (x y z : ConeIndex.{max uObj uHom} n) (hxy : x ≤ y) (hyz : y ≤ z) :
    coneChainIndexMap F A x z (hxy.trans hyz) =
      coneChainIndexMap F A x y hxy ≫ coneChainIndexMap F A y z hyz := by
  rcases x with i | v <;> rcases y with j | w <;> rcases z with k | t
  · change (A.map (homOfLE _)).hom = (A.map (homOfLE _)).hom ≫ (A.map (homOfLE _)).hom
    exact congrArg ConeMorphism.hom (A.map_comp _ _)
  · have hij : i ≤ j := Sum.Lex.inl_le_inl_iff.mp hxy
    exact (A.map (homOfLE hij)).w t |>.symm
  · exact (Sum.Lex.not_inr_le_inl hyz).elim
  · exact (A.obj i.down).w (homOfLE (Sum.Lex.inr_le_inr_iff.mp hyz)) |>.symm
  · exact (Sum.Lex.not_inr_le_inl hxy).elim
  · exact (Sum.Lex.not_inr_le_inl hxy).elim
  · exact (Sum.Lex.not_inr_le_inl hyz).elim
  · exact F.map_comp
      (homOfLE (Sum.Lex.inr_le_inr_iff.mp hxy))
      (homOfLE (Sum.Lex.inr_le_inr_iff.mp hyz))

private def indexFunctorOfConeChain (F : CospanObjects.{max uObj uHom} ⥤ C) {n : ℕ}
    (A : ComposableArrows (Cone F) n) : ConeIndex.{max uObj uHom} n ⥤ C where
  obj := coneChainIndexObj F A
  map f := coneChainIndexMap F A _ _ (leOfHom f)
  map_id := coneChainIndexMap_id F A
  map_comp f g := coneChainIndexMap_comp F A _ _ _ (leOfHom f) (leOfHom g)

private theorem indexFunctorOfConeChain_right (F : CospanObjects.{max uObj uHom} ⥤ C) {n : ℕ}
    (A : ComposableArrows (Cone F) n) :
    indexRightFunctor n ⋙ indexFunctorOfConeChain F A = F := rfl

/-- The entire original joined simplex encoded by an ordinary chain of cones. -/
private def coneSimplexOfChain (Q : DiamondObjects.{max uObj uHom} ⥤ C) {n : ℕ}
    (A : ComposableArrows (Cone (cospanInclusionFunctor ⋙ Q)) n) :
    (sliceOver (nerve C) (cospanInclusion ≫ nerveMapMax Q)).obj (op ⦋n⦌) :=
  ⟨(indexJoinIso n).hom ≫ nerveMapMax (indexFunctorOfConeChain (cospanInclusionFunctor ⋙ Q) A), by
    rw [← Category.assoc, indexJoinIso_right, nerveMapMax_comp, indexFunctorOfConeChain_right]
    exact (nerveMapMax_comp cospanInclusionFunctor Q).symm⟩

/-- Recover the full ordinary cone chain from an original joined simplex. -/
private def coneChainOfSimplex (Q : DiamondObjects.{max uObj uHom} ⥤ C) {n : ℕ}
    (g : (sliceOver (nerve C) (cospanInclusion ≫ nerveMapMax Q)).obj (op ⦋n⦌)) :
    ComposableArrows (Cone (cospanInclusionFunctor ⋙ Q)) n :=
  coneChainOfIndexFunctor (cospanInclusionFunctor ⋙ Q) (indexFunctorOfSimplex Q n g)
    (indexFunctorOfSimplex_right Q n g)

private theorem indexFunctor_coneChainOfIndexFunctor (F : CospanObjects.{max uObj uHom} ⥤ C) {n : ℕ}
    (G : ConeIndex.{max uObj uHom} n ⥤ C) (h : indexRightFunctor n ⋙ G = F) :
    indexFunctorOfConeChain F (coneChainOfIndexFunctor F G h) = G := by
  subst F
  refine Functor.hext (fun x => by rcases x with i | v <;> rfl) ?_
  intro x y f
  rcases x with i | v <;> rcases y with j | w
  · apply heq_of_eq
    change G.map _ = G.map f
    congr 1
  · apply heq_of_eq
    change G.map (mixedArrow n i.down w) ≫ (𝟙 _) = G.map f
    rw [Category.comp_id]
    congr 1
  · exact (Sum.Lex.not_inr_le_inl (leOfHom f)).elim
  · apply heq_of_eq
    change G.map _ = G.map f
    congr 1

private theorem coneChain_indexFunctorOfConeChain (F : CospanObjects.{max uObj uHom} ⥤ C) {n : ℕ}
    (A : ComposableArrows (Cone F) n)
    (h : indexRightFunctor n ⋙ indexFunctorOfConeChain F A = F) :
    coneChainOfIndexFunctor F (indexFunctorOfConeChain F A) h = A := by
  have hobj : ∀ i, (coneChainOfIndexFunctor F (indexFunctorOfConeChain F A) h).obj i = A.obj i := by
    intro i
    change Cone.mk (A.obj i).pt _ = Cone.mk (A.obj i).pt (A.obj i).π
    apply congrArg (Cone.mk (A.obj i).pt)
    apply NatTrans.ext
    funext v
    exact Category.comp_id ((A.obj i).π.app v)
  refine CategoryTheory.Functor.ext hobj ?_
  intro i j f
  apply ConeMorphism.ext
  have hi : (eqToHom (hobj i)).hom = 𝟙 (A.obj i).pt := by
    change (Cone.forget F).map (eqToHom (hobj i)) = 𝟙 (A.obj i).pt
    rw [eqToHom_map]
    rfl
  have hj : (eqToHom (hobj j).symm).hom = 𝟙 (A.obj j).pt := by
    change (Cone.forget F).map (eqToHom (hobj j).symm) = 𝟙 (A.obj j).pt
    rw [eqToHom_map]
    rfl
  change (A.map f).hom = (eqToHom (hobj i)).hom ≫ (A.map f).hom ≫ (eqToHom (hobj j).symm).hom
  rw [hi, hj]
  exact (Category.comp_id (A.map f).hom).symm.trans (Category.id_comp _).symm

private theorem indexFunctorOfConeChain_operator (F : CospanObjects.{max uObj uHom} ⥤ C) {n m : ℕ}
    (f : ⦋n⦌ ⟶ ⦋m⦌) (A : ComposableArrows (Cone F) m) :
    indexFunctorOfConeChain F ((nerve (Cone F)).map f.op A) =
      (indexMap f).monotone.functor ⋙ indexFunctorOfConeChain F A := by
  refine Functor.hext (fun x => by rcases x with i | v <;> rfl) ?_
  intro x y k
  rcases x with i | v <;> rcases y with j | w
  · rfl
  · rfl
  · exact (Sum.Lex.not_inr_le_inl (leOfHom k)).elim
  · rfl

private theorem indexFunctorOfSimplex_coneSimplexOfChain (Q : DiamondObjects.{max uObj uHom} ⥤ C) {n : ℕ}
    (A : ComposableArrows (Cone (cospanInclusionFunctor ⋙ Q)) n) :
    indexFunctorOfSimplex Q n (coneSimplexOfChain Q A) =
      indexFunctorOfConeChain (cospanInclusionFunctor ⋙ Q) A := by
  change NerveUniverses.functorOfMapMax.{uObj, uHom} ((indexJoinIso n).inv ≫
    ((indexJoinIso n).hom ≫ nerveMapMax (indexFunctorOfConeChain (cospanInclusionFunctor ⋙ Q) A))) = _
  rw [Iso.inv_hom_id_assoc]
  exact NerveUniverses.functorOfMapMax_nerveMapMax _

/-- Converting an ordinary cone chain to its whole native simplex and back keeps that chain. -/
private theorem coneChainOfSimplex_coneSimplexOfChain (Q : DiamondObjects.{max uObj uHom} ⥤ C) {n : ℕ}
    (A : ComposableArrows (Cone (cospanInclusionFunctor ⋙ Q)) n) :
    coneChainOfSimplex Q (coneSimplexOfChain Q A) = A := by
  unfold coneChainOfSimplex
  simp only [indexFunctorOfSimplex_coneSimplexOfChain]
  exact coneChain_indexFunctorOfConeChain _ A _

/-- Converting a whole native cone simplex to its ordinary chain and back keeps the entire map. -/
private theorem coneSimplexOfChain_coneChainOfSimplex (Q : DiamondObjects.{max uObj uHom} ⥤ C) {n : ℕ}
    (g : (sliceOver (nerve C) (cospanInclusion ≫ nerveMapMax Q)).obj (op ⦋n⦌)) :
    coneSimplexOfChain Q (coneChainOfSimplex Q g) = g := by
  apply Subtype.ext
  change (indexJoinIso n).hom ≫ nerveMapMax
    (indexFunctorOfConeChain (cospanInclusionFunctor ⋙ Q)
      (coneChainOfIndexFunctor (cospanInclusionFunctor ⋙ Q) (indexFunctorOfSimplex Q n g)
        (indexFunctorOfSimplex_right Q n g))) = g.val
  rw [indexFunctor_coneChainOfIndexFunctor, indexFunctorOfSimplex,
    NerveUniverses.nerveMapMax_functorOfMapMax, Iso.hom_inv_id_assoc]

/-- Every simplex operator retains the entire ordinary cone chain's native joined map. -/
private theorem coneSimplexOfChain_natural (Q : DiamondObjects.{max uObj uHom} ⥤ C) {n m : ℕ}
    (f : ⦋n⦌ ⟶ ⦋m⦌) (A : ComposableArrows (Cone (cospanInclusionFunctor ⋙ Q)) m) :
    coneSimplexOfChain Q ((nerve (Cone (cospanInclusionFunctor ⋙ Q))).map f.op A) =
      (sliceOver (nerve C) (cospanInclusion ≫ nerveMapMax Q)).map f.op (coneSimplexOfChain Q A) := by
  apply Subtype.ext
  change (indexJoinIso n).hom ≫ nerveMapMax
      (indexFunctorOfConeChain (cospanInclusionFunctor ⋙ Q)
        ((nerve (Cone (cospanInclusionFunctor ⋙ Q))).map f.op A)) =
    (join.map (SSet.stdSimplex.map f)).app cospanShape ≫
      ((indexJoinIso m).hom ≫ nerveMapMax (indexFunctorOfConeChain (cospanInclusionFunctor ⋙ Q) A))
  rw [indexFunctorOfConeChain_operator, ← nerveMapMax_comp, ← Category.assoc,
    ← indexJoinIso_natural, Category.assoc]

private def coneSimplexEquiv (Q : DiamondObjects.{max uObj uHom} ⥤ C) (n : ℕ) :
    (nerve (Cone (cospanInclusionFunctor ⋙ Q))).obj (op ⦋n⦌) ≃
      (sliceOver (nerve C) (cospanInclusion ≫ nerveMapMax Q)).obj (op ⦋n⦌) where
  toFun := coneSimplexOfChain Q
  invFun := coneChainOfSimplex Q
  left_inv := coneChainOfSimplex_coneSimplexOfChain Q
  right_inv := coneSimplexOfChain_coneChainOfSimplex Q

private def coneNerveNativeIso (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    nerve (Cone (cospanInclusionFunctor ⋙ Q)) ≅
      sliceOver (nerve C) (cospanInclusion ≫ nerveMapMax Q) :=
  NatIso.ofComponents (fun q => (coneSimplexEquiv Q q.unop.len).toIso)
    (by
      intro q r f
      apply ConcreteCategory.hom_ext
      intro A
      exact coneSimplexOfChain_natural Q f.unop A)

/-- The whole original over-slice is the nerve of the actual ordinary cone category. -/
private def nerveConeIso (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    sliceOver (nerve C) (cospanInclusion ≫ nerveMapMax Q) ≅
      nerve (Cone (cospanInclusionFunctor ⋙ Q)) :=
  (coneNerveNativeIso Q).symm

/-- The native comparison reads each original simplex as its entire chain of ordinary cones. -/
private theorem nerveConeIso_hom_app (Q : DiamondObjects.{max uObj uHom} ⥤ C) {n : ℕ}
    (g : (sliceOver (nerve C) (cospanInclusion ≫ nerveMapMax Q)).obj (op ⦋n⦌)) :
    (nerveConeIso Q).hom.app (op ⦋n⦌) g = coneChainOfSimplex Q g := rfl

/-- The inverse comparison reads an entire ordinary cone chain as its original whole joined map. -/
private theorem nerveConeIso_inv_app (Q : DiamondObjects.{max uObj uHom} ⥤ C) {n : ℕ}
    (A : (nerve (Cone (cospanInclusionFunctor ⋙ Q))).obj (op ⦋n⦌)) :
    (nerveConeIso Q).inv.app (op ⦋n⦌) A = coneSimplexOfChain Q A := rfl

/-- Forgetting the ordinary cone legs keeps the complete original free-apex chain. -/
private theorem coneChainOfSimplex_forget (Q : DiamondObjects.{max uObj uHom} ⥤ C) {n : ℕ}
    (g : (sliceOver (nerve C) (cospanInclusion ≫ nerveMapMax Q)).obj (op ⦋n⦌)) :
    coneChainOfSimplex Q g ⋙ Cone.forget (cospanInclusionFunctor ⋙ Q) =
      (sliceOver.proj (nerve C) (cospanInclusion ≫ nerveMapMax Q)).app (op ⦋n⦌) g := by
  change indexLeftFunctor n ⋙ indexFunctorOfSimplex Q n g =
    yonedaEquiv (joinInl Δ[n] cospanShape ≫ g.val)
  calc
    _ = yonedaEquiv (yonedaEquiv.symm (indexLeftFunctor n) ≫
        nerveMapMax (indexFunctorOfSimplex Q n g)) := by
      exact ((congrArg yonedaEquiv (yonedaEquiv_symm_comp (indexLeftFunctor n)
        (nerveMapMax (indexFunctorOfSimplex Q n g)))).trans (yonedaEquiv.apply_symm_apply _)).symm
    _ = _ := by
      rw [indexFunctorOfSimplex, NerveUniverses.nerveMapMax_functorOfMapMax,
        ← indexJoinIso_left, Category.assoc, Iso.hom_inv_id_assoc]

/-- The native over-slice projection is exactly the nerve of the ordinary cone forgetful functor. -/
private theorem nerveConeIso_hom_comp_nerveMap_forget (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    (nerveConeIso Q).hom ≫ nerveMapCross (Cone.forget (cospanInclusionFunctor ⋙ Q)) =
      sliceOver.proj (nerve C) (cospanInclusion ≫ nerveMapMax Q) := by
  ext q g
  change coneChainOfSimplex Q g ⋙ Cone.forget (cospanInclusionFunctor ⋙ Q) =
    (sliceOver.proj (nerve C) (cospanInclusion ≫ nerveMapMax Q)).app q g
  exact coneChainOfSimplex_forget Q g

private def indexZeroToSquare : ConeIndex.{u} 0 ⥤ DiamondObjects.{u} :=
  (show Monotone (fun x : ConeIndex.{u} 0 => match x with
      | Sum.inlₗ _ => (⟨(0, 0)⟩ : DiamondObjects.{u})
      | Sum.inrₗ v => v.val) from by
    rintro (i | v) (j | w) h
    · exact le_rfl
    · exact ⟨Fin.zero_le _, Fin.zero_le _⟩
    · exact (Sum.Lex.not_inr_le_inl h).elim
    · have h' : v ≤ w := Sum.Lex.inr_le_inr_iff.mp h
      exact h').functor

private theorem indexRightChart_zero_toSquare :
    indexRightChart.{u} 0 ≫ nerveMap indexZeroToSquare = rightTriangle := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

private theorem indexLeftChart_zero_toSquare :
    indexLeftChart.{u} 0 ≫ nerveMap indexZeroToSquare = leftTriangle := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

private theorem indexZeroToSquare_comp_shapeJoinIso :
    nerveMap indexZeroToSquare.{u} ≫ shapeJoinIso.hom = (indexJoinIso 0).inv := by
  apply (indexShape_isPushout 0).hom_ext
  · calc
      indexRightChart 0 ≫ (nerveMap indexZeroToSquare ≫ shapeJoinIso.hom) =
          rightTriangle ≫ shapeJoinIso.hom := by
        rw [← Category.assoc, indexRightChart_zero_toSquare]
      _ = joinedRightChart 0 := rightTriangle_comp_shapeJoinIso_hom
      _ = indexRightChart 0 ≫ (indexJoinIso 0).inv :=
        ((nativeJoinedShape_isPushout 0).inl_isoIsPushout_inv _ _ (indexShape_isPushout 0)).symm
  · calc
      indexLeftChart 0 ≫ (nerveMap indexZeroToSquare ≫ shapeJoinIso.hom) =
          leftTriangle ≫ shapeJoinIso.hom := by
        rw [← Category.assoc, indexLeftChart_zero_toSquare]
      _ = joinedLeftChart 0 := leftTriangle_comp_shapeJoinIso_hom
      _ = indexLeftChart 0 ≫ (indexJoinIso 0).inv :=
        ((nativeJoinedShape_isPushout 0).inr_isoIsPushout_inv _ _ (indexShape_isPushout 0)).symm

private theorem indexFunctorOfSimplex_squareConeSimplex (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    indexFunctorOfSimplex Q 0 (squareConeSimplex Q) = indexZeroToSquare ⋙ Q := by
  change NerveUniverses.functorOfMapMax.{uObj, uHom} ((indexJoinIso 0).inv ≫
    (shapeJoinIso.inv ≫ nerveMapMax Q)) = indexZeroToSquare ⋙ Q
  rw [← indexZeroToSquare_comp_shapeJoinIso, Category.assoc, Iso.hom_inv_id_assoc,
    nerveMapMax_comp]
  exact NerveUniverses.functorOfMapMax_nerveMapMax _

private theorem coneChainOfIndexFunctor_zero (Q : DiamondObjects.{max uObj uHom} ⥤ C)
    (h : indexRightFunctor 0 ⋙ (indexZeroToSquare ⋙ Q) = cospanInclusionFunctor ⋙ Q) :
    coneChainOfIndexFunctor (cospanInclusionFunctor ⋙ Q) (indexZeroToSquare ⋙ Q) h =
      ComposableArrows.mk₀ (ordinaryCone Q) := by
  apply ComposableArrows.ext₀
  change Cone.mk (ordinaryCone Q).pt _ = Cone.mk (ordinaryCone Q).pt (ordinaryCone Q).π
  apply congrArg (Cone.mk (ordinaryCone Q).pt)
  apply NatTrans.ext
  funext v
  change (ordinaryCone Q).π.app v ≫ (𝟙 _) = (ordinaryCone Q).π.app v
  exact Category.comp_id _

/-- Reading the original whole square cone gives its original ordinary cone at the initial object. -/
private theorem coneChainOfSimplex_squareConeSimplex (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    coneChainOfSimplex Q (squareConeSimplex Q) = ComposableArrows.mk₀ (ordinaryCone Q) := by
  unfold coneChainOfSimplex
  simp only [indexFunctorOfSimplex_squareConeSimplex]
  exact coneChainOfIndexFunctor_zero Q _

/-- The zero-simplex readback of the entire original coherent cone is exactly its ordinary cone. -/
private theorem nerveConeIso_hom_squareConeSimplex (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    (nerveConeIso Q).hom.app (op ⦋0⦌) (squareConeSimplex Q) =
      ComposableArrows.mk₀ (ordinaryCone Q) := by
  rw [nerveConeIso_hom_app, coneChainOfSimplex_squareConeSimplex]

/-- The original whole cone point is sent to the actual point of its original ordinary cone. -/
private theorem squareConePoint_comp_nerveConeIso_hom (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    squareConePoint Q ≫ (nerveConeIso Q).hom = yonedaEquiv.symm (ComposableArrows.mk₀ (ordinaryCone Q)) := by
  rw [squareConePoint, yonedaEquiv_symm_comp, nerveConeIso_hom_squareConeSimplex]


end SSet.NativePullback.Coordinate

namespace SSet.NativePullback

variable {C : Type uObj} [Category.{uHom} C]

/-- The canonical ordinary cone, obtained from the native WithInitial universal construction. -/
@[expose] def ordinaryCone (Q : DiamondObjects.{u} ⥤ C) : Cone (cospanInclusionFunctor ⋙ Q) where
  pt := Q.obj WithInitial.star
  π := (WithInitial.mkCommaObject Q).hom

/-- The first cone leg is the top arrow of the original square. -/
theorem ordinaryCone_right (Q : DiamondObjects.{u} ⥤ C) :
    (ordinaryCone Q).π.app (ULift.up WalkingCospan.left) =
      Q.map (WithInitial.homTo (ULift.up WalkingCospan.left)) := rfl

/-- The second cone leg is the left arrow of the original square. -/
theorem ordinaryCone_left (Q : DiamondObjects.{u} ⥤ C) :
    (ordinaryCone Q).π.app (ULift.up WalkingCospan.right) =
      Q.map (WithInitial.homTo (ULift.up WalkingCospan.right)) := rfl

/-- The target cone leg is the common initial-to-target diagonal. -/
theorem ordinaryCone_target (Q : DiamondObjects.{u} ⥤ C) :
    (ordinaryCone Q).π.app (ULift.up WalkingCospan.one) =
      Q.map (WithInitial.homTo (ULift.up WalkingCospan.one)) := rfl

/-- The first cospan arrow is the original right square side. -/
theorem ordinaryDiagram_right (Q : DiamondObjects.{u} ⥤ C) :
    (cospanInclusionFunctor ⋙ Q).map
      (show (ULift.up WalkingCospan.left : CospanObjects.{u}) ⟶ ULift.up WalkingCospan.one from
        WalkingCospan.Hom.inl) =
      Q.map (WithInitial.incl.map (show (ULift.up WalkingCospan.left : CospanObjects.{u}) ⟶
        ULift.up WalkingCospan.one from WalkingCospan.Hom.inl)) := rfl

/-- The second cospan arrow is the original bottom square side. -/
theorem ordinaryDiagram_bottom (Q : DiamondObjects.{u} ⥤ C) :
    (cospanInclusionFunctor ⋙ Q).map
      (show (ULift.up WalkingCospan.right : CospanObjects.{u}) ⟶ ULift.up WalkingCospan.one from
        WalkingCospan.Hom.inr) =
      Q.map (WithInitial.incl.map (show (ULift.up WalkingCospan.right : CospanObjects.{u}) ⟶
        ULift.up WalkingCospan.one from WalkingCospan.Hom.inr)) := rfl

section

attribute [local instance] CategoryTheory.uliftCategory

/-- A native Hom-universe-zero index maps to the original category at its common nerve universe. -/
@[expose] def nerveMapIndex {A : Type (max uObj uHom)} [Category.{0} A] (F : A ⥤ C) :
    nerve A ⟶ nerve C :=
  nerveMapHomDown (F ⋙ ULift.upFunctor) ≫ nerveMapCross ULift.downFunctor

/-- The canonical index map preserves each whole original chain. -/
theorem nerveMapIndex_app {A : Type (max uObj uHom)} [Category.{0} A] (F : A ⥤ C)
    (n : SimplexCategoryᵒᵖ) (s : ComposableArrows A n.unop.len) :
    (nerveMapIndex F).app n s = (F.mapComposableArrows _).obj s := rfl

end

/-- The full canonical cone simplex retains the original square functor. -/
@[expose] def squareConeSimplex (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    (sliceOver (nerve C) (cospanInclusion ≫ nerveMapIndex Q)).obj (op ⦋0⦌) :=
  ⟨shapeJoinIso.inv ≫ nerveMapIndex Q, by
    rw [← cospanInclusion_comp_shapeJoinIso_hom]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]⟩

/-- The entire canonical cone as a native point in its actual over-slice. -/
@[expose] def squareConePoint (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    (Δ[0] : SSet.{max uObj uHom}) ⟶ sliceOver (nerve C) (cospanInclusion ≫ nerveMapIndex Q) :=
  yonedaEquiv.symm (squareConeSimplex Q)

section

universe uJ vJ uK vK
variable {J : Type uJ} [Category.{vJ} J] {K : Type uK} [Category.{vK} K]
variable {F : J ⥤ C}

private theorem cone_eq_of_iso_identity {s t : Cone F} (i : s ≅ t)
    (hpt : s.pt = t.pt) (hh : i.hom.hom = eqToHom hpt) : s = t := by
  rcases s with ⟨s, sp⟩
  rcases t with ⟨t, tp⟩
  dsimp at hpt
  subst t
  have hp : sp = tp := by
    apply NatTrans.ext
    funext j
    have h := i.hom.w j
    rw [hh, eqToHom_refl, Category.id_comp] at h
    exact h.symm
  cases hp
  rfl

private theorem coneFunctor_eq_id (H : Cone F ⥤ Cone F) (i : H ≅ 𝟭 (Cone F))
    (hpt : ∀ s, (H.obj s).pt = s.pt)
    (hh : ∀ s, (i.hom.app s).hom = eqToHom (hpt s)) : H = 𝟭 (Cone F) := by
  have ho : ∀ s, H.obj s = s := fun s => cone_eq_of_iso_identity (i.app s) (hpt s) (hh s)
  have hi : ∀ s, i.hom.app s = eqToHom (ho s) := by
    intro s
    apply ConeMorphism.ext
    change (i.hom.app s).hom = (Cone.forget F).map (eqToHom (ho s))
    rw [eqToHom_map]
    exact hh s
  refine CategoryTheory.Functor.ext ho ?_
  intro s t f
  have h := congrArg (fun g => g ≫ eqToHom (ho t).symm) (i.hom.naturality f)
  simpa only [hi, CategoryTheory.Functor.id_map, Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id] using h



private theorem coneEquivalence_unit (e : J ≌ K) (F : K ⥤ C) (G : J ⥤ C)
    (α : e.functor ⋙ F ≅ G) :
    (Cone.equivalenceOfReindexing e α).functor ⋙ (Cone.equivalenceOfReindexing e α).inverse =
      𝟭 (Cone F) := by
  have hp : ∀ s, (((Cone.equivalenceOfReindexing e α).functor ⋙
      (Cone.equivalenceOfReindexing e α).inverse).obj s).pt = s.pt := fun _ => rfl
  apply coneFunctor_eq_id _ (Cone.equivalenceOfReindexing e α).unitIso.symm hp
  intro s
  dsimp [Cone.equivalenceOfReindexing, CategoryTheory.Equivalence.trans,
    Cone.whiskeringEquivalence, Cone.postcomposeEquivalence, Cone.ext, NatIso.ofComponents]
  simp
  change (𝟙 s.pt) = (𝟙 s.pt)
  rfl

private theorem coneEquivalence_counit (e : J ≌ K) (F : K ⥤ C) (G : J ⥤ C)
    (α : e.functor ⋙ F ≅ G) :
    (Cone.equivalenceOfReindexing e α).inverse ⋙ (Cone.equivalenceOfReindexing e α).functor =
      𝟭 (Cone G) := by
  have hp : ∀ s, (((Cone.equivalenceOfReindexing e α).inverse ⋙
      (Cone.equivalenceOfReindexing e α).functor).obj s).pt = s.pt := fun _ => rfl
  apply coneFunctor_eq_id _ (Cone.equivalenceOfReindexing e α).counitIso hp
  intro s
  dsimp [Cone.equivalenceOfReindexing, CategoryTheory.Equivalence.trans,
    Cone.whiskeringEquivalence, Cone.postcomposeEquivalence, Cone.ext, NatIso.ofComponents]
  simp
  change (𝟙 s.pt) = (𝟙 s.pt)
  rfl

private theorem coneEquivalence_forwardLeg (e : J ≌ K) (F : K ⥤ C) (G : J ⥤ C)
    (h : e.functor ⋙ F = G) (s : Cone F) (j : J) :
    ((Cone.equivalenceOfReindexing e (eqToIso h)).functor.obj s).π.app j =
      s.π.app (e.functor.obj j) ≫ eqToHom (CategoryTheory.Functor.congr_obj h j) := by
  dsimp [Cone.equivalenceOfReindexing, CategoryTheory.Equivalence.trans,
    CategoryTheory.Functor.comp, NatTrans.vcomp, CategoryTheory.eqToIso,
    Cone.whiskeringEquivalence, Cone.whiskering, Cone.whisker,
    Cone.postcomposeEquivalence, Cone.postcompose, CategoryTheory.Functor.whiskerLeft]
  rw [CategoryTheory.eqToHom_app]

end

private abbrev pulledSquare (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    Coordinate.DiamondObjects.{max uObj uHom} ⥤ C :=
  Coordinate.squareToCanonical ⋙ Q

private theorem pulledDiagram_eq (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    Coordinate.cospanEquivalence.functor ⋙ (cospanInclusionFunctor ⋙ Q) =
      Coordinate.cospanInclusionFunctor ⋙ pulledSquare Q :=
  (congrArg (fun F => F ⋙ Q) Coordinate.inclusion_toCanonical).symm

private def coneEquivalence (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    Cone (cospanInclusionFunctor ⋙ Q) ≌
      Cone (Coordinate.cospanInclusionFunctor ⋙ pulledSquare Q) :=
  Cone.equivalenceOfReindexing Coordinate.cospanEquivalence (eqToIso (pulledDiagram_eq Q))

private theorem pulledNerveMap (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    Coordinate.squareIso.hom ≫ nerveMapIndex Q =
      CategoryTheory.NerveUniverses.nerveMapMax (pulledSquare Q) := by
  ext n s
  rfl

private theorem pulledNativeDiagram_eq (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    Coordinate.cospanIso.hom ≫ (cospanInclusion ≫ nerveMapIndex Q) =
      Coordinate.cospanInclusion ≫ CategoryTheory.NerveUniverses.nerveMapMax (pulledSquare Q) := by
  rw [← Category.assoc, ← Coordinate.inclusion_squareIso, Category.assoc, pulledNerveMap]

private def coordinateOverIso (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    sliceOver (nerve C) (cospanInclusion ≫ nerveMapIndex Q) ≅
      sliceOver (nerve C) (Coordinate.cospanInclusion ≫
        CategoryTheory.NerveUniverses.nerveMapMax (pulledSquare Q)) :=
  sliceOver.indexIso (nerve C) (cospanInclusion ≫ nerveMapIndex Q) Coordinate.cospanIso ≪≫
    eqToIso (congrArg (sliceOver (nerve C)) (pulledNativeDiagram_eq Q))

private def coneNerveIso (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    nerve (Cone (cospanInclusionFunctor ⋙ Q)) ≅
      nerve (Cone (Coordinate.cospanInclusionFunctor ⋙ pulledSquare Q)) where
  hom := nerveMap (coneEquivalence Q).functor
  inv := nerveMap (coneEquivalence Q).inverse
  hom_inv_id := by
    rw [nerveMap_comp]
    have h := coneEquivalence_unit Coordinate.cospanEquivalence (cospanInclusionFunctor ⋙ Q)
      (Coordinate.cospanInclusionFunctor ⋙ pulledSquare Q) (eqToIso (pulledDiagram_eq Q))
    change nerveMap ((coneEquivalence Q).functor ⋙ (coneEquivalence Q).inverse) = _
    rw [show (coneEquivalence Q).functor ⋙ (coneEquivalence Q).inverse = 𝟭 _ from h]
    ext n s
    rfl
  inv_hom_id := by
    rw [nerveMap_comp]
    have h := coneEquivalence_counit Coordinate.cospanEquivalence (cospanInclusionFunctor ⋙ Q)
      (Coordinate.cospanInclusionFunctor ⋙ pulledSquare Q) (eqToIso (pulledDiagram_eq Q))
    change nerveMap ((coneEquivalence Q).inverse ⋙ (coneEquivalence Q).functor) = _
    rw [show (coneEquivalence Q).inverse ⋙ (coneEquivalence Q).functor = 𝟭 _ from h]
    ext n s
    rfl

/-- The full native fixed-cospan slice is the nerve of the actual canonical cone category. -/
def nerveConeIso (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    sliceOver (nerve C) (cospanInclusion ≫ nerveMapIndex Q) ≅
      nerve (Cone (cospanInclusionFunctor ⋙ Q)) :=
  coordinateOverIso Q ≪≫ Coordinate.nerveConeIso (pulledSquare Q) ≪≫ (coneNerveIso Q).symm

private theorem nerveConeIso_hom_definition (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    (nerveConeIso Q).hom = (coordinateOverIso Q).hom ≫
      (Coordinate.nerveConeIso (pulledSquare Q)).hom ≫ nerveMap (coneEquivalence Q).inverse := rfl

private theorem nerveConeIso_inv_definition (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    (nerveConeIso Q).inv = nerveMap (coneEquivalence Q).functor ≫
      (Coordinate.nerveConeIso (pulledSquare Q)).inv ≫ (coordinateOverIso Q).inv := rfl

attribute [irreducible] nerveConeIso

/-- Read every original simplex as a chain of actual canonical cones. -/
@[expose] def coneChainOfSimplex (Q : DiamondObjects.{max uObj uHom} ⥤ C) {n : ℕ}
    (g : (sliceOver (nerve C) (cospanInclusion ≫ nerveMapIndex Q)).obj (op ⦋n⦌)) :
    ComposableArrows (Cone (cospanInclusionFunctor ⋙ Q)) n :=
  (nerveConeIso Q).hom.app (op ⦋n⦌) g

/-- Reconstruct every whole slice simplex from its actual canonical cone chain. -/
@[expose] def coneSimplexOfChain (Q : DiamondObjects.{max uObj uHom} ⥤ C) {n : ℕ}
    (A : ComposableArrows (Cone (cospanInclusionFunctor ⋙ Q)) n) :
    (sliceOver (nerve C) (cospanInclusion ≫ nerveMapIndex Q)).obj (op ⦋n⦌) :=
  (nerveConeIso Q).inv.app (op ⦋n⦌) A

/-- The native cone-nerve isomorphism reads the original complete cone chain. -/
theorem nerveConeIso_hom_app (Q : DiamondObjects.{max uObj uHom} ⥤ C) {n : ℕ}
    (g : (sliceOver (nerve C) (cospanInclusion ≫ nerveMapIndex Q)).obj (op ⦋n⦌)) :
    (nerveConeIso Q).hom.app (op ⦋n⦌) g = coneChainOfSimplex Q g := rfl

/-- The native inverse retains each whole cone-chain simplex. -/
theorem nerveConeIso_inv_app (Q : DiamondObjects.{max uObj uHom} ⥤ C) {n : ℕ}
    (A : ComposableArrows (Cone (cospanInclusionFunctor ⋙ Q)) n) :
    (nerveConeIso Q).inv.app (op ⦋n⦌) A = coneSimplexOfChain Q A := rfl

/-- Reading after reconstruction returns the actual whole canonical cone chain. -/
theorem coneChainOfSimplex_coneSimplexOfChain (Q : DiamondObjects.{max uObj uHom} ⥤ C) {n : ℕ}
    (A : ComposableArrows (Cone (cospanInclusionFunctor ⋙ Q)) n) :
    coneChainOfSimplex Q (coneSimplexOfChain Q A) = A := by
  have h := NatTrans.congr_app (nerveConeIso Q).inv_hom_id (op ⦋n⦌)
  exact ConcreteCategory.congr_hom h A

/-- Reconstructing after reading returns the original whole slice simplex. -/
theorem coneSimplexOfChain_coneChainOfSimplex (Q : DiamondObjects.{max uObj uHom} ⥤ C) {n : ℕ}
    (g : (sliceOver (nerve C) (cospanInclusion ≫ nerveMapIndex Q)).obj (op ⦋n⦌)) :
    coneSimplexOfChain Q (coneChainOfSimplex Q g) = g := by
  have h := NatTrans.congr_app (nerveConeIso Q).hom_inv_id (op ⦋n⦌)
  exact ConcreteCategory.congr_hom h g

/-- Native simplex reading commutes with every original simplicial operator. -/
theorem coneChainOfSimplex_natural (Q : DiamondObjects.{max uObj uHom} ⥤ C) {n m : ℕ}
    (f : ⦋n⦌ ⟶ ⦋m⦌)
    (g : (sliceOver (nerve C) (cospanInclusion ≫ nerveMapIndex Q)).obj (op ⦋m⦌)) :
    (nerve (Cone (cospanInclusionFunctor ⋙ Q))).map f.op (coneChainOfSimplex Q g) =
      coneChainOfSimplex Q ((sliceOver (nerve C) (cospanInclusion ≫ nerveMapIndex Q)).map f.op g) :=
  (NatTrans.naturality_apply (nerveConeIso Q).hom f.op g).symm

private theorem coneEquivalence_inverse_forget (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    (coneEquivalence Q).inverse ⋙ Cone.forget (cospanInclusionFunctor ⋙ Q) =
      Cone.forget (Coordinate.cospanInclusionFunctor ⋙ pulledSquare Q) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro s t f
  change f.hom = (𝟙 _) ≫ f.hom ≫ (𝟙 _)
  simp

private theorem coordinateOverIso_hom_comp_proj (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    (coordinateOverIso Q).hom ≫ sliceOver.proj (nerve C)
      (Coordinate.cospanInclusion ≫ CategoryTheory.NerveUniverses.nerveMapMax (pulledSquare Q)) =
        sliceOver.proj (nerve C) (cospanInclusion ≫ nerveMapIndex Q) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro g
  have hc : ((coordinateOverIso Q).hom.app n g).val =
      (join.obj (stdSimplex.obj n.unop)).map Coordinate.cospanIso.hom ≫ g.val :=
    sliceOver.fixedDiagramEq_app_val (pulledNativeDiagram_eq Q) n
      ((sliceOver.indexIso (nerve C) (cospanInclusion ≫ nerveMapIndex Q)
        Coordinate.cospanIso).hom.app n g)
  change yonedaEquiv (joinInl (stdSimplex.obj n.unop) Coordinate.cospanShape ≫
      ((coordinateOverIso Q).hom.app n g).val) =
    yonedaEquiv (joinInl (stdSimplex.obj n.unop) cospanShape ≫ g.val)
  rw [hc, ← Category.assoc, joinInl_comp_map]

/-- Reading canonical cones preserves every original apex-chain projection. -/
theorem nerveConeIso_hom_comp_nerveMap_forget (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    (nerveConeIso Q).hom ≫ nerveMapCross (Cone.forget (cospanInclusionFunctor ⋙ Q)) =
      sliceOver.proj (nerve C) (cospanInclusion ≫ nerveMapIndex Q) := by
  have hf : nerveMap (coneEquivalence Q).inverse ≫
      nerveMapCross (Cone.forget (cospanInclusionFunctor ⋙ Q)) =
        nerveMapCross (Cone.forget (Coordinate.cospanInclusionFunctor ⋙ pulledSquare Q)) := by
    rw [nerveMap_nerveMapCross_comp, coneEquivalence_inverse_forget]
  rw [nerveConeIso_hom_definition]
  simp only [Category.assoc]
  rw [hf, Coordinate.nerveConeIso_hom_comp_nerveMap_forget, coordinateOverIso_hom_comp_proj]

/-- The whole canonical cone chain forgets to the actual original apex chain. -/
theorem coneChainOfSimplex_forget (Q : DiamondObjects.{max uObj uHom} ⥤ C) {n : ℕ}
    (g : (sliceOver (nerve C) (cospanInclusion ≫ nerveMapIndex Q)).obj (op ⦋n⦌)) :
    coneChainOfSimplex Q g ⋙ Cone.forget (cospanInclusionFunctor ⋙ Q) =
      (sliceOver.proj (nerve C) (cospanInclusion ≫ nerveMapIndex Q)).app (op ⦋n⦌) g := by
  have h := NatTrans.congr_app (nerveConeIso_hom_comp_nerveMap_forget Q) (op ⦋n⦌)
  exact ConcreteCategory.congr_hom h g

/-- Reconstructing a whole native simplex commutes with every simplicial operator. -/
theorem coneSimplexOfChain_natural (Q : DiamondObjects.{max uObj uHom} ⥤ C) {n m : ℕ}
    (f : ⦋n⦌ ⟶ ⦋m⦌) (A : ComposableArrows (Cone (cospanInclusionFunctor ⋙ Q)) m) :
    coneSimplexOfChain Q ((nerve (Cone (cospanInclusionFunctor ⋙ Q))).map f.op A) =
      (sliceOver (nerve C) (cospanInclusion ≫ nerveMapIndex Q)).map f.op (coneSimplexOfChain Q A) :=
  NatTrans.naturality_apply (nerveConeIso Q).inv f.op A

private theorem coordinateOverIso_hom_squareConeSimplex
    (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    (coordinateOverIso Q).hom.app (op ⦋0⦌) (squareConeSimplex Q) =
      Coordinate.squareConeSimplex (pulledSquare Q) := by
  apply Subtype.ext
  have hc : ((coordinateOverIso Q).hom.app (op ⦋0⦌) (squareConeSimplex Q)).val =
      (join.obj (Δ[0] : SSet.{max uObj uHom})).map Coordinate.cospanIso.hom ≫
        (squareConeSimplex Q).val :=
    sliceOver.fixedDiagramEq_app_val (pulledNativeDiagram_eq Q) (op ⦋0⦌)
      ((sliceOver.indexIso (nerve C) (cospanInclusion ≫ nerveMapIndex Q)
        Coordinate.cospanIso).hom.app (op ⦋0⦌) (squareConeSimplex Q))
  rw [hc]
  change (join.obj (Δ[0] : SSet.{max uObj uHom})).map Coordinate.cospanIso.hom ≫
      ((join.obj (Δ[0] : SSet.{max uObj uHom})).map Coordinate.cospanIso.inv ≫
        (Coordinate.shapeJoinIso.inv ≫ Coordinate.squareIso.hom)) ≫ nerveMapIndex Q = _
  calc
    _ = (join.obj (Δ[0] : SSet.{max uObj uHom})).map
        (Coordinate.cospanIso.hom ≫ Coordinate.cospanIso.inv) ≫
          (Coordinate.shapeJoinIso.inv ≫ Coordinate.squareIso.hom ≫ nerveMapIndex Q) := by
      rw [CategoryTheory.Functor.map_comp]
      simp only [Category.assoc]
    _ = Coordinate.shapeJoinIso.inv ≫ Coordinate.squareIso.hom ≫ nerveMapIndex Q := by
      rw [Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
    _ = _ := by rw [pulledNerveMap]; rfl

private theorem coneEquivalence_functor_ordinaryCone
    (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    (coneEquivalence Q).functor.obj (ordinaryCone Q) = Coordinate.ordinaryCone (pulledSquare Q) := by
  let hi : (coneEquivalence Q).functor.obj (ordinaryCone Q) ≅
      Coordinate.ordinaryCone (pulledSquare Q) := by
    refine Cone.ext (Iso.refl (Q.obj WithInitial.star)) ?_
    intro j
    change ((Cone.equivalenceOfReindexing Coordinate.cospanEquivalence
      (eqToIso (pulledDiagram_eq Q))).functor.obj (ordinaryCone Q)).π.app j = _
    rw [coneEquivalence_forwardLeg]
    simp only [Iso.refl_hom]
    rcases j with ⟨⟨⟨a, b⟩⟩, hn⟩
    fin_cases a <;> fin_cases b
    all_goals
      first
      | exact (hn rfl).elim
      | (dsimp [CategoryTheory.Functor.comp,
          ordinaryCone, Coordinate.ordinaryCone, pulledSquare, WithInitial.mkCommaObject,
          Coordinate.cospanEquivalence, Coordinate.cospanToCanonical,
          Coordinate.squareToCanonical]
         erw [eqToHom_refl, Category.comp_id, Category.id_comp]
         exact congrArg Q.map (Subsingleton.elim _ _))
  apply cone_eq_of_iso_identity hi rfl
  dsimp [hi, Cone.ext]
  rfl

private theorem coneEquivalence_inverse_ordinaryCone
    (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    (coneEquivalence Q).inverse.obj (Coordinate.ordinaryCone (pulledSquare Q)) = ordinaryCone Q := by
  rw [← coneEquivalence_functor_ordinaryCone]
  have h : (coneEquivalence Q).functor ⋙ (coneEquivalence Q).inverse = 𝟭 _ :=
    coneEquivalence_unit Coordinate.cospanEquivalence (cospanInclusionFunctor ⋙ Q)
      (Coordinate.cospanInclusionFunctor ⋙ pulledSquare Q) (eqToIso (pulledDiagram_eq Q))
  exact congrArg (fun F => F.obj (ordinaryCone Q)) h

/-- The full canonical square cone simplex reads its actual original ordinary cone. -/
theorem nerveConeIso_hom_squareConeSimplex (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    (nerveConeIso Q).hom.app (op ⦋0⦌) (squareConeSimplex Q) =
      ComposableArrows.mk₀ (ordinaryCone Q) := by
  rw [nerveConeIso_hom_definition]
  change (nerveMap (coneEquivalence Q).inverse).app (op ⦋0⦌)
    ((Coordinate.nerveConeIso (pulledSquare Q)).hom.app (op ⦋0⦌)
      ((coordinateOverIso Q).hom.app (op ⦋0⦌) (squareConeSimplex Q))) = _
  rw [coordinateOverIso_hom_squareConeSimplex,
    Coordinate.nerveConeIso_hom_squareConeSimplex, nerveMap_app_mk₀,
    coneEquivalence_inverse_ordinaryCone]

/-- Reading the actual canonical whole square yields its actual ordinary cone at degree zero. -/
theorem coneChainOfSimplex_squareConeSimplex (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    coneChainOfSimplex Q (squareConeSimplex Q) = ComposableArrows.mk₀ (ordinaryCone Q) :=
  nerveConeIso_hom_squareConeSimplex Q

/-- The actual whole canonical cone point is preserved by the all-degree nerve isomorphism. -/
theorem squareConePoint_comp_nerveConeIso_hom (Q : DiamondObjects.{max uObj uHom} ⥤ C) :
    squareConePoint Q ≫ (nerveConeIso Q).hom = yonedaEquiv.symm (ComposableArrows.mk₀ (ordinaryCone Q)) := by
  rw [squareConePoint, yonedaEquiv_symm_comp, nerveConeIso_hom_squareConeSimplex]

end SSet.NativePullback
