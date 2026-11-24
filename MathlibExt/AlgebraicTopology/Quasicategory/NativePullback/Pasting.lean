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

public import MathlibExt.AlgebraicTopology.Quasicategory.NativePullback.Basic
public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinSlicePushout
public import MathlibExt.AlgebraicTopology.SimplicialSet.NervePreorderSubtype
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.CategoryTheory.LiftingProperties.Limits
import all MathlibExt.AlgebraicTopology.Quasicategory.NativePullback.Shapes
import Mathlib.Tactic.FinCases

/-!
# Native cone pasting through a pullback square

The original right square in a coherent two-square grid can be substituted
into its original cospan inside the complete cone index. The indexing
pushout retains every nerve word. Its native over-slice pullback therefore
transports every boundary lift of the original square comparison.

This is the concrete square-substitution step used in pullback pasting and
in reconstructing admissible span diagrams; see Haugseng, Hebestreit,
Linskens and Nuiten, *Two-variable fibrations, factorisation systems and
infinity-categories of spans*, Definition 2.1 and Lemmas 2.5 and 2.17.
-/

public section

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace SSet.NativePullback

/-- The actual six-object indexing grid, including its three 3-simplices. -/
abbrev PastingGridObjects := ULift.{u} (Fin 3 × Fin 2)

/-- Delete only the initial object of the original coherent grid. -/
abbrev PastingConeObjects :=
  {v : PastingGridObjects.{u} // v.down ≠ (0, 0)}

/-- The full cone index with the upper middle object removed. -/
abbrev PastingBaseObjects :=
  {v : PastingConeObjects.{u} // v.val.down ≠ (1, 0)}

/-- The original coherent grid carrier. -/
abbrev pastingGridShape : SSet.{u} := nerve PastingGridObjects.{u}

/-- The whole original five-object cone index. -/
abbrev pastingConeShape : SSet.{u} := nerve PastingConeObjects.{u}

/-- The whole original four-object index of a partial cone. -/
abbrev pastingBaseShape : SSet.{u} := nerve PastingBaseObjects.{u}

/-- The whole original cone index includes in the grid. -/
@[expose] def pastingConeInclusion : pastingConeShape.{u} ⟶ pastingGridShape.{u} :=
  nerveMap (preorderSubtypeInclusion (fun v : PastingGridObjects.{u} =>
    v.down ≠ (0, 0)))

/-- The original four-object index includes in the five-object cone index. -/
@[expose] def pastingBaseInclusion : pastingBaseShape.{u} ⟶ pastingConeShape.{u} :=
  nerveMap (preorderSubtypeInclusion (fun v : PastingConeObjects.{u} =>
    v.val.down ≠ (1, 0)))

private def coordinateRightSquareFunctor : Coordinate.DiamondObjects.{u} ⥤ PastingConeObjects.{u} :=
  (show Monotone (fun v : Coordinate.DiamondObjects.{u} =>
    (⟨⟨(v.down.1.succ, v.down.2)⟩, by simp⟩ : PastingConeObjects.{u})) from by
      intro a b h
      exact ⟨Fin.succ_le_succ_iff.mpr h.1, h.2⟩).functor

private def coordinateRightCospanFunctor : Coordinate.CospanObjects.{u} ⥤ PastingBaseObjects.{u} :=
  (show Monotone (fun v : Coordinate.CospanObjects.{u} =>
    (⟨coordinateRightSquareFunctor.obj v.val, by
      rcases v with ⟨⟨⟨a, b⟩⟩, hv⟩
      change (a.succ, b) ≠ (1, 0)
      fin_cases a <;> fin_cases b <;> first | decide | exact (hv rfl).elim⟩ :
        PastingBaseObjects.{u})) from by
      intro a b h
      exact ⟨Fin.succ_le_succ_iff.mpr h.1, h.2⟩).functor

/-- The canonical initial completion embeds as the original right square in columns one and two. -/
def pastingRightSquareFunctor : DiamondObjects.{u} ⥤ PastingConeObjects.{u} :=
  Coordinate.squareFromCanonical ⋙ coordinateRightSquareFunctor

/-- The entire right square retains both original triangles and their common diagonal. -/
def pastingRightSquare : squareShape.{u} ⟶ pastingConeShape.{u} :=
  nerveMapHomDown pastingRightSquareFunctor

/-- The canonical walking cospan includes in the original partial cone index. -/
def pastingRightCospanFunctor : CospanObjects.{u} ⥤ PastingBaseObjects.{u} :=
  Coordinate.cospanFromCanonical ⋙ coordinateRightCospanFunctor

/-- The whole canonical cospan keeps all original simplices in the partial cone index. -/
def pastingRightCospan : cospanShape.{u} ⟶ pastingBaseShape.{u} :=
  nerveMapHomDown pastingRightCospanFunctor

private theorem pastingRightSquare_eq_coordinate :
    pastingRightSquare.{u} =
      (Coordinate.squareIso.{u}).inv ≫ nerveMap coordinateRightSquareFunctor.{u} := by
  ext n s <;> rfl

private theorem pastingRightCospan_eq_coordinate :
    pastingRightCospan.{u} =
      (Coordinate.cospanIso.{u}).inv ≫ nerveMap coordinateRightCospanFunctor.{u} := by
  ext n s <;> rfl

private theorem coordinateRightCospan_comm :
    nerveMap coordinateRightCospanFunctor.{u} ≫ pastingBaseInclusion =
      Coordinate.cospanInclusion ≫ nerveMap coordinateRightSquareFunctor := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext i
  rfl

private theorem canonicalInclusion_fromCoordinate :
    Coordinate.cospanIso.inv.{u} ≫ Coordinate.cospanInclusion =
      cospanInclusion ≫ Coordinate.squareIso.inv := by
  have h := congrArg (fun f => Coordinate.cospanIso.inv ≫ f ≫ Coordinate.squareIso.inv)
    Coordinate.inclusion_squareIso
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.inv_hom_id_assoc] using h

/-- The indexing square keeps the same canonical cospan inside the same full cone. -/
theorem pastingRightCospan_comm :
    pastingRightCospan.{u} ≫ pastingBaseInclusion =
      cospanInclusion ≫ pastingRightSquare := by
  rw [pastingRightCospan_eq_coordinate, pastingRightSquare_eq_coordinate]
  rw [Category.assoc, coordinateRightCospan_comm, ← Category.assoc,
    canonicalInclusion_fromCoordinate, Category.assoc]

/-- The right-square chart reads every actual canonical object at the original grid vertex. -/
theorem pastingRightSquare_app_obj (n : SimplexCategoryᵒᵖ)
    (s : squareShape.{u}.obj n) (i : Fin (n.unop.len + 1)) :
    (((pastingRightSquare.app n) s).obj i).val.down =
      match s.obj i with
      | .star => (1, 0)
      | .of ⟨WalkingCospan.left⟩ => (2, 0)
      | .of ⟨WalkingCospan.right⟩ => (1, 1)
      | .of ⟨WalkingCospan.one⟩ => (2, 1) := by
  change (coordinateRightSquareFunctor.obj (Coordinate.squareFromCanonical.obj (s.obj i))).val.down = _
  cases s.obj i with
  | star => rfl
  | of v =>
    rcases v with ⟨v⟩
    cases v with
    | none => rfl
    | some v => cases v <;> rfl

/-- The full cone inclusion preserves every original scalar grid object. -/
theorem pastingConeInclusion_app_obj (n : SimplexCategoryᵒᵖ)
    (s : pastingConeShape.{u}.obj n) (i : Fin (n.unop.len + 1)) :
    ((pastingConeInclusion.app n) s).obj i = (s.obj i).val := rfl

/-- The partial cone inclusion preserves every original scalar cone object. -/
theorem pastingBaseInclusion_app_obj (n : SimplexCategoryᵒᵖ)
    (s : pastingBaseShape.{u}.obj n) (i : Fin (n.unop.len + 1)) :
    ((pastingBaseInclusion.app n) s).obj i = (s.obj i).val := rfl

private def baseP (v : PastingConeObjects.{u}) : Prop := v.val.down ≠ (1, 0)

private def rightP (v : PastingConeObjects.{u}) : Prop := 1 ≤ v.val.down.1

private def baseSupport : pastingConeShape.{u}.Subcomplex :=
  preorderSubtypeSubcomplex baseP

private def rightSupport : pastingConeShape.{u}.Subcomplex :=
  preorderSubtypeSubcomplex rightP

private theorem rightSquare_base_iff (v : Coordinate.DiamondObjects.{u}) :
    baseP (coordinateRightSquareFunctor.obj v) ↔ v.down ≠ (0, 0) := by
  rcases v with ⟨⟨a, b⟩⟩
  change (a.succ, b) ≠ (1, 0) ↔ (a, b) ≠ (0, 0)
  fin_cases a <;> fin_cases b <;> decide

private def rightOrderIso :
    Coordinate.DiamondObjects.{u} ≃o {v : PastingConeObjects.{u} // rightP v} where
  toFun v := ⟨coordinateRightSquareFunctor.obj v, by
    change 1 ≤ v.down.1.succ
    exact Fin.succ_pos _⟩
  invFun v := ⟨(⟨v.val.val.down.1.val - 1, by
    have ha := v.val.val.down.1.isLt
    have hp := v.property
    change 1 ≤ v.val.val.down.1.val at hp
    omega⟩, v.val.val.down.2)⟩
  left_inv v := by
    apply ULift.ext
    apply Prod.ext
    · apply Fin.ext
      change (v.down.1.val + 1) - 1 = v.down.1.val
      exact Nat.add_sub_cancel _ _
    · rfl
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    apply ULift.ext
    apply Prod.ext
    · apply Fin.ext
      have hp := v.property
      change 1 ≤ v.val.val.down.1.val at hp
      change v.val.val.down.1.val - 1 + 1 = v.val.val.down.1.val
      omega
    · rfl
  map_rel_iff' := by
    intro a b
    change (a.down.1.succ ≤ b.down.1.succ ∧ a.down.2 ≤ b.down.2) ↔
      (a.down.1 ≤ b.down.1 ∧ a.down.2 ≤ b.down.2)
    simp only [Fin.succ_le_succ_iff]

private def rightCospanOrderIso :
    Coordinate.CospanObjects.{u} ≃o {v : PastingConeObjects.{u} // baseP v ∧ rightP v} where
  toFun v := ⟨coordinateRightSquareFunctor.obj v.val,
    ⟨(rightSquare_base_iff v.val).mpr v.property, (rightOrderIso v.val).property⟩⟩
  invFun v := ⟨rightOrderIso.symm ⟨v.val, v.property.2⟩, by
    apply (rightSquare_base_iff _).mp
    have h : coordinateRightSquareFunctor.obj
        (rightOrderIso.symm ⟨v.val, v.property.2⟩) = v.val :=
      congrArg Subtype.val (rightOrderIso.apply_symm_apply ⟨v.val, v.property.2⟩)
    rw [h]
    exact v.property.1⟩
  left_inv v := by
    apply Subtype.ext
    exact rightOrderIso.symm_apply_apply v.val
  right_inv v := by
    apply Subtype.ext
    change coordinateRightSquareFunctor.obj
      (rightOrderIso.symm ⟨v.val, v.property.2⟩) = v.val
    exact congrArg Subtype.val (rightOrderIso.apply_symm_apply ⟨v.val, v.property.2⟩)
  map_rel_iff' := by
    intro a b
    change (a.val.down.1.succ ≤ b.val.down.1.succ ∧
      a.val.down.2 ≤ b.val.down.2) ↔
      (a.val.down.1 ≤ b.val.down.1 ∧ a.val.down.2 ≤ b.val.down.2)
    simp only [Fin.succ_le_succ_iff]

private def orderNerveIso {A B : Type u} [Preorder A] [Preorder B]
    (e : A ≃o B) : nerve A ≅ nerve B :=
  nerveFunctor.mapIso (Cat.isoOfEquiv (C := Cat.of A) (D := Cat.of B)
    e.equivalence e.symm_apply_apply e.apply_symm_apply)

private def baseIso : pastingBaseShape.{u} ≅ (baseSupport : SSet.{u}) :=
  nervePreorderSubtypeIso baseP

private def coordinateRightIso : Coordinate.squareShape.{u} ≅ (rightSupport : SSet.{u}) :=
  orderNerveIso rightOrderIso ≪≫ nervePreorderSubtypeIso rightP

private theorem support_inf :
    preorderSubtypeSubcomplex (fun v : PastingConeObjects.{u} => baseP v ∧ rightP v) =
      baseSupport ⊓ rightSupport := by
  ext n s
  change (∀ i, baseP (s.obj i) ∧ rightP (s.obj i)) ↔
    ((∀ i, baseP (s.obj i)) ∧ ∀ i, rightP (s.obj i))
  exact forall_and

private def coordinateRightCospanIso : Coordinate.cospanShape.{u} ≅
    ((baseSupport ⊓ rightSupport : pastingConeShape.{u}.Subcomplex) : SSet.{u}) :=
  orderNerveIso rightCospanOrderIso ≪≫
    nervePreorderSubtypeIso (fun v => baseP v ∧ rightP v) ≪≫
    Subcomplex.eqToIso support_inf

private theorem support_cover : baseSupport.{u} ⊔ rightSupport = ⊤ := by
  refine le_antisymm le_top ?_
  intro n s _
  by_cases hb : ∀ i, baseP (s.obj i)
  · exact Or.inl hb
  · right
    obtain ⟨t, ht⟩ := not_forall.mp hb
    have ht : (s.obj t).val.down = (1, 0) := not_not.mp ht
    intro i
    change 1 ≤ (s.obj i).val.down.1
    rcases le_total i t with hit | hti
    · have h := leOfHom (s.map (homOfLE hit))
      change ((s.obj i).val.down.1 ≤ (s.obj t).val.down.1 ∧
        (s.obj i).val.down.2 ≤ (s.obj t).val.down.2) at h
      rw [ht] at h
      by_contra! hn
      have ha : (s.obj i).val.down.1 = 0 := by
        apply Fin.ext
        change (s.obj i).val.down.1.val = 0
        change (s.obj i).val.down.1.val < 1 at hn
        omega
      have hb : (s.obj i).val.down.2 = 0 := le_antisymm h.2 (Fin.zero_le _)
      exact (s.obj i).property (Prod.ext ha hb)
    · have h := leOfHom (s.map (homOfLE hti))
      change ((s.obj t).val.down.1 ≤ (s.obj i).val.down.1 ∧
        (s.obj t).val.down.2 ≤ (s.obj i).val.down.2) at h
      rw [ht] at h
      exact h.1

private theorem baseIso_inclusion :
    baseIso.{u}.hom ≫ baseSupport.ι = pastingBaseInclusion := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext i
  rfl

private theorem coordinateRightIso_inclusion :
    coordinateRightIso.{u}.hom ≫ rightSupport.ι = nerveMap coordinateRightSquareFunctor := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext i
  rfl

private theorem coordinateRightCospanIso_inclusion :
    coordinateRightCospanIso.{u}.hom ≫ (baseSupport ⊓ rightSupport).ι =
      Coordinate.cospanInclusion ≫ nerveMap coordinateRightSquareFunctor := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext i
  rfl

private def rightIso : squareShape.{u} ≅ (rightSupport : SSet.{u}) :=
  Coordinate.squareIso.symm ≪≫ coordinateRightIso

private def rightCospanIso : cospanShape.{u} ≅
    ((baseSupport ⊓ rightSupport : pastingConeShape.{u}.Subcomplex) : SSet.{u}) :=
  Coordinate.cospanIso.symm ≪≫ coordinateRightCospanIso

private theorem rightIso_inclusion :
    rightIso.{u}.hom ≫ rightSupport.ι = pastingRightSquare := by
  change (Coordinate.squareIso.inv ≫ coordinateRightIso.hom) ≫ rightSupport.ι = _
  rw [Category.assoc, coordinateRightIso_inclusion, ← pastingRightSquare_eq_coordinate]

private theorem rightCospanIso_inclusion :
    rightCospanIso.{u}.hom ≫ (baseSupport ⊓ rightSupport).ι =
      cospanInclusion ≫ pastingRightSquare := by
  change (Coordinate.cospanIso.inv ≫ coordinateRightCospanIso.hom) ≫ (baseSupport ⊓ rightSupport).ι = _
  rw [Category.assoc, coordinateRightCospanIso_inclusion, ← Category.assoc,
    canonicalInclusion_fromCoordinate, Category.assoc, ← pastingRightSquare_eq_coordinate]

/-- The whole original cone index is the nerve pushout of its partial index
and its original right square along that square's complete cospan. -/
theorem pastingConeShape_isPushout :
    IsPushout pastingRightCospan.{u} cospanInclusion
      pastingBaseInclusion pastingRightSquare := by
  have h := Subcomplex.BicartSq.isPushout
    (show Subcomplex.BicartSq (baseSupport ⊓ rightSupport)
      baseSupport rightSupport (⊤ : pastingConeShape.{u}.Subcomplex) from
        { sup_eq := support_cover, inf_eq := rfl })
  apply h.of_iso' rightCospanIso baseIso rightIso
    (Subcomplex.topIso pastingConeShape).symm
  · apply (cancel_mono baseSupport.ι).mp
    rw [Category.assoc, Subcomplex.homOfLE_ι, rightCospanIso_inclusion,
      Category.assoc, baseIso_inclusion, pastingRightCospan_comm]
  · apply (cancel_mono rightSupport.ι).mp
    rw [Category.assoc, Subcomplex.homOfLE_ι, rightCospanIso_inclusion,
      Category.assoc, rightIso_inclusion]
  · apply (cancel_mono (Subcomplex.topIso pastingConeShape).hom).mp
    simp only [Category.assoc, Iso.symm_hom, Subcomplex.topIso_hom,
      Subcomplex.homOfLE_ι, Subcomplex.topIso_inv_ι, Category.comp_id,
      baseIso_inclusion]
  · apply (cancel_mono (Subcomplex.topIso pastingConeShape).hom).mp
    simp only [Category.assoc, Iso.symm_hom, Subcomplex.topIso_hom,
      Subcomplex.homOfLE_ι, Subcomplex.topIso_inv_ι, Category.comp_id,
      rightIso_inclusion]

/-- The literal original restriction from a full cone to its partial cone. -/
abbrev pastingComparison {X : SSet.{u}} (q : pastingConeShape.{u} ⟶ X) :
    sliceOver X q ⟶ sliceOver X (pastingBaseInclusion ≫ q) :=
  sliceOver.restrict X q pastingBaseInclusion

/-- The entire original joined map is restricted only on its indexing factor. -/
theorem pastingComparison_app_val {X : SSet.{u}} (q : pastingConeShape.{u} ⟶ X)
    (n : SimplexCategoryᵒᵖ) (s : (sliceOver X q).obj n) :
    ((pastingComparison q).app n s).val =
      (join.obj (stdSimplex.obj n.unop)).map pastingBaseInclusion ≫ s.val := rfl

/-- The actual square of full cone carriers is the pullback of the original
right-square-to-cospan comparison, with its fixed diagram transported exactly. -/
theorem pastingComparison_isPullback {X : SSet.{u}} (q : pastingConeShape.{u} ⟶ X) :
    IsPullback (pastingComparison q) (sliceOver.restrict X q pastingRightSquare)
      (sliceOver.restrict X (pastingBaseInclusion ≫ q) pastingRightCospan)
      (sliceOver.commSqRightRestriction pastingConeShape_isPushout.toCommSq q) :=
  sliceOver.isPullback_restrict_of_isPushout pastingConeShape_isPushout q

/-- A native pullback right square supplies every boundary lift of the
original full-cone restriction. The result retains arbitrary higher simplices
and requires no quasicategory or preselected cone lift as additional input. -/
theorem hasLiftingProperty_pastingComparison_of_isPullbackSquare
    {X : SSet.{u}} (q : pastingConeShape.{u} ⟶ X)
    (hq : IsPullbackSquare (pastingRightSquare ≫ q)) (m : ℕ) :
    HasLiftingProperty (boundary.{u} m).ι (pastingComparison q) := by
  let : HasLiftingProperty (boundary.{u} m).ι
      (sliceOver.restrict X (pastingRightSquare ≫ q) cospanInclusion) := hq m
  have hs : HasLiftingProperty (boundary.{u} m).ι
      (sliceOver.commSqRightRestriction pastingConeShape_isPushout.toCommSq q) := by
    unfold sliceOver.commSqRightRestriction
    infer_instance
  exact (pastingComparison_isPullback q).flip.hasLiftingProperty _

/-- The original cone pasting comparison lifts the whole boundary family. -/
theorem pastingComparison_I_rlp_of_isPullbackSquare
    {X : SSet.{u}} (q : pastingConeShape.{u} ⟶ X)
    (hq : IsPullbackSquare (pastingRightSquare ≫ q)) :
    modelCategoryQuillen.I.rlp (pastingComparison q) := by
  intro A B i hi
  obtain ⟨m⟩ := hi
  exact hasLiftingProperty_pastingComparison_of_isPullbackSquare q hq m

/-- The same cone pasting theorem applies to the entire original coherent
grid, including its three nondegenerate 3-simplices. -/
theorem pastingGridComparison_I_rlp_of_isPullbackSquare
    {X : SSet.{u}} (q : pastingGridShape.{u} ⟶ X)
    (hq : IsPullbackSquare (pastingRightSquare ≫ pastingConeInclusion ≫ q)) :
    modelCategoryQuillen.I.rlp (pastingComparison (pastingConeInclusion ≫ q)) :=
  pastingComparison_I_rlp_of_isPullbackSquare _ hq

end SSet.NativePullback
