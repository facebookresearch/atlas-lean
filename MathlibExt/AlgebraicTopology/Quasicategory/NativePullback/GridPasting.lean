/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Quasicategory.NativePullback.Pasting
import MathlibExt.AlgebraicTopology.Quasicategory.NativePullback.JoinShape
import MathlibExt.AlgebraicTopology.Quasicategory.NativePullback.Cone
import MathlibExt.AlgebraicTopology.Quasicategory.NativePullback.Symmetry
import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.CategoricalTerminalTransport
import MathlibExt.AlgebraicTopology.SimplicialSet.DirectedSliceComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.IteratedJoinSlice

/-!
# Original coherent grid pullback pasting

The three square restrictions retain the complete original grid. Concrete
index attachments compare the native cone spaces, and the original whole
cone point supplies the pullback pasting and cancellation laws.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace SSet.NativePullback

private def nativeSquareOfCone {C : Type u} [Category.{u} C]
    {A B T : C} {f : A ⟶ T} {g : B ⟶ T} (c : PullbackCone f g) :
    DiamondObjects.{u} ⥤ C :=
  WithInitial.lift (ULift.downFunctor ⋙ cospan f g)
    (fun v => c.π.app v.down) (fun _ _ h => c.w h)

/-- The original left square uses its actual00,10,01,11 native cone. -/
def gridLeftFunctor : DiamondObjects.{u} ⥤ PastingGridObjects.{u} :=
  nativeSquareOfCone (PullbackCone.mk
    (homOfLE (show (⟨(0, 0)⟩ : PastingGridObjects.{u}) ≤ ⟨(1, 0)⟩ from ⟨by decide, le_rfl⟩))
    (homOfLE (show (⟨(0, 0)⟩ : PastingGridObjects.{u}) ≤ ⟨(0, 1)⟩ from ⟨le_rfl, by decide⟩))
    (f := homOfLE (show (⟨(1, 0)⟩ : PastingGridObjects.{u}) ≤ ⟨(1, 1)⟩ from ⟨le_rfl, by decide⟩))
    (g := homOfLE (show (⟨(0, 1)⟩ : PastingGridObjects.{u}) ≤ ⟨(1, 1)⟩ from ⟨by decide, le_rfl⟩))
    (Subsingleton.elim _ _))

/-- The original outer square uses its actual00,20,01,21 native cone. -/
def gridOuterFunctor : DiamondObjects.{u} ⥤ PastingGridObjects.{u} :=
  nativeSquareOfCone (PullbackCone.mk
    (homOfLE (show (⟨(0, 0)⟩ : PastingGridObjects.{u}) ≤ ⟨(2, 0)⟩ from ⟨by decide, le_rfl⟩))
    (homOfLE (show (⟨(0, 0)⟩ : PastingGridObjects.{u}) ≤ ⟨(0, 1)⟩ from ⟨le_rfl, by decide⟩))
    (f := homOfLE (show (⟨(2, 0)⟩ : PastingGridObjects.{u}) ≤ ⟨(2, 1)⟩ from ⟨le_rfl, by decide⟩))
    (g := homOfLE (show (⟨(0, 1)⟩ : PastingGridObjects.{u}) ≤ ⟨(2, 1)⟩ from ⟨by decide, le_rfl⟩))
    (Subsingleton.elim _ _))

/-- The native left-square functor reads the four original grid vertices. -/
theorem gridLeftFunctor_obj (v : DiamondObjects.{u}) :
    gridLeftFunctor.obj v =
      match v with
      | .star => ⟨(0, 0)⟩
      | .of ⟨WalkingCospan.left⟩ => ⟨(1, 0)⟩
      | .of ⟨WalkingCospan.right⟩ => ⟨(0, 1)⟩
      | .of ⟨WalkingCospan.one⟩ => ⟨(1, 1)⟩ := by
  cases v with
  | star => rfl
  | of v =>
    rcases v with ⟨v⟩
    cases v with
    | none => rfl
    | some v => cases v <;> rfl

/-- The native outer-square functor reads the four original grid vertices. -/
theorem gridOuterFunctor_obj (v : DiamondObjects.{u}) :
    gridOuterFunctor.obj v =
      match v with
      | .star => ⟨(0, 0)⟩
      | .of ⟨WalkingCospan.left⟩ => ⟨(2, 0)⟩
      | .of ⟨WalkingCospan.right⟩ => ⟨(0, 1)⟩
      | .of ⟨WalkingCospan.one⟩ => ⟨(2, 1)⟩ := by
  cases v with
  | star => rfl
  | of v =>
    rcases v with ⟨v⟩
    cases v with
    | none => rfl
    | some v => cases v <;> rfl

/-- The complete original left-square chart retains both triangles and the common diagonal. -/
def gridLeftSquare : squareShape.{u} ⟶ pastingGridShape.{u} :=
  nerveMapHomDown.{u, 0, u} gridLeftFunctor

/-- The complete original outer-square chart retains both triangles and the common diagonal. -/
def gridOuterSquare : squareShape.{u} ⟶ pastingGridShape.{u} :=
  nerveMapHomDown.{u, 0, u} gridOuterFunctor

/-- The original left cospan keeps its actual10,01,11 cone-subtype objects. -/
def gridLeftCospanFunctor : CospanObjects.{u} ⥤ PastingConeObjects.{u} :=
  ULift.downFunctor ⋙ cospan
    (homOfLE (show (⟨⟨(1, 0)⟩, by decide⟩ : PastingConeObjects.{u}) ≤
      ⟨⟨(1, 1)⟩, by decide⟩ from ⟨le_rfl, by decide⟩))
    (homOfLE (show (⟨⟨(0, 1)⟩, by decide⟩ : PastingConeObjects.{u}) ≤
      ⟨⟨(1, 1)⟩, by decide⟩ from ⟨by decide, le_rfl⟩))

/-- The original outer cospan keeps its actual20,01,21 base-subtype objects. -/
def gridOuterCospanFunctor : CospanObjects.{u} ⥤ PastingBaseObjects.{u} :=
  ULift.downFunctor ⋙ cospan
    (homOfLE (show (⟨⟨⟨(2, 0)⟩, by decide⟩, by decide⟩ : PastingBaseObjects.{u}) ≤
      ⟨⟨⟨(2, 1)⟩, by decide⟩, by decide⟩ from ⟨le_rfl, by decide⟩))
    (homOfLE (show (⟨⟨⟨(0, 1)⟩, by decide⟩, by decide⟩ : PastingBaseObjects.{u}) ≤
      ⟨⟨⟨(2, 1)⟩, by decide⟩, by decide⟩ from ⟨by decide, le_rfl⟩))

/-- The complete original left-cospan inclusion in the full cone index. -/
def gridLeftCospan : cospanShape.{u} ⟶ pastingConeShape.{u} :=
  nerveMapHomDown.{u, 0, u} gridLeftCospanFunctor

/-- The complete original outer-cospan inclusion in the partial cone index. -/
def gridOuterCospan : cospanShape.{u} ⟶ pastingBaseShape.{u} :=
  nerveMapHomDown.{u, 0, u} gridOuterCospanFunctor

/-- The original left square and cospan have the same literal grid inclusion. -/
theorem gridLeftCospan_comp :
    gridLeftCospan.{u} ≫ pastingConeInclusion = cospanInclusion ≫ gridLeftSquare := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext i
  change (gridLeftCospanFunctor.obj (s.obj i)).val =
    gridLeftFunctor.obj (WithInitial.of (s.obj i))
  rcases s.obj i with ⟨v⟩
  cases v with
  | none => rfl
  | some v => cases v <;> rfl

/-- The original outer square and cospan have the same literal grid inclusion. -/
theorem gridOuterCospan_comp :
    gridOuterCospan.{u} ≫ pastingBaseInclusion ≫ pastingConeInclusion =
      cospanInclusion ≫ gridOuterSquare := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext i
  change (gridOuterCospanFunctor.obj (s.obj i)).val.val =
    gridOuterFunctor.obj (WithInitial.of (s.obj i))
  rcases s.obj i with ⟨v⟩
  cases v with
  | none => rfl
  | some v => cases v <;> rfl

/-!
## The original outer-cospan attachment
-/

private theorem supportedInf {A : Type u} [Preorder A] (P Q : A → Prop) :
    preorderSubtypeSubcomplex (fun a => P a ∧ Q a) =
      preorderSubtypeSubcomplex P ⊓ preorderSubtypeSubcomplex Q := by
  ext n x
  exact forall_and

private def supportSimplexIso {A : Type u} [Preorder A] {n : ℕ}
    (P : A → Prop) (e : Fin (n + 1) ≃o {a : A // P a}) :
    (Δ[n] : SSet.{u}) ≅ (preorderSubtypeSubcomplex P : SSet.{u}) :=
  stdSimplex.isoOfRepresentableBy (nerve.representableBy _ e.symm) ≪≫
    nervePreorderSubtypeIso P

private def orderNerveIso {A B : Type u} [Preorder A] [Preorder B]
    (e : A ≃o B) : nerve A ≅ nerve B :=
  nerveFunctor.mapIso (Cat.isoOfEquiv (C := Cat.of A) (D := Cat.of B)
    e.equivalence e.symm_apply_apply e.apply_symm_apply)

private theorem supportedCover {A : Type u} [Preorder A] (P Q : A → Prop)
    (h : ∀ a b, ¬ P a → (b ≤ a ∨ a ≤ b) → Q b) :
    preorderSubtypeSubcomplex P ⊔ preorderSubtypeSubcomplex Q = ⊤ := by
  classical
  refine le_antisymm le_top ?_
  intro n x _
  by_cases hx : ∀ i, P (x.obj i)
  · exact Or.inl hx
  · right
    obtain ⟨t, ht⟩ := not_forall.mp hx
    intro i
    apply h (x.obj t) (x.obj i) ht
    rcases le_total i t with hit | hti
    · exact Or.inl (leOfHom (x.map (homOfLE hit)))
    · exact Or.inr (leOfHom (x.map (homOfLE hti)))

private def outerP (v : PastingBaseObjects.{u}) : Prop := v.val.val.down ≠ (1, 1)
private def bottomP (v : PastingBaseObjects.{u}) : Prop := v.val.val.down.2 = 1
private def outerSupport : pastingBaseShape.{u}.Subcomplex := preorderSubtypeSubcomplex outerP
private def bottomSupport : pastingBaseShape.{u}.Subcomplex := preorderSubtypeSubcomplex bottomP

/-- The whole original lower-row triangle01→11→21. -/
def gridBottomTriangle : (Δ[2] : SSet.{u}) ⟶ pastingBaseShape.{u} :=
  yonedaEquiv.symm (ComposableArrows.mk₂
    (homOfLE (show (⟨⟨⟨(0, 1)⟩, by decide⟩, by decide⟩ : PastingBaseObjects.{u}) ≤
      ⟨⟨⟨(1, 1)⟩, by decide⟩, by decide⟩ from ⟨by decide, le_rfl⟩))
    (homOfLE (show (⟨⟨⟨(1, 1)⟩, by decide⟩, by decide⟩ : PastingBaseObjects.{u}) ≤
      ⟨⟨⟨(2, 1)⟩, by decide⟩, by decide⟩ from ⟨by decide, le_rfl⟩)))

private def bottomOrderIso : Fin 3 ≃o {v : PastingBaseObjects.{u} // bottomP v} where
  toFun i := ⟨⟨⟨⟨(i, 1)⟩, by
    intro h
    exact (by decide : (1 : Fin 2) ≠ 0) (congrArg Prod.snd h)⟩, by
      intro h
      exact (by decide : (1 : Fin 2) ≠ 0) (congrArg Prod.snd h)⟩, rfl⟩
  invFun v := v.val.val.val.down.1
  left_inv _ := rfl
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply ULift.ext
    exact Prod.ext rfl v.property.symm
  map_rel_iff' := by
    intro i j
    change (i ≤ j ∧ (1 : Fin 2) ≤ 1) ↔ i ≤ j
    simp only [le_refl, and_true]

private def outerInverseObject (v : {v : PastingBaseObjects.{u} // outerP v}) : CospanObjects.{u} :=
  if v.val.val.val.down.1 = 0 then ⟨WalkingCospan.right⟩
  else if v.val.val.val.down.2 = 0 then ⟨WalkingCospan.left⟩ else ⟨WalkingCospan.one⟩

private theorem outerForward_mem (v : CospanObjects.{u}) :
    outerP (gridOuterCospanFunctor.obj v) := by
  rcases v with ⟨v⟩
  cases v with
  | none => dsimp [outerP]; decide
  | some v => cases v <;> dsimp [outerP] <;> decide

private def outerForward : CospanObjects.{u} ⥤ {v : PastingBaseObjects.{u} // outerP v} where
  obj v := ⟨gridOuterCospanFunctor.obj v, outerForward_mem v⟩
  map f := homOfLE (leOfHom (gridOuterCospanFunctor.map f))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

private theorem outerInverseHom_nonempty
    (v w : {v : PastingBaseObjects.{u} // outerP v}) (h : v ≤ w) :
    Nonempty (outerInverseObject v ⟶ outerInverseObject w) := by
  rcases v with ⟨v, hv⟩
  rcases v with ⟨v, hvb⟩
  rcases v with ⟨v, hv0⟩
  rcases v with ⟨⟨a, b⟩⟩
  rcases w with ⟨w, hw⟩
  rcases w with ⟨w, hwb⟩
  rcases w with ⟨w, hw0⟩
  rcases w with ⟨⟨c, d⟩⟩
  change a.val ≤ c.val ∧ b.val ≤ d.val at h
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  all_goals dsimp [outerInverseObject] at *
  all_goals
    first
    | exact (hv0 rfl).elim
    | exact (hvb rfl).elim
    | exact (hv rfl).elim
    | exact (hw0 rfl).elim
    | exact (hwb rfl).elim
    | exact (hw rfl).elim
    | (exfalso; omega)
    | exact ⟨WalkingCospan.Hom.inl⟩
    | exact ⟨WalkingCospan.Hom.inr⟩
    | exact ⟨𝟙 _⟩

private def outerInverse : {v : PastingBaseObjects.{u} // outerP v} ⥤ CospanObjects.{u} where
  obj := outerInverseObject
  map f := Classical.choice (outerInverseHom_nonempty _ _ (leOfHom f))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

private theorem outerInverse_forward (v : CospanObjects.{u}) :
    outerInverse.obj (outerForward.obj v) = v := by
  rcases v with ⟨v⟩
  cases v with
  | none => rfl
  | some v => cases v <;> rfl

private theorem outerForward_inverse (v : {v : PastingBaseObjects.{u} // outerP v}) :
    outerForward.obj (outerInverse.obj v) = v := by
  rcases v with ⟨v, hv⟩
  rcases v with ⟨v, hvb⟩
  rcases v with ⟨v, hv0⟩
  rcases v with ⟨⟨a, b⟩⟩
  fin_cases a <;> fin_cases b
  all_goals
    first
    | exact (hv0 rfl).elim
    | exact (hvb rfl).elim
    | exact (hv rfl).elim
    | rfl

private def outerEquivalence :
    CospanObjects.{u} ≌ {v : PastingBaseObjects.{u} // outerP v} where
  functor := outerForward
  inverse := outerInverse
  unitIso := NatIso.ofComponents (fun v => eqToIso (outerInverse_forward v).symm)
    (by intros; exact Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents (fun v => eqToIso (outerForward_inverse v))
    (by intros; exact Subsingleton.elim _ _)

private def outerNerveIso :
    nerve CospanObjects.{u} ≅ nerve {v : PastingBaseObjects.{u} // outerP v} where
  hom := nerveMapHomDown.{u, 0, u} outerEquivalence.functor
  inv := nerveMapHomDown.{u, u, 0} outerEquivalence.inverse
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    apply nerve.ext_of_isThin
    funext i
    exact outerInverse_forward (x.obj i)
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    apply nerve.ext_of_isThin
    funext i
    exact outerForward_inverse (x.obj i)

private def outerBottomOrderIso :
    Fin 2 ≃o {v : PastingBaseObjects.{u} // outerP v ∧ bottomP v} where
  toFun i := ⟨⟨⟨⟨(⟨2 * i.val, by have h := i.isLt; omega⟩, 1)⟩, by
    intro h
    exact (by decide : (1 : Fin 2) ≠ 0) (congrArg Prod.snd h)⟩, by
      intro h
      exact (by decide : (1 : Fin 2) ≠ 0) (congrArg Prod.snd h)⟩,
    ⟨by
      intro h
      have hc := congrArg (fun p : Fin 3 × Fin 2 => p.1.val) h
      change 2 * i.val = 1 at hc
      omega, rfl⟩⟩
  invFun v := ⟨v.val.val.val.down.1.val / 2, by
    have h := v.val.val.val.down.1.isLt
    omega⟩
  left_inv i := by
    apply Fin.ext
    change 2 * i.val / 2 = i.val
    omega
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply ULift.ext
    apply Prod.ext
    · apply Fin.ext
      change 2 * (v.val.val.val.down.1.val / 2) = v.val.val.val.down.1.val
      have hl := v.val.val.val.down.1.isLt
      have hn : v.val.val.val.down.1.val ≠ 1 := by
        intro h
        exact v.property.1 (Prod.ext (Fin.ext h) v.property.2)
      omega
    · exact v.property.2.symm
  map_rel_iff' := by
    intro i j
    change (2 * i.val ≤ 2 * j.val ∧ (1 : ℕ) ≤ 1) ↔ i.val ≤ j.val
    omega

private def bottomIso : (Δ[2] : SSet.{u}) ≅ (bottomSupport : SSet.{u}) :=
  supportSimplexIso bottomP bottomOrderIso
private def outerIso : cospanShape.{u} ≅ (outerSupport : SSet.{u}) :=
  outerNerveIso ≪≫ nervePreorderSubtypeIso outerP
private def outerBottomIso : (Δ[1] : SSet.{u}) ≅
    ((outerSupport ⊓ bottomSupport : pastingBaseShape.{u}.Subcomplex) : SSet.{u}) :=
  supportSimplexIso (fun v => outerP v ∧ bottomP v) outerBottomOrderIso ≪≫
    Subcomplex.eqToIso (supportedInf outerP bottomP)

private theorem outerCover : outerSupport.{u} ⊔ bottomSupport = ⊤ := by
  apply supportedCover outerP bottomP
  intro a b ha hb
  have ha : a.val.val.down = (1, 1) := not_not.mp ha
  change b.val.val.down.2 = (1 : Fin 2)
  rcases hb with hba | hab
  · by_contra hrow
    have h0 : b.val.val.down.2 = (0 : Fin 2) := by
      apply Fin.ext
      have hl := b.val.val.down.2.isLt
      have hn : b.val.val.down.2.val ≠ 1 := fun h => hrow (Fin.ext h)
      change b.val.val.down.2.val = 0
      omega
    have hc : b.val.val.down.1 ≤ (1 : Fin 3) := by
      have h := hba.1
      change b.val.val.down.1 ≤ a.val.val.down.1 at h
      rw [ha] at h
      exact h
    have h₀ : b.val.val.down.1.val ≠ 0 := fun h => b.val.property (Prod.ext (Fin.ext h) h0)
    have h₁ : b.val.val.down.1.val ≠ 1 := fun h => b.property (Prod.ext (Fin.ext h) h0)
    change b.val.val.down.1.val ≤ 1 at hc
    omega
  · have h := hab.2
    change a.val.val.down.2 ≤ b.val.val.down.2 at h
    rw [ha] at h
    exact le_antisymm (Fin.le_last _) h

private theorem outerIso_inclusion : outerIso.{u}.hom ≫ outerSupport.ι = gridOuterCospan := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext i
  rfl

private theorem bottomIso_inclusion : bottomIso.{u}.hom ≫ bottomSupport.ι = gridBottomTriangle := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

private theorem outerBottomIso_inclusion :
    outerBottomIso.{u}.hom ≫ (outerSupport ⊓ bottomSupport).ι =
      cospanLeftChart ≫ gridOuterCospan := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

/-- The original lower-row triangle has the original outer long edge01→21. -/
theorem gridBottomTriangle_long : stdSimplex.δ (1 : Fin 3) ≫ gridBottomTriangle.{u} =
    cospanLeftChart ≫ gridOuterCospan := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

/-- The original partial cone is obtained by attaching its full lower-row
triangle to the outer cospan along the original long edge. -/
theorem gridOuterAttachment_isPushout :
    IsPushout cospanLeftChart.{u} (stdSimplex.δ (1 : Fin 3))
      gridOuterCospan gridBottomTriangle := by
  have h := Subcomplex.BicartSq.isPushout
    (show Subcomplex.BicartSq (outerSupport ⊓ bottomSupport)
      outerSupport bottomSupport (⊤ : pastingBaseShape.{u}.Subcomplex) from
        { sup_eq := outerCover, inf_eq := rfl })
  apply h.of_iso' outerBottomIso outerIso bottomIso (Subcomplex.topIso pastingBaseShape).symm
  · apply (cancel_mono outerSupport.ι).mp
    simp only [Category.assoc, Subcomplex.homOfLE_ι, outerBottomIso_inclusion,
      outerIso_inclusion]
  · apply (cancel_mono bottomSupport.ι).mp
    simp only [Category.assoc, Subcomplex.homOfLE_ι, outerBottomIso_inclusion,
      bottomIso_inclusion, gridBottomTriangle_long]
  · apply (cancel_mono (Subcomplex.topIso pastingBaseShape).hom).mp
    simp only [Category.assoc, Iso.symm_hom, Subcomplex.topIso_hom,
      Subcomplex.homOfLE_ι, Subcomplex.topIso_inv_ι, Category.comp_id,
      outerIso_inclusion]
  · apply (cancel_mono (Subcomplex.topIso pastingBaseShape).hom).mp
    simp only [Category.assoc, Iso.symm_hom, Subcomplex.topIso_hom,
      Subcomplex.homOfLE_ι, Subcomplex.topIso_inv_ι, Category.comp_id,
      bottomIso_inclusion]

/-- The computed outer attachment gives every boundary lift for the original
partial-cone restriction onto the original outer cospan. -/
theorem gridBaseOuterRestriction_I_rlp {X : SSet.{u}} [Quasicategory X]
    (q : pastingBaseShape.{u} ⟶ X) :
    modelCategoryQuillen.I.rlp (sliceOver.restrict X q gridOuterCospan) := by
  have hp := sliceOver.isPullback_restrict_of_isPushout gridOuterAttachment_isPushout q
  have ht : modelCategoryQuillen.I.rlp
      (sliceOver.restrict X (gridBottomTriangle ≫ q) (stdSimplex.δ (1 : Fin 3))) :=
    sliceOver.rlp_I_restrict_of_leftAnodyne X (stdSimplex.δ (1 : Fin 3))
      (leftHorn_llp_triangleFace 1 (by decide)) (gridBottomTriangle ≫ q)
  have hc : modelCategoryQuillen.I.rlp
      (sliceOver.commSqRightRestriction gridOuterAttachment_isPushout.toCommSq q) := by
    dsimp only [sliceOver.commSqRightRestriction]
    exact modelCategoryQuillen.I.rlp.comp_mem _ _ ht
      (modelCategoryQuillen.I.rlp.of_isIso _)
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hp.flip hc

/-- The actual right-square pullback supplies every boundary lift from the
entire original cone index to its original outer cospan. -/
theorem gridConeOuterRestriction_I_rlp {X : SSet.{u}} [Quasicategory X]
    (q : pastingConeShape.{u} ⟶ X)
    (hq : IsPullbackSquare (pastingRightSquare ≫ q)) :
    modelCategoryQuillen.I.rlp
      (sliceOver.restrict X q (gridOuterCospan ≫ pastingBaseInclusion)) := by
  rw [sliceOver.restrict_comp]
  exact modelCategoryQuillen.I.rlp.comp_mem _ _
    (pastingComparison_I_rlp_of_isPullbackSquare q hq)
    (gridBaseOuterRestriction_I_rlp (pastingBaseInclusion ≫ q))

/-!
## The exact incomplete left attachment
-/

private def leftP (v : PastingConeObjects.{u}) : Prop := v.val.down.1.val ≤ 1
private def lowerP (v : PastingConeObjects.{u}) : Prop := v.val.down.2 = 1
private def leftSupport : pastingConeShape.{u}.Subcomplex := preorderSubtypeSubcomplex leftP
private def lowerSupport : pastingConeShape.{u}.Subcomplex := preorderSubtypeSubcomplex lowerP

/-- The exact intermediate index is the union of the original left cospan
and the lower triangle. Its missing long edge10→21 is not inserted yet. -/
abbrev gridLeftStage : pastingConeShape.{u}.Subcomplex := leftSupport ⊔ lowerSupport

private def leftInverseObject (v : {v : PastingConeObjects.{u} // leftP v}) : CospanObjects.{u} :=
  if v.val.val.down.1 = 0 then ⟨WalkingCospan.right⟩
  else if v.val.val.down.2 = 0 then ⟨WalkingCospan.left⟩ else ⟨WalkingCospan.one⟩

private theorem leftForward_mem (v : CospanObjects.{u}) :
    leftP (gridLeftCospanFunctor.obj v) := by
  rcases v with ⟨v⟩
  cases v with
  | none => dsimp [leftP]; decide
  | some v => cases v <;> dsimp [leftP] <;> decide

private def leftForward : CospanObjects.{u} ⥤ {v : PastingConeObjects.{u} // leftP v} where
  obj v := ⟨gridLeftCospanFunctor.obj v, leftForward_mem v⟩
  map f := homOfLE (leOfHom (gridLeftCospanFunctor.map f))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

private theorem leftInverseHom_nonempty
    (v w : {v : PastingConeObjects.{u} // leftP v}) (h : v ≤ w) :
    Nonempty (leftInverseObject v ⟶ leftInverseObject w) := by
  rcases v with ⟨v, hv⟩
  rcases v with ⟨v, hv0⟩
  rcases v with ⟨⟨a, b⟩⟩
  rcases w with ⟨w, hw⟩
  rcases w with ⟨w, hw0⟩
  rcases w with ⟨⟨c, d⟩⟩
  change a.val ≤ c.val ∧ b.val ≤ d.val at h
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  all_goals dsimp [leftInverseObject, leftP] at *
  all_goals
    first
    | exact (hv0 rfl).elim
    | exact (hw0 rfl).elim
    | (exfalso; omega)
    | exact ⟨WalkingCospan.Hom.inl⟩
    | exact ⟨WalkingCospan.Hom.inr⟩
    | exact ⟨𝟙 _⟩

private def leftInverse : {v : PastingConeObjects.{u} // leftP v} ⥤ CospanObjects.{u} where
  obj := leftInverseObject
  map f := Classical.choice (leftInverseHom_nonempty _ _ (leOfHom f))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

private theorem leftInverse_forward (v : CospanObjects.{u}) :
    leftInverse.obj (leftForward.obj v) = v := by
  rcases v with ⟨v⟩
  cases v with
  | none => rfl
  | some v => cases v <;> rfl

private theorem leftForward_inverse (v : {v : PastingConeObjects.{u} // leftP v}) :
    leftForward.obj (leftInverse.obj v) = v := by
  rcases v with ⟨v, hv⟩
  rcases v with ⟨v, hv0⟩
  rcases v with ⟨⟨a, b⟩⟩
  fin_cases a <;> fin_cases b
  all_goals
    first
    | exact (hv0 rfl).elim
    | (exfalso; dsimp [leftP] at hv; omega)
    | rfl

private def leftEquivalence :
    CospanObjects.{u} ≌ {v : PastingConeObjects.{u} // leftP v} where
  functor := leftForward
  inverse := leftInverse
  unitIso := NatIso.ofComponents (fun v => eqToIso (leftInverse_forward v).symm)
    (by intros; exact Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents (fun v => eqToIso (leftForward_inverse v))
    (by intros; exact Subsingleton.elim _ _)

private def leftNerveIso :
    nerve CospanObjects.{u} ≅ nerve {v : PastingConeObjects.{u} // leftP v} where
  hom := nerveMapHomDown.{u, 0, u} leftEquivalence.functor
  inv := nerveMapHomDown.{u, u, 0} leftEquivalence.inverse
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    apply nerve.ext_of_isThin
    funext i
    exact leftInverse_forward (x.obj i)
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    apply nerve.ext_of_isThin
    funext i
    exact leftForward_inverse (x.obj i)

private def lowerOrderIso : Fin 3 ≃o {v : PastingConeObjects.{u} // lowerP v} where
  toFun i := ⟨⟨⟨(i, 1)⟩, by
    intro h
    exact (by decide : (1 : Fin 2) ≠ 0) (congrArg Prod.snd h)⟩, rfl⟩
  invFun v := v.val.val.down.1
  left_inv _ := rfl
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    apply ULift.ext
    exact Prod.ext rfl v.property.symm
  map_rel_iff' := by
    intro i j
    change (i ≤ j ∧ (1 : Fin 2) ≤ 1) ↔ i ≤ j
    simp only [le_refl, and_true]

private def leftLowerOrderIso :
    Fin 2 ≃o {v : PastingConeObjects.{u} // leftP v ∧ lowerP v} where
  toFun i := ⟨⟨⟨(i.castSucc, 1)⟩, by
    intro h
    exact (by decide : (1 : Fin 2) ≠ 0) (congrArg Prod.snd h)⟩,
    ⟨by change i.val ≤ 1; have h := i.isLt; omega, rfl⟩⟩
  invFun v := ⟨v.val.val.down.1.val, by
    have h := v.property.1
    change v.val.val.down.1.val ≤ 1 at h
    omega⟩
  left_inv _ := rfl
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    apply ULift.ext
    apply Prod.ext
    · apply Fin.ext
      rfl
    · exact v.property.2.symm
  map_rel_iff' := by
    intro i j
    change (i.val ≤ j.val ∧ (1 : Fin 2) ≤ 1) ↔ i.val ≤ j.val
    simp only [le_refl, and_true]

private def leftIso : cospanShape.{u} ≅ (leftSupport : SSet.{u}) :=
  leftNerveIso ≪≫ nervePreorderSubtypeIso leftP
private def lowerIso : (Δ[2] : SSet.{u}) ≅ (lowerSupport : SSet.{u}) :=
  supportSimplexIso lowerP lowerOrderIso
private def leftLowerIso : (Δ[1] : SSet.{u}) ≅
    ((leftSupport ⊓ lowerSupport : pastingConeShape.{u}.Subcomplex) : SSet.{u}) :=
  supportSimplexIso (fun v => leftP v ∧ lowerP v) leftLowerOrderIso ≪≫
    Subcomplex.eqToIso (supportedInf leftP lowerP)

private theorem leftIso_inclusion : leftIso.{u}.hom ≫ leftSupport.ι = gridLeftCospan := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext i
  rfl
private theorem lowerIso_inclusion :
    lowerIso.{u}.hom ≫ lowerSupport.ι = gridBottomTriangle ≫ pastingBaseInclusion := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl
private theorem leftLowerIso_inclusion :
    leftLowerIso.{u}.hom ≫ (leftSupport ⊓ lowerSupport).ι =
      cospanLeftChart ≫ gridLeftCospan := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

/-- The full lower triangle starts on the original edge01→11. -/
theorem gridBottomTriangle_initial :
    stdSimplex.δ (2 : Fin 3) ≫ gridBottomTriangle.{u} ≫ pastingBaseInclusion =
      cospanLeftChart ≫ gridLeftCospan := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

private theorem leftSupport_le_stage : leftSupport.{u} ≤ gridLeftStage := le_sup_left
private theorem lowerSupport_le_stage : lowerSupport.{u} ≤ gridLeftStage := le_sup_right

/-- The original left cospan includes into the exact incomplete stage. -/
def gridLeftStageInl : cospanShape.{u} ⟶ (gridLeftStage : SSet.{u}) :=
  leftIso.hom ≫ Subcomplex.homOfLE leftSupport_le_stage
/-- The original lower triangle includes into the same exact stage. -/
def gridLeftStageInr : (Δ[2] : SSet.{u}) ⟶ (gridLeftStage : SSet.{u}) :=
  lowerIso.hom ≫ Subcomplex.homOfLE lowerSupport_le_stage

/-- The stage's full original left cospan reads back to the same cone index. -/
theorem gridLeftStageInl_ι : gridLeftStageInl.{u} ≫ gridLeftStage.ι = gridLeftCospan := by
  dsimp only [gridLeftStageInl]
  rw [Category.assoc, Subcomplex.homOfLE_ι, leftIso_inclusion]
/-- The stage's full original lower triangle reads back to the same cone index. -/
theorem gridLeftStageInr_ι : gridLeftStageInr.{u} ≫ gridLeftStage.ι =
    gridBottomTriangle ≫ pastingBaseInclusion := by
  dsimp only [gridLeftStageInr]
  rw [Category.assoc, Subcomplex.homOfLE_ι, lowerIso_inclusion]

/-- The first left-stage attachment is the actual initial-edge pushout. -/
theorem gridLeftInitialAttachment_isPushout :
    IsPushout cospanLeftChart.{u} (stdSimplex.δ (2 : Fin 3))
      gridLeftStageInl gridLeftStageInr := by
  have h := Subcomplex.BicartSq.isPushout
    (show Subcomplex.BicartSq (leftSupport ⊓ lowerSupport) leftSupport lowerSupport
      gridLeftStage.{u} from { sup_eq := rfl, inf_eq := rfl })
  apply h.of_iso' leftLowerIso leftIso lowerIso (Iso.refl _)
  · apply (cancel_mono leftSupport.ι).mp
    simp only [Category.assoc, Subcomplex.homOfLE_ι, leftLowerIso_inclusion, leftIso_inclusion]
  · apply (cancel_mono lowerSupport.ι).mp
    simp only [Category.assoc, Subcomplex.homOfLE_ι, leftLowerIso_inclusion,
      lowerIso_inclusion, gridBottomTriangle_initial]
  · rfl
  · rfl

private theorem restriction_I_rlp_of_isPushout {X A B C D : SSet.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {inl : B ⟶ D} {inr : C ⟶ D}
    (h : IsPushout f g inl inr) (q : D ⟶ X)
    (hg : modelCategoryQuillen.I.rlp (sliceOver.restrict X (inr ≫ q) g)) :
    modelCategoryQuillen.I.rlp (sliceOver.restrict X q inl) := by
  have hc : modelCategoryQuillen.I.rlp (sliceOver.commSqRightRestriction h.toCommSq q) := by
    dsimp only [sliceOver.commSqRightRestriction]
    exact modelCategoryQuillen.I.rlp.comp_mem _ _ hg (modelCategoryQuillen.I.rlp.of_isIso _)
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (sliceOver.isPullback_restrict_of_isPushout h q).flip hc

/-- The actual first left-stage restriction lifts every whole boundary. -/
theorem gridLeftInitialRestriction_I_rlp {X : SSet.{u}} [Quasicategory X]
    (q : (gridLeftStage : SSet.{u}) ⟶ X) :
    modelCategoryQuillen.I.rlp (sliceOver.restrict X q gridLeftStageInl) :=
  restriction_I_rlp_of_isPushout gridLeftInitialAttachment_isPushout q
    (sliceOver.rlp_I_restrict_of_leftAnodyne X (stdSimplex.δ (2 : Fin 3))
      (leftHorn_llp_triangleFace 2 (by decide)) (gridLeftStageInr ≫ q))

/-!
## The actual inner-horn attachment
-/

private def middleP (v : PastingConeObjects.{u}) : Prop :=
  1 ≤ v.val.down.1.val ∧ v.val.down.1.val ≤ v.val.down.2.val + 1
private def filledP (v : PastingConeObjects.{u}) : Prop := v.val.down ≠ (2, 0)
private def middleSupport : pastingConeShape.{u}.Subcomplex := preorderSubtypeSubcomplex middleP
/-- The full four-object index after the original middle triangle has been attached. -/
abbrev gridLeftFilled : pastingConeShape.{u}.Subcomplex := preorderSubtypeSubcomplex filledP

private def middleVertices : Fin 3 → PastingConeObjects.{u} :=
  ![⟨⟨(1, 0)⟩, by decide⟩, ⟨⟨(1, 1)⟩, by decide⟩, ⟨⟨(2, 1)⟩, by decide⟩]

private def middleChain : ComposableArrows PastingConeObjects.{u} 2 :=
  ComposableArrows.mk₂
    (homOfLE (show (⟨⟨(1, 0)⟩, by decide⟩ : PastingConeObjects.{u}) ≤
      ⟨⟨(1, 1)⟩, by decide⟩ from ⟨le_rfl, by decide⟩))
    (homOfLE (show (⟨⟨(1, 1)⟩, by decide⟩ : PastingConeObjects.{u}) ≤
      ⟨⟨(2, 1)⟩, by decide⟩ from ⟨by decide, le_rfl⟩))

/-- The whole original middle triangle10→11→21. -/
def gridMiddleTriangle : (Δ[2] : SSet.{u}) ⟶ pastingConeShape.{u} :=
  yonedaEquiv.symm middleChain

private def middleOrderIso : Fin 3 ≃o {v : PastingConeObjects.{u} // middleP v} where
  toFun i := ⟨middleVertices i, by fin_cases i <;> dsimp [middleP, middleVertices] <;> decide⟩
  invFun v := ⟨v.val.val.down.1.val + v.val.val.down.2.val - 1, by
    have hc := v.val.val.down.1.isLt
    have hr := v.val.val.down.2.isLt
    omega⟩
  left_inv i := by fin_cases i <;> rfl
  right_inv v := by
    rcases v with ⟨⟨⟨⟨a, b⟩⟩, hC⟩, h⟩
    change 1 ≤ a.val ∧ a.val ≤ b.val + 1 at h
    fin_cases a <;> fin_cases b
    all_goals dsimp [middleVertices] at h ⊢
    all_goals omega
  map_rel_iff' := by
    intro i j
    change ((middleVertices i).val.down.1 ≤ (middleVertices j).val.down.1 ∧
      (middleVertices i).val.down.2 ≤ (middleVertices j).val.down.2) ↔ i ≤ j
    fin_cases i <;> fin_cases j <;> dsimp [middleVertices] <;> decide

private def middleIso : (Δ[2] : SSet.{u}) ≅ (middleSupport : SSet.{u}) :=
  supportSimplexIso middleP middleOrderIso
private theorem middleIso_inclusion :
    middleIso.{u}.hom ≫ middleSupport.ι = gridMiddleTriangle := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

private instance middleTriangle_mono : Mono gridMiddleTriangle.{u} := by
  rw [← middleIso_inclusion]
  infer_instance

private theorem middleTriangle_obj (n : SimplexCategoryᵒᵖ) (x : (Δ[2] : SSet.{u}).obj n)
    (i : Fin (n.unop.len + 1)) :
    ((gridMiddleTriangle.app n) x).obj i = middleVertices (stdSimplex.asOrderHom x i) := by
  rcases n with ⟨⟨d⟩⟩
  change middleChain.obj (stdSimplex.asOrderHom x i) = _
  generalize stdSimplex.asOrderHom x i = j
  fin_cases j <;> rfl

private theorem middleVertices_left (i : Fin 3) : leftP (middleVertices.{u} i) ↔ i ≠ 2 := by
  fin_cases i <;> dsimp [leftP, middleVertices] <;> decide
private theorem middleVertices_lower (i : Fin 3) : lowerP (middleVertices.{u} i) ↔ i ≠ 0 := by
  fin_cases i <;> dsimp [lowerP, middleVertices] <;> decide

private theorem horn_two_one_word (n : SimplexCategoryᵒᵖ) (x : (Δ[2] : SSet.{u}).obj n) :
    x ∈ (horn 2 (1 : Fin 3)).obj n ↔
      (∀ i, stdSimplex.asOrderHom x i ≠ 2) ∨ (∀ i, stdSimplex.asOrderHom x i ≠ 0) := by
  rw [mem_horn_iff]
  simp only [Ne, Set.eq_univ_iff_forall, not_forall, Set.mem_union, Set.mem_range,
    Set.mem_singleton_iff, not_or, not_exists]
  constructor
  · rintro ⟨j, hj, hn⟩
    fin_cases j
    · exact Or.inr hj
    · exact (hn rfl).elim
    · exact Or.inl hj
  · rintro (h | h)
    · exact ⟨2, h, by decide⟩
    · exact ⟨0, h, by decide⟩

private theorem middleTriangle_preimage :
    gridLeftStage.{u}.preimage gridMiddleTriangle = horn 2 (1 : Fin 3) := by
  ext n x
  rw [horn_two_one_word]
  change ((∀ i, leftP (((gridMiddleTriangle.app n) x).obj i)) ∨
    (∀ i, lowerP (((gridMiddleTriangle.app n) x).obj i))) ↔ _
  simp only [middleTriangle_obj, middleVertices_left, middleVertices_lower]

private theorem supportRelativeCover {A : Type u} [Preorder A] (P Q R : A → Prop)
    (hP : ∀ a, P a → R a) (hQ : ∀ a, Q a → R a)
    (h : ∀ a b, R a → R b → ¬ P a → (b ≤ a ∨ a ≤ b) → Q b) :
    preorderSubtypeSubcomplex P ⊔ preorderSubtypeSubcomplex Q = preorderSubtypeSubcomplex R := by
  classical
  refine le_antisymm ?_ ?_
  · intro n x hx i
    rcases hx with hx | hx
    · exact hP _ (hx i)
    · exact hQ _ (hx i)
  · intro n x hx
    by_cases hp : ∀ i, P (x.obj i)
    · exact Or.inl hp
    · right
      obtain ⟨t, ht⟩ := not_forall.mp hp
      intro i
      apply h (x.obj t) (x.obj i) (hx t) (hx i) ht
      rcases le_total i t with hit | hti
      · exact Or.inl (leOfHom (x.map (homOfLE hit)))
      · exact Or.inr (leOfHom (x.map (homOfLE hti)))

private theorem lowerMiddle_cover : lowerSupport.{u} ⊔ middleSupport = gridLeftFilled := by
  apply supportRelativeCover lowerP middleP filledP
  · intro a ha h
    have hb := congrArg Prod.snd h
    change a.val.down.2 = (0 : Fin 2) at hb
    exact (by decide : (1 : Fin 2) ≠ 0) (ha.symm.trans hb)
  · intro a ha h
    have hc := congrArg (fun p : Fin 3 × Fin 2 => p.1.val) h
    have hr := congrArg (fun p : Fin 3 × Fin 2 => p.2.val) h
    change a.val.down.1.val = 2 at hc
    change a.val.down.2.val = 0 at hr
    change 1 ≤ a.val.down.1.val ∧ a.val.down.1.val ≤ a.val.down.2.val + 1 at ha
    omega
  · rintro ⟨⟨a, b⟩, hA⟩ ⟨⟨c, d⟩, hB⟩ ha hb hn hc
    change (c.val ≤ a.val ∧ d.val ≤ b.val) ∨ (a.val ≤ c.val ∧ b.val ≤ d.val) at hc
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
    all_goals dsimp [filledP, lowerP, middleP] at hA hB ha hb hn hc ⊢
    all_goals
      first
      | exact (hA rfl).elim
      | exact (hB rfl).elim
      | exact (ha rfl).elim
      | exact (hb rfl).elim
      | omega

private theorem left_le_filled : leftSupport.{u} ≤ gridLeftFilled := by
  intro n x hx i h
  have hc := congrArg (fun p : Fin 3 × Fin 2 => p.1.val) h
  change (x.obj i).val.down.1.val = 2 at hc
  have hi := hx i
  change (x.obj i).val.down.1.val ≤ 1 at hi
  omega

private theorem leftStage_middle_cover : gridLeftStage.{u} ⊔ middleSupport = gridLeftFilled := by
  rw [sup_assoc, lowerMiddle_cover]
  exact sup_eq_right.mpr left_le_filled

private theorem middleRange : Subcomplex.range gridMiddleTriangle.{u} = middleSupport := by
  rw [← middleIso_inclusion, Subcomplex.range_comp]
  have hr : Subcomplex.range middleIso.{u}.hom = ⊤ :=
    (Subcomplex.range_eq_top_iff _).mpr inferInstance
  rw [hr, Subcomplex.image_top]
  exact Subfunctor.range_ι _

private theorem image_preimage_inf {A B : SSet.{u}} (S : B.Subcomplex) (p : A ⟶ B) :
    (S.preimage p).image p = S ⊓ Subcomplex.range p := by
  ext n y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, ⟨x, rfl⟩⟩
  · rintro ⟨hy, x, rfl⟩
    exact ⟨x, hy, rfl⟩

private theorem middleHorn_image :
    (horn 2 (1 : Fin 3)).image gridMiddleTriangle.{u} = gridLeftStage ⊓ middleSupport := by
  rw [← middleTriangle_preimage, image_preimage_inf, middleRange]

private instance middleHorn_toImage_isIso :
    IsIso ((horn 2 (1 : Fin 3)).toImage gridMiddleTriangle.{u}) := by
  have hm : Mono ((horn 2 (1 : Fin 3)).toImage gridMiddleTriangle.{u}) :=
    mono_of_mono_fac ((horn 2 (1 : Fin 3)).toImage_ι gridMiddleTriangle)
  exact isIso_of_mono_of_epi _

private def middleHornIso : (horn 2 (1 : Fin 3) : SSet.{u}) ≅
    ((gridLeftStage ⊓ middleSupport : pastingConeShape.{u}.Subcomplex) : SSet.{u}) :=
  asIso ((horn 2 (1 : Fin 3)).toImage gridMiddleTriangle) ≪≫
    Subcomplex.eqToIso middleHorn_image

private theorem middleHornIso_inclusion :
    middleHornIso.{u}.hom ≫ (gridLeftStage ⊓ middleSupport).ι =
      (horn 2 (1 : Fin 3)).ι ≫ gridMiddleTriangle := by
  rw [middleHornIso, Iso.trans_hom, Category.assoc,
    Subcomplex.eqToIso_hom, Subcomplex.homOfLE_ι]
  exact (horn 2 (1 : Fin 3)).toImage_ι gridMiddleTriangle

private theorem middleSupport_le_filled : middleSupport.{u} ≤ gridLeftFilled := by
  rw [← leftStage_middle_cover]
  exact le_sup_right

private theorem middleHorn_le_stage : gridLeftStage.{u} ⊓ middleSupport ≤ gridLeftStage := inf_le_left

/-- The actual incomplete stage includes into the full four-object index. -/
def gridLeftMiddleInl : (gridLeftStage : SSet.{u}) ⟶ (gridLeftFilled : SSet.{u}) :=
  Subcomplex.homOfLE (by rw [← leftStage_middle_cover]; exact le_sup_left)
/-- The whole original middle triangle includes into the same full index. -/
def gridLeftMiddleInr : (Δ[2] : SSet.{u}) ⟶ (gridLeftFilled : SSet.{u}) :=
  middleIso.hom ≫ Subcomplex.homOfLE middleSupport_le_filled
/-- The entire original horn is retained inside the incomplete stage. -/
def gridLeftMiddleHorn : (horn 2 (1 : Fin 3) : SSet.{u}) ⟶ (gridLeftStage : SSet.{u}) :=
  middleHornIso.hom ≫ Subcomplex.homOfLE middleHorn_le_stage

/-- The second attachment adds precisely the original middle triangle
along its whole original inner horn; it retains every higher degeneracy. -/
theorem gridLeftMiddleAttachment_isPushout :
    IsPushout gridLeftMiddleHorn.{u} (horn 2 (1 : Fin 3)).ι
      gridLeftMiddleInl gridLeftMiddleInr := by
  have h := Subcomplex.BicartSq.isPushout
    (show Subcomplex.BicartSq (gridLeftStage ⊓ middleSupport) gridLeftStage middleSupport
      gridLeftFilled.{u} from { sup_eq := leftStage_middle_cover, inf_eq := rfl })
  apply h.of_iso' middleHornIso (Iso.refl _) middleIso (Iso.refl _)
  · rfl
  · apply (cancel_mono middleSupport.ι).mp
    simp only [Category.assoc, Subcomplex.homOfLE_ι,
      middleHornIso_inclusion, middleIso_inclusion]
  · rfl
  · rfl

/-- The second, actual inner-horn attachment gives every native boundary lift. -/
theorem gridLeftMiddleRestriction_I_rlp {X : SSet.{u}} [Quasicategory X]
    (q : (gridLeftFilled : SSet.{u}) ⟶ X) :
    modelCategoryQuillen.I.rlp (sliceOver.restrict X q gridLeftMiddleInl) :=
  restriction_I_rlp_of_isPushout gridLeftMiddleAttachment_isPushout q
    (sliceOver.rlp_I_restrict_of_leftAnodyne X (horn 2 (1 : Fin 3)).ι (by
      intro A B p hp
      exact hp _ (horn_ι_mem_leftHornInclusions (by decide))) (gridLeftMiddleInr ≫ q))

/-!
## The original final diagonal attachment
-/

private def topP (v : PastingConeObjects.{u}) : Prop := v.val.down.2 = 0 ∨ v.val.down.1 = 2
private def topSupport : pastingConeShape.{u}.Subcomplex := preorderSubtypeSubcomplex topP
private def topVertices : Fin 3 → PastingConeObjects.{u} :=
  ![⟨⟨(1, 0)⟩, by decide⟩, ⟨⟨(2, 0)⟩, by decide⟩, ⟨⟨(2, 1)⟩, by decide⟩]

/-- The entire original top triangle10→20→21. -/
def gridTopTriangle : (Δ[2] : SSet.{u}) ⟶ pastingConeShape.{u} :=
  rightTriangle ≫ pastingRightSquare

private def topOrderIso : Fin 3 ≃o {v : PastingConeObjects.{u} // topP v} where
  toFun i := ⟨topVertices i, by fin_cases i <;> dsimp [topP, topVertices] <;> decide⟩
  invFun v := ⟨v.val.val.down.1.val + v.val.val.down.2.val - 1, by
    have hc := v.val.val.down.1.isLt
    have hr := v.val.val.down.2.isLt
    omega⟩
  left_inv i := by fin_cases i <;> rfl
  right_inv v := by
    rcases v with ⟨⟨⟨⟨a, b⟩⟩, hC⟩, h⟩
    fin_cases a <;> fin_cases b
    all_goals dsimp [topP, topVertices] at h ⊢
    all_goals
      first
      | exact (hC rfl).elim
      | simp at h
  map_rel_iff' := by
    intro i j
    change ((topVertices i).val.down.1 ≤ (topVertices j).val.down.1 ∧
      (topVertices i).val.down.2 ≤ (topVertices j).val.down.2) ↔ i ≤ j
    fin_cases i <;> fin_cases j <;> dsimp [topVertices] <;> decide

private def diagonalVertices : Fin 2 → PastingConeObjects.{u} :=
  ![⟨⟨(1, 0)⟩, by decide⟩, ⟨⟨(2, 1)⟩, by decide⟩]
private def finalDiagonalOrderIso :
    Fin 2 ≃o {v : PastingConeObjects.{u} // filledP v ∧ topP v} where
  toFun i := ⟨diagonalVertices i, by
    fin_cases i <;> dsimp [filledP, topP, diagonalVertices] <;> decide⟩
  invFun v := v.val.val.down.2
  left_inv i := by fin_cases i <;> rfl
  right_inv v := by
    rcases v with ⟨⟨⟨⟨a, b⟩⟩, hC⟩, h⟩
    fin_cases a <;> fin_cases b
    all_goals dsimp [filledP, topP, diagonalVertices] at h ⊢
    all_goals
      first
      | exact (hC rfl).elim
      | simp at h
  map_rel_iff' := by
    intro i j
    change ((diagonalVertices i).val.down.1 ≤ (diagonalVertices j).val.down.1 ∧
      (diagonalVertices i).val.down.2 ≤ (diagonalVertices j).val.down.2) ↔ i ≤ j
    fin_cases i <;> fin_cases j <;> dsimp [diagonalVertices] <;> decide

private def topIso : (Δ[2] : SSet.{u}) ≅ (topSupport : SSet.{u}) :=
  supportSimplexIso topP topOrderIso
private def finalDiagonalIso : (Δ[1] : SSet.{u}) ≅
    ((gridLeftFilled ⊓ topSupport : pastingConeShape.{u}.Subcomplex) : SSet.{u}) :=
  supportSimplexIso (fun v => filledP v ∧ topP v) finalDiagonalOrderIso ≪≫
    Subcomplex.eqToIso (supportedInf filledP topP)

private theorem filledTop_cover : gridLeftFilled.{u} ⊔ topSupport = ⊤ := by
  apply supportedCover filledP topP
  intro a b ha hb
  have ha : a.val.down = (2, 0) := not_not.mp ha
  rcases hb with hba | hab
  · left
    have h := hba.2
    change b.val.down.2 ≤ a.val.down.2 at h
    rw [ha] at h
    exact le_antisymm h (Fin.zero_le _)
  · right
    have h := hab.1
    change a.val.down.1 ≤ b.val.down.1 at h
    rw [ha] at h
    exact le_antisymm (Fin.le_last _) h

private theorem topIso_inclusion : topIso.{u}.hom ≫ topSupport.ι = gridTopTriangle := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl
private theorem finalDiagonalIso_inclusion :
    finalDiagonalIso.{u}.hom ≫ (gridLeftFilled ⊓ topSupport).ι =
      stdSimplex.δ (1 : Fin 3) ≫ gridTopTriangle := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

private theorem finalDiagonal_le_filled : gridLeftFilled.{u} ⊓ topSupport ≤ gridLeftFilled := inf_le_left

/-- The original diagonal10→21 includes into the actual filled left index. -/
def gridLeftFinalCommon : (Δ[1] : SSet.{u}) ⟶ (gridLeftFilled : SSet.{u}) :=
  finalDiagonalIso.hom ≫ Subcomplex.homOfLE finalDiagonal_le_filled

/-- Attaching the original top triangle along its original diagonal gives
the whole original five-object cone index, with every original nerve word. -/
theorem gridLeftFinalAttachment_isPushout :
    IsPushout gridLeftFinalCommon.{u} (stdSimplex.δ (1 : Fin 3))
      gridLeftFilled.ι gridTopTriangle := by
  have h := Subcomplex.BicartSq.isPushout
    (show Subcomplex.BicartSq (gridLeftFilled ⊓ topSupport) gridLeftFilled topSupport
      (⊤ : pastingConeShape.{u}.Subcomplex) from
        { sup_eq := filledTop_cover, inf_eq := rfl })
  apply h.of_iso' finalDiagonalIso (Iso.refl _) topIso (Subcomplex.topIso pastingConeShape).symm
  · rfl
  · apply (cancel_mono topSupport.ι).mp
    simp only [Category.assoc, Subcomplex.homOfLE_ι, finalDiagonalIso_inclusion, topIso_inclusion]
  · apply (cancel_mono (Subcomplex.topIso pastingConeShape).hom).mp
    simp only [Iso.refl_hom, Iso.symm_hom, Category.id_comp, Category.assoc,
      Subcomplex.topIso_hom, Subcomplex.homOfLE_ι, Subcomplex.topIso_inv_ι, Category.comp_id]
  · apply (cancel_mono (Subcomplex.topIso pastingConeShape).hom).mp
    simp only [Category.assoc, Iso.symm_hom, Subcomplex.topIso_hom,
      Subcomplex.homOfLE_ι, Subcomplex.topIso_inv_ι, Category.comp_id, topIso_inclusion]

/-- The last original diagonal attachment gives every native boundary lift. -/
theorem gridLeftFinalRestriction_I_rlp {X : SSet.{u}} [Quasicategory X]
    (q : pastingConeShape.{u} ⟶ X) :
    modelCategoryQuillen.I.rlp (sliceOver.restrict X q gridLeftFilled.ι) :=
  restriction_I_rlp_of_isPushout gridLeftFinalAttachment_isPushout q
    (sliceOver.rlp_I_restrict_of_leftAnodyne X (stdSimplex.δ (1 : Fin 3))
      (leftHorn_llp_triangleFace 1 (by decide)) (gridTopTriangle ≫ q))

/-- The middle-stage inclusion retains the same complete original index. -/
theorem gridLeftMiddleInl_ι : gridLeftMiddleInl.{u} ≫ gridLeftFilled.ι = gridLeftStage.ι := by
  rw [gridLeftMiddleInl, Subcomplex.homOfLE_ι]

/-- The three computed left attachments give all boundary lifts of the
literal original cone-to-left-cospan restriction. -/
theorem gridConeLeftRestriction_I_rlp {X : SSet.{u}} [Quasicategory X]
    (q : pastingConeShape.{u} ⟶ X) :
    modelCategoryQuillen.I.rlp (sliceOver.restrict X q gridLeftCospan) := by
  have h₂ : modelCategoryQuillen.I.rlp
      (sliceOver.restrict X q (gridLeftMiddleInl ≫ gridLeftFilled.ι)) := by
    rw [sliceOver.restrict_comp]
    exact modelCategoryQuillen.I.rlp.comp_mem _ _
      (gridLeftFinalRestriction_I_rlp q)
      (gridLeftMiddleRestriction_I_rlp (gridLeftFilled.ι ≫ q))
  have h₃ : modelCategoryQuillen.I.rlp
      (sliceOver.restrict X q (gridLeftStageInl ≫ (gridLeftMiddleInl ≫ gridLeftFilled.ι))) := by
    rw [sliceOver.restrict_comp]
    exact modelCategoryQuillen.I.rlp.comp_mem _ _ h₂
      (gridLeftInitialRestriction_I_rlp (gridLeftMiddleInl ≫ gridLeftFilled.ι ≫ q))
  have hi : gridLeftStageInl.{u} ≫ (gridLeftMiddleInl ≫ gridLeftFilled.ι) = gridLeftCospan := by
    rw [gridLeftMiddleInl_ι, gridLeftStageInl_ι]
  exact (congrArg (fun i : cospanShape.{u} ⟶ pastingConeShape.{u} =>
    modelCategoryQuillen.I.rlp (sliceOver.restrict X q i)) hi).mp h₃

/-!
## The native two-chart filled index and join-face readbacks
-/

private def lowerMiddleOrderIso :
    Fin 2 ≃o {v : PastingConeObjects.{u} // lowerP v ∧ middleP v} where
  toFun i := ⟨⟨⟨(i.succ, 1)⟩, by simp⟩, ⟨rfl, by
    change 1 ≤ i.val + 1 ∧ i.val + 1 ≤ 1 + 1
    have h := i.isLt
    omega⟩⟩
  invFun v := ⟨v.val.val.down.1.val - 1, by
    have hc := v.val.val.down.1.isLt
    have hp := v.property.2.1
    change 1 ≤ v.val.val.down.1.val at hp
    omega⟩
  left_inv i := by apply Fin.ext; change i.val + 1 - 1 = i.val; omega
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    apply ULift.ext
    apply Prod.ext
    · apply Fin.ext
      have h := v.property.2.1
      change 1 ≤ v.val.val.down.1.val at h
      change v.val.val.down.1.val - 1 + 1 = v.val.val.down.1.val
      omega
    · exact v.property.1.symm
  map_rel_iff' := by
    intro i j
    change (i.val + 1 ≤ j.val + 1 ∧ (1 : Fin 2) ≤ 1) ↔ i.val ≤ j.val
    omega

private def lowerMiddleIso : (Δ[1] : SSet.{u}) ≅
    ((lowerSupport ⊓ middleSupport : pastingConeShape.{u}.Subcomplex) : SSet.{u}) :=
  supportSimplexIso (fun v => lowerP v ∧ middleP v) lowerMiddleOrderIso ≪≫
    Subcomplex.eqToIso (supportedInf lowerP middleP)

private theorem lowerSupport_le_filled : lowerSupport.{u} ≤ gridLeftFilled := by
  rw [← lowerMiddle_cover]
  exact le_sup_left

/-- The original lower triangle includes into the actual filled index. -/
def gridLowerFilled : (Δ[2] : SSet.{u}) ⟶ (gridLeftFilled : SSet.{u}) :=
  lowerIso.hom ≫ Subcomplex.homOfLE lowerSupport_le_filled

private theorem gridLowerFilled_ι : gridLowerFilled.{u} ≫ gridLeftFilled.ι =
    gridBottomTriangle ≫ pastingBaseInclusion := by
  dsimp only [gridLowerFilled]
  rw [Category.assoc, Subcomplex.homOfLE_ι, lowerIso_inclusion]
private theorem gridMiddleFilled_ι : gridLeftMiddleInr.{u} ≫ gridLeftFilled.ι =
    gridMiddleTriangle := by
  dsimp only [gridLeftMiddleInr]
  rw [Category.assoc, Subcomplex.homOfLE_ι, middleIso_inclusion]
private theorem lowerMiddleIso_inclusion :
    lowerMiddleIso.{u}.hom ≫ (lowerSupport ⊓ middleSupport).ι =
      stdSimplex.δ (0 : Fin 3) ≫ gridMiddleTriangle := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl
private theorem lowerMiddle_common :
    stdSimplex.δ (0 : Fin 3) ≫ gridBottomTriangle.{u} ≫ pastingBaseInclusion =
      stdSimplex.δ (0 : Fin 3) ≫ gridMiddleTriangle := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

/-- The entire filled index is the pushout of its two original triangles
along their original common edge11→21. -/
theorem gridFilled_isPushout :
    IsPushout (stdSimplex.δ (0 : Fin 3)) (stdSimplex.δ (0 : Fin 3))
      gridLowerFilled.{u} gridLeftMiddleInr := by
  have h := Subcomplex.BicartSq.isPushout
    (show Subcomplex.BicartSq (lowerSupport ⊓ middleSupport) lowerSupport middleSupport
      gridLeftFilled.{u} from { sup_eq := lowerMiddle_cover, inf_eq := rfl })
  apply h.of_iso' lowerMiddleIso lowerIso middleIso (Iso.refl _)
  · apply (cancel_mono lowerSupport.ι).mp
    simp only [Category.assoc, Subcomplex.homOfLE_ι, lowerMiddleIso_inclusion,
      lowerIso_inclusion, lowerMiddle_common]
  · apply (cancel_mono middleSupport.ι).mp
    simp only [Category.assoc, Subcomplex.homOfLE_ι, lowerMiddleIso_inclusion, middleIso_inclusion]
  · rfl
  · rfl

private theorem joinZeroFace (i : Fin 3) :
    (join.obj (Δ[0] : SSet.{u})).map (stdSimplex.δ i) ≫ (joinStdSimplexIso 0 2).hom =
      (joinStdSimplexIso 0 1).hom ≫ stdSimplex.δ i.succ := by
  have hi : AugmentedSimplexCategory.tensorHomOf (𝟙 ⦋0⦌) (SimplexCategory.δ i) =
      SimplexCategory.δ i.succ := by
    rw [JoinHorn.Internal.joinHorn_tensorHomOf_id_δ]
    congr 1
    apply Fin.ext
    change 0 + 1 + i.val = i.val + 1
    omega
  have h := joinStdSimplexIso_natural_right.{u} (m := 0) (SimplexCategory.δ i)
  rw [hi] at h
  exact h

private theorem joinZeroFaceInv (i : Fin 3) :
    stdSimplex.δ i.succ ≫ (joinStdSimplexIso.{u} 0 2).inv =
      (joinStdSimplexIso 0 1).inv ≫ (join.obj (Δ[0] : SSet.{u})).map (stdSimplex.δ i) := by
  apply (cancel_mono (joinStdSimplexIso.{u} 0 2).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [joinZeroFace, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-!
## All three original three-simplex grid charts
-/

private def gLowerP (v : PastingGridObjects.{u}) : Prop := v.down.1 = 0 ∨ v.down.2 = 1
private def gMiddleP (v : PastingGridObjects.{u}) : Prop :=
  v.down.2.val ≤ v.down.1.val ∧ v.down.1.val ≤ v.down.2.val + 1
private def gTopP (v : PastingGridObjects.{u}) : Prop := v.down.2 = 0 ∨ v.down.1 = 2
private def gFilledP (v : PastingGridObjects.{u}) : Prop := v.down ≠ (2, 0)
private def gLowerSupport : pastingGridShape.{u}.Subcomplex := preorderSubtypeSubcomplex gLowerP
private def gMiddleSupport : pastingGridShape.{u}.Subcomplex := preorderSubtypeSubcomplex gMiddleP
private def gTopSupport : pastingGridShape.{u}.Subcomplex := preorderSubtypeSubcomplex gTopP
private abbrev gFilledSupport : pastingGridShape.{u}.Subcomplex := preorderSubtypeSubcomplex gFilledP

private def gLowerVertices : Fin 4 → PastingGridObjects.{u} :=
  ![⟨(0, 0)⟩, ⟨(0, 1)⟩, ⟨(1, 1)⟩, ⟨(2, 1)⟩]
private def gMiddleVertices : Fin 4 → PastingGridObjects.{u} :=
  ![⟨(0, 0)⟩, ⟨(1, 0)⟩, ⟨(1, 1)⟩, ⟨(2, 1)⟩]
private def gTopVertices : Fin 4 → PastingGridObjects.{u} :=
  ![⟨(0, 0)⟩, ⟨(1, 0)⟩, ⟨(2, 0)⟩, ⟨(2, 1)⟩]

private def gridChainOrderIso (P : PastingGridObjects.{u} → Prop)
    (v : Fin 4 → PastingGridObjects.{u}) (hv : ∀ i, P (v i))
    (hl : ∀ i, (v i).down.1.val + (v i).down.2.val = i.val)
    (hr : ∀ a (_ha : P a),
      v ⟨a.down.1.val + a.down.2.val, by
        have h₁ := a.down.1.isLt; have h₂ := a.down.2.isLt; omega⟩ = a)
    (hm : ∀ i j, v i ≤ v j ↔ i ≤ j) : Fin 4 ≃o {a : PastingGridObjects.{u} // P a} where
  toFun i := ⟨v i, hv i⟩
  invFun a := ⟨a.val.down.1.val + a.val.down.2.val, by
    have h₁ := a.val.down.1.isLt; have h₂ := a.val.down.2.isLt; omega⟩
  left_inv i := Fin.ext (hl i)
  right_inv a := Subtype.ext (hr a.val a.property)
  map_rel_iff' := by
    intro i j
    change v i ≤ v j ↔ i ≤ j
    exact hm i j

private def gLowerOrderIso : Fin 4 ≃o {v : PastingGridObjects.{u} // gLowerP v} :=
  gridChainOrderIso gLowerP gLowerVertices
    (by intro i; fin_cases i <;> dsimp [gLowerP, gLowerVertices] <;> decide)
    (by intro i; fin_cases i <;> rfl)
    (by
      rintro ⟨⟨a, b⟩⟩ h
      fin_cases a <;> fin_cases b
      all_goals dsimp [gLowerP, gLowerVertices] at h ⊢
      all_goals simp at h)
    (by
      intro i j
      change ((gLowerVertices i).down.1 ≤ (gLowerVertices j).down.1 ∧
        (gLowerVertices i).down.2 ≤ (gLowerVertices j).down.2) ↔ i ≤ j
      fin_cases i <;> fin_cases j <;> dsimp [gLowerVertices] <;> decide)
private def gMiddleOrderIso : Fin 4 ≃o {v : PastingGridObjects.{u} // gMiddleP v} :=
  gridChainOrderIso gMiddleP gMiddleVertices
    (by intro i; fin_cases i <;> dsimp [gMiddleP, gMiddleVertices] <;> decide)
    (by intro i; fin_cases i <;> rfl)
    (by
      rintro ⟨⟨a, b⟩⟩ h
      fin_cases a <;> fin_cases b
      all_goals dsimp [gMiddleP, gMiddleVertices] at h ⊢
      all_goals omega)
    (by
      intro i j
      change ((gMiddleVertices i).down.1 ≤ (gMiddleVertices j).down.1 ∧
        (gMiddleVertices i).down.2 ≤ (gMiddleVertices j).down.2) ↔ i ≤ j
      fin_cases i <;> fin_cases j <;> dsimp [gMiddleVertices] <;> decide)
private def gTopOrderIso : Fin 4 ≃o {v : PastingGridObjects.{u} // gTopP v} :=
  gridChainOrderIso gTopP gTopVertices
    (by intro i; fin_cases i <;> dsimp [gTopP, gTopVertices] <;> decide)
    (by intro i; fin_cases i <;> rfl)
    (by
      rintro ⟨⟨a, b⟩⟩ h
      fin_cases a <;> fin_cases b
      all_goals dsimp [gTopP, gTopVertices] at h ⊢
      all_goals simp at h)
    (by
      intro i j
      change ((gTopVertices i).down.1 ≤ (gTopVertices j).down.1 ∧
        (gTopVertices i).down.2 ≤ (gTopVertices j).down.2) ↔ i ≤ j
      fin_cases i <;> fin_cases j <;> dsimp [gTopVertices] <;> decide)

private def gLowerIso : (Δ[3] : SSet.{u}) ≅ (gLowerSupport : SSet.{u}) :=
  supportSimplexIso gLowerP gLowerOrderIso
private def gMiddleIso : (Δ[3] : SSet.{u}) ≅ (gMiddleSupport : SSet.{u}) :=
  supportSimplexIso gMiddleP gMiddleOrderIso
private def gTopIso : (Δ[3] : SSet.{u}) ≅ (gTopSupport : SSet.{u}) :=
  supportSimplexIso gTopP gTopOrderIso

/-- The complete original grid three-simplex00→01→11→21. -/
def gridLowerChart : (Δ[3] : SSet.{u}) ⟶ pastingGridShape.{u} := gLowerIso.hom ≫ gLowerSupport.ι
/-- The complete original grid three-simplex00→10→11→21. -/
def gridMiddleChart : (Δ[3] : SSet.{u}) ⟶ pastingGridShape.{u} := gMiddleIso.hom ≫ gMiddleSupport.ι
/-- The complete original grid three-simplex00→10→20→21. -/
def gridTopChart : (Δ[3] : SSet.{u}) ⟶ pastingGridShape.{u} := gTopIso.hom ≫ gTopSupport.ι

private theorem gLowerMiddle_cover : gLowerSupport.{u} ⊔ gMiddleSupport = gFilledSupport := by
  apply supportRelativeCover gLowerP gMiddleP gFilledP
  · intro a ha h
    have hc := congrArg Prod.fst h
    have hr := congrArg Prod.snd h
    rcases ha with ha | ha
    · exact (by decide : (0 : Fin 3) ≠ 2) (ha.symm.trans hc)
    · exact (by decide : (1 : Fin 2) ≠ 0) (ha.symm.trans hr)
  · intro a ha h
    have hc := congrArg (fun p : Fin 3 × Fin 2 => p.1.val) h
    have hr := congrArg (fun p : Fin 3 × Fin 2 => p.2.val) h
    change a.down.1.val = 2 at hc
    change a.down.2.val = 0 at hr
    change a.down.2.val ≤ a.down.1.val ∧ a.down.1.val ≤ a.down.2.val + 1 at ha
    omega
  · rintro ⟨⟨a, b⟩⟩ ⟨⟨c, d⟩⟩ ha hb hn hc
    change (c.val ≤ a.val ∧ d.val ≤ b.val) ∨ (a.val ≤ c.val ∧ b.val ≤ d.val) at hc
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
    all_goals dsimp [gFilledP, gLowerP, gMiddleP] at ha hb hn hc ⊢
    all_goals
      first
      | exact (ha rfl).elim
      | exact (hb rfl).elim
      | omega

private theorem gFilledTop_cover : gFilledSupport.{u} ⊔ gTopSupport = ⊤ := by
  apply supportedCover gFilledP gTopP
  intro a b ha hb
  have ha : a.down = (2, 0) := not_not.mp ha
  rcases hb with hb | hb
  · left
    have h := hb.2
    change b.down.2 ≤ a.down.2 at h
    rw [ha] at h
    exact le_antisymm h (Fin.zero_le _)
  · right
    have h := hb.1
    change a.down.1 ≤ b.down.1 at h
    rw [ha] at h
    exact le_antisymm (Fin.le_last _) h

private def gridThreeOrderIso (P : PastingGridObjects.{u} → Prop)
    (v : Fin 3 → PastingGridObjects.{u}) (hv : ∀ i, P (v i))
    (hl : ∀ i, (v i).down.1 = i)
    (hr : ∀ a (_ha : P a), v a.down.1 = a)
    (hm : ∀ i j, v i ≤ v j ↔ i ≤ j) : Fin 3 ≃o {a : PastingGridObjects.{u} // P a} where
  toFun i := ⟨v i, hv i⟩
  invFun a := a.val.down.1
  left_inv := hl
  right_inv a := Subtype.ext (hr a.val a.property)
  map_rel_iff' := by intro i j; change v i ≤ v j ↔ i ≤ j; exact hm i j

private def gSideVertices : Fin 3 → PastingGridObjects.{u} := ![⟨(0, 0)⟩, ⟨(1, 1)⟩, ⟨(2, 1)⟩]
private def gDiagonalVertices : Fin 3 → PastingGridObjects.{u} := ![⟨(0, 0)⟩, ⟨(1, 0)⟩, ⟨(2, 1)⟩]
private def gSideOrderIso :
    Fin 3 ≃o {v : PastingGridObjects.{u} // gLowerP v ∧ gMiddleP v} :=
  gridThreeOrderIso (fun v => gLowerP v ∧ gMiddleP v) gSideVertices
    (by intro i; fin_cases i <;> dsimp [gLowerP, gMiddleP, gSideVertices] <;> decide)
    (by intro i; fin_cases i <;> rfl)
    (by
      rintro ⟨⟨a, b⟩⟩ h
      fin_cases a <;> fin_cases b
      all_goals dsimp [gLowerP, gMiddleP, gSideVertices] at h ⊢
      all_goals simp at h)
    (by
      intro i j
      change ((gSideVertices i).down.1 ≤ (gSideVertices j).down.1 ∧
        (gSideVertices i).down.2 ≤ (gSideVertices j).down.2) ↔ i ≤ j
      fin_cases i <;> fin_cases j <;> dsimp [gSideVertices] <;> decide)
private def gDiagonalOrderIso :
    Fin 3 ≃o {v : PastingGridObjects.{u} // gFilledP v ∧ gTopP v} :=
  gridThreeOrderIso (fun v => gFilledP v ∧ gTopP v) gDiagonalVertices
    (by intro i; fin_cases i <;> dsimp [gFilledP, gTopP, gDiagonalVertices] <;> decide)
    (by intro i; fin_cases i <;> rfl)
    (by
      rintro ⟨⟨a, b⟩⟩ h
      fin_cases a <;> fin_cases b
      all_goals dsimp [gFilledP, gTopP, gDiagonalVertices] at h ⊢
      all_goals simp at h)
    (by
      intro i j
      change ((gDiagonalVertices i).down.1 ≤ (gDiagonalVertices j).down.1 ∧
        (gDiagonalVertices i).down.2 ≤ (gDiagonalVertices j).down.2) ↔ i ≤ j
      fin_cases i <;> fin_cases j <;> dsimp [gDiagonalVertices] <;> decide)

private def gSideIso : (Δ[2] : SSet.{u}) ≅
    ((gLowerSupport ⊓ gMiddleSupport : pastingGridShape.{u}.Subcomplex) : SSet.{u}) :=
  supportSimplexIso (fun v => gLowerP v ∧ gMiddleP v) gSideOrderIso ≪≫
    Subcomplex.eqToIso (supportedInf gLowerP gMiddleP)
private def gDiagonalIso : (Δ[2] : SSet.{u}) ≅
    ((gFilledSupport ⊓ gTopSupport : pastingGridShape.{u}.Subcomplex) : SSet.{u}) :=
  supportSimplexIso (fun v => gFilledP v ∧ gTopP v) gDiagonalOrderIso ≪≫
    Subcomplex.eqToIso (supportedInf gFilledP gTopP)

private def gLowerFilled : (Δ[3] : SSet.{u}) ⟶ (gFilledSupport : SSet.{u}) :=
  gLowerIso.hom ≫ Subcomplex.homOfLE (by rw [← gLowerMiddle_cover]; exact le_sup_left)
private def gMiddleFilled : (Δ[3] : SSet.{u}) ⟶ (gFilledSupport : SSet.{u}) :=
  gMiddleIso.hom ≫ Subcomplex.homOfLE (by rw [← gLowerMiddle_cover]; exact le_sup_right)

private theorem gLowerFilled_ι : gLowerFilled.{u} ≫ gFilledSupport.ι = gridLowerChart := by
  rw [gLowerFilled, Category.assoc, Subcomplex.homOfLE_ι]
  rfl
private theorem gMiddleFilled_ι : gMiddleFilled.{u} ≫ gFilledSupport.ι = gridMiddleChart := by
  rw [gMiddleFilled, Category.assoc, Subcomplex.homOfLE_ι]
  rfl
private theorem gSideIso_inclusion :
    gSideIso.{u}.hom ≫ (gLowerSupport ⊓ gMiddleSupport).ι =
      stdSimplex.δ (1 : Fin 4) ≫ gridMiddleChart := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl
private theorem gSide_common :
    stdSimplex.δ (1 : Fin 4) ≫ gridLowerChart.{u} =
      stdSimplex.δ (1 : Fin 4) ≫ gridMiddleChart := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl
private theorem gDiagonalIso_inclusion :
    gDiagonalIso.{u}.hom ≫ (gFilledSupport ⊓ gTopSupport).ι =
      stdSimplex.δ (2 : Fin 4) ≫ gridMiddleChart := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl
private theorem gDiagonal_common :
    stdSimplex.δ (2 : Fin 4) ≫ gridTopChart.{u} =
      stdSimplex.δ (2 : Fin 4) ≫ gridMiddleChart := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

private theorem gFilled_isPushout :
    IsPushout (stdSimplex.δ (1 : Fin 4)) (stdSimplex.δ (1 : Fin 4))
      gLowerFilled.{u} gMiddleFilled := by
  have h := Subcomplex.BicartSq.isPushout
    (show Subcomplex.BicartSq (gLowerSupport ⊓ gMiddleSupport) gLowerSupport gMiddleSupport
      gFilledSupport.{u} from { sup_eq := gLowerMiddle_cover, inf_eq := rfl })
  apply h.of_iso' gSideIso gLowerIso gMiddleIso (Iso.refl _)
  · apply (cancel_mono gLowerSupport.ι).mp
    simp only [Category.assoc, Subcomplex.homOfLE_ι, gSideIso_inclusion]
    change stdSimplex.δ (1 : Fin 4) ≫ gridMiddleChart =
      stdSimplex.δ (1 : Fin 4) ≫ gridLowerChart
    exact gSide_common.symm
  · apply (cancel_mono gMiddleSupport.ι).mp
    simp only [Category.assoc, Subcomplex.homOfLE_ι, gSideIso_inclusion]
    rfl
  · rfl
  · rfl

private theorem gFull_isPushout :
    IsPushout (stdSimplex.δ (2 : Fin 4) ≫ gMiddleFilled.{u}) (stdSimplex.δ (2 : Fin 4))
      gFilledSupport.ι gridTopChart := by
  have h := Subcomplex.BicartSq.isPushout
    (show Subcomplex.BicartSq (gFilledSupport ⊓ gTopSupport) gFilledSupport gTopSupport
      (⊤ : pastingGridShape.{u}.Subcomplex) from { sup_eq := gFilledTop_cover, inf_eq := rfl })
  apply h.of_iso' gDiagonalIso (Iso.refl _) gTopIso (Subcomplex.topIso pastingGridShape).symm
  · apply (cancel_mono gFilledSupport.ι).mp
    simp only [Iso.refl_hom, Category.id_comp, Category.assoc, Subcomplex.homOfLE_ι,
      gDiagonalIso_inclusion, gMiddleFilled_ι]
  · apply (cancel_mono gTopSupport.ι).mp
    simp only [Category.assoc, Subcomplex.homOfLE_ι, gDiagonalIso_inclusion]
    change stdSimplex.δ (2 : Fin 4) ≫ gridMiddleChart = stdSimplex.δ (2 : Fin 4) ≫ gridTopChart
    exact gDiagonal_common.symm
  · apply (cancel_mono (Subcomplex.topIso pastingGridShape).hom).mp
    simp only [Iso.refl_hom, Iso.symm_hom, Category.id_comp, Category.assoc, Category.comp_id,
      Subcomplex.topIso_hom, Subcomplex.homOfLE_ι, Subcomplex.topIso_inv_ι]
  · apply (cancel_mono (Subcomplex.topIso pastingGridShape).hom).mp
    simp only [Category.assoc, Iso.symm_hom, Subcomplex.topIso_hom,
      Subcomplex.homOfLE_ι, Subcomplex.topIso_inv_ι, Category.comp_id]
    rfl

private def joinedLowerFilled : (Δ[3] : SSet.{u}) ⟶ (Δ[0] ⋆ (gridLeftFilled : SSet.{u})) :=
  (joinStdSimplexIso 0 2).inv ≫ (join.obj (Δ[0] : SSet.{u})).map gridLowerFilled
private def joinedMiddleFilled : (Δ[3] : SSet.{u}) ⟶ (Δ[0] ⋆ (gridLeftFilled : SSet.{u})) :=
  (joinStdSimplexIso 0 2).inv ≫ (join.obj (Δ[0] : SSet.{u})).map gridLeftMiddleInr

private theorem joinedFilled_isPushout :
    IsPushout (stdSimplex.δ (1 : Fin 4)) (stdSimplex.δ (1 : Fin 4))
      joinedLowerFilled.{u} joinedMiddleFilled := by
  have h := gridFilled_isPushout.map (join.obj (Δ[0] : SSet.{u}))
  apply h.of_iso (joinStdSimplexIso 0 1) (joinStdSimplexIso 0 2)
    (joinStdSimplexIso 0 2) (Iso.refl _)
  · exact joinZeroFace 0
  · exact joinZeroFace 0
  · simp only [Iso.refl_hom, Category.comp_id, joinedLowerFilled, Iso.hom_inv_id_assoc]
  · simp only [Iso.refl_hom, Category.comp_id, joinedMiddleFilled, Iso.hom_inv_id_assoc]

private def gridFilledConeIso : (Δ[0] : SSet.{u}) ⋆ (gridLeftFilled : SSet.{u}) ≅
    (gFilledSupport : SSet.{u}) :=
  joinedFilled_isPushout.isoIsPushout _ _ gFilled_isPushout
private theorem joinedLowerFilled_coneIso :
    joinedLowerFilled.{u} ≫ gridFilledConeIso.hom = gLowerFilled :=
  joinedFilled_isPushout.inl_isoIsPushout_hom _ _ gFilled_isPushout
private theorem joinedMiddleFilled_coneIso :
    joinedMiddleFilled.{u} ≫ gridFilledConeIso.hom = gMiddleFilled :=
  joinedFilled_isPushout.inr_isoIsPushout_hom _ _ gFilled_isPushout

private theorem finalCommon_middle :
    gridLeftFinalCommon.{u} = stdSimplex.δ (1 : Fin 3) ≫ gridLeftMiddleInr := by
  apply (cancel_mono gridLeftFilled.ι).mp
  dsimp only [gridLeftFinalCommon]
  rw [Category.assoc, Subcomplex.homOfLE_ι,
    finalDiagonalIso_inclusion, Category.assoc, gridMiddleFilled_ι]
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

private theorem joinedFinalCommon_coneIso :
    (join.obj (Δ[0] : SSet.{u})).map gridLeftFinalCommon ≫ gridFilledConeIso.hom =
      (joinStdSimplexIso 0 1).hom ≫ stdSimplex.δ (2 : Fin 4) ≫ gMiddleFilled := by
  rw [finalCommon_middle, Functor.map_comp]
  have hm : (join.obj (Δ[0] : SSet.{u})).map gridLeftMiddleInr ≫ gridFilledConeIso.hom =
      (joinStdSimplexIso 0 2).hom ≫ gMiddleFilled := by
    apply (cancel_epi (joinStdSimplexIso.{u} 0 2).inv).mp
    rw [← Category.assoc]
    change joinedMiddleFilled.{u} ≫ gridFilledConeIso.hom = _
    rw [joinedMiddleFilled_coneIso, Iso.inv_hom_id_assoc]
  rw [Category.assoc, hm, ← Category.assoc, joinZeroFace]
  simp only [show (1 : Fin 3).succ = (2 : Fin 4) from by decide, Category.assoc]

private def joinedGridFilled : (gFilledSupport : SSet.{u}) ⟶
    (Δ[0] : SSet.{u}) ⋆ pastingConeShape :=
  gridFilledConeIso.inv ≫ (join.obj (Δ[0] : SSet.{u})).map gridLeftFilled.ι
private def joinedGridTop : (Δ[3] : SSet.{u}) ⟶ (Δ[0] : SSet.{u}) ⋆ pastingConeShape :=
  (joinStdSimplexIso 0 2).inv ≫ (join.obj (Δ[0] : SSet.{u})).map gridTopTriangle

private theorem joinedGrid_isPushout :
    IsPushout (stdSimplex.δ (2 : Fin 4) ≫ gMiddleFilled.{u}) (stdSimplex.δ (2 : Fin 4))
      joinedGridFilled joinedGridTop := by
  have h := gridLeftFinalAttachment_isPushout.map (join.obj (Δ[0] : SSet.{u}))
  apply h.of_iso (joinStdSimplexIso 0 1) gridFilledConeIso (joinStdSimplexIso 0 2) (Iso.refl _)
  · exact joinedFinalCommon_coneIso
  · exact joinZeroFace 1
  · simp only [Iso.refl_hom, Category.comp_id, joinedGridFilled, Iso.hom_inv_id_assoc]
  · simp only [Iso.refl_hom, Category.comp_id, joinedGridTop, Iso.hom_inv_id_assoc]

/-- The original whole grid is exactly the left cone on its original full
five-point index. All three original three-simplex charts occur in its construction. -/
def gridConeIso : (Δ[0] : SSet.{u}) ⋆ pastingConeShape.{u} ≅ pastingGridShape.{u} :=
  joinedGrid_isPushout.isoIsPushout _ _ gFull_isPushout

private theorem joinedGridFilled_iso : joinedGridFilled.{u} ≫ gridConeIso.hom = gFilledSupport.ι :=
  joinedGrid_isPushout.inl_isoIsPushout_hom _ _ gFull_isPushout
private theorem joinedGridTop_iso : joinedGridTop.{u} ≫ gridConeIso.hom = gridTopChart :=
  joinedGrid_isPushout.inr_isoIsPushout_hom _ _ gFull_isPushout

/-!
## Whole original chart and point readbacks
-/

private theorem joinedFilled_full :
    (join.obj (Δ[0] : SSet.{u})).map gridLeftFilled.ι ≫ gridConeIso.hom =
      gridFilledConeIso.hom ≫ gFilledSupport.ι := by
  apply (cancel_epi gridFilledConeIso.inv).mp
  rw [← Category.assoc]
  change joinedGridFilled.{u} ≫ gridConeIso.hom = _
  rw [joinedGridFilled_iso, Iso.inv_hom_id_assoc]

/-- The whole original lower grid chart is the cone on the same original lower triangle. -/
theorem gridConeIso_lower :
    (join.obj (Δ[0] : SSet.{u})).map (gridBottomTriangle ≫ pastingBaseInclusion) ≫
        gridConeIso.hom = (joinStdSimplexIso 0 2).hom ≫ gridLowerChart := by
  rw [← gridLowerFilled_ι, Functor.map_comp, Category.assoc, joinedFilled_full]
  have hc : (join.obj (Δ[0] : SSet.{u})).map gridLowerFilled ≫ gridFilledConeIso.hom =
      (joinStdSimplexIso 0 2).hom ≫ gLowerFilled := by
    apply (cancel_epi (joinStdSimplexIso.{u} 0 2).inv).mp
    rw [← Category.assoc]
    change joinedLowerFilled.{u} ≫ gridFilledConeIso.hom = _
    rw [joinedLowerFilled_coneIso, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, hc, Category.assoc, gLowerFilled_ι]

/-- The whole original middle grid chart is the cone on the same original middle triangle. -/
theorem gridConeIso_middle :
    (join.obj (Δ[0] : SSet.{u})).map gridMiddleTriangle ≫ gridConeIso.hom =
      (joinStdSimplexIso 0 2).hom ≫ gridMiddleChart := by
  rw [← gridMiddleFilled_ι, Functor.map_comp, Category.assoc, joinedFilled_full]
  have hc : (join.obj (Δ[0] : SSet.{u})).map gridLeftMiddleInr ≫ gridFilledConeIso.hom =
      (joinStdSimplexIso 0 2).hom ≫ gMiddleFilled := by
    apply (cancel_epi (joinStdSimplexIso.{u} 0 2).inv).mp
    rw [← Category.assoc]
    change joinedMiddleFilled.{u} ≫ gridFilledConeIso.hom = _
    rw [joinedMiddleFilled_coneIso, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, hc, Category.assoc, gMiddleFilled_ι]

/-- The whole original top grid chart is the cone on the same original top triangle. -/
theorem gridConeIso_top :
    (join.obj (Δ[0] : SSet.{u})).map gridTopTriangle ≫ gridConeIso.hom =
      (joinStdSimplexIso 0 2).hom ≫ gridTopChart := by
  apply (cancel_epi (joinStdSimplexIso.{u} 0 2).inv).mp
  rw [← Category.assoc]
  change joinedGridTop.{u} ≫ gridConeIso.hom = _
  rw [joinedGridTop_iso, Iso.inv_hom_id_assoc]

private theorem joinZeroRight :
    joinInr (Δ[0] : SSet.{u}) Δ[2] ≫ (joinStdSimplexIso 0 2).hom =
      stdSimplex.δ (0 : Fin 4) := by
  have hi : AugmentedSimplexCategory.inr' ⦋0⦌ ⦋2⦌ = SimplexCategory.δ (0 : Fin 4) := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext i
    fin_cases i <;> rfl
  rw [joinInr_comp_joinStdSimplexIso_hom, hi]
  rfl
private theorem joinZeroLeft :
    joinInl (Δ[0] : SSet.{u}) Δ[2] ≫ (joinStdSimplexIso 0 2).hom =
      SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋3⦌ 0) := by
  have hi : AugmentedSimplexCategory.inl' ⦋0⦌ ⦋2⦌ =
      SimplexCategory.const ⦋0⦌ ⦋3⦌ 0 := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext i
    fin_cases i
    rfl
  rw [joinInl_comp_joinStdSimplexIso_hom, hi]

private theorem gridLowerChart_tail : stdSimplex.δ (0 : Fin 4) ≫ gridLowerChart.{u} =
    gridBottomTriangle ≫ pastingBaseInclusion ≫ pastingConeInclusion := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl
private theorem gridMiddleChart_tail : stdSimplex.δ (0 : Fin 4) ≫ gridMiddleChart.{u} =
    gridMiddleTriangle ≫ pastingConeInclusion := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl
private theorem gridTopChart_tail : stdSimplex.δ (0 : Fin 4) ≫ gridTopChart.{u} =
    gridTopTriangle ≫ pastingConeInclusion := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

private theorem gridCone_lower_right :
    (gridBottomTriangle ≫ pastingBaseInclusion) ≫
        (joinInr (Δ[0] : SSet.{u}) pastingConeShape ≫ gridConeIso.hom) =
      gridBottomTriangle ≫ pastingBaseInclusion ≫ pastingConeInclusion := by
  rw [← Category.assoc, map_comp_joinInr, Category.assoc, gridConeIso_lower,
    ← Category.assoc, joinZeroRight, gridLowerChart_tail]
private theorem gridCone_middle_right :
    gridMiddleTriangle ≫ (joinInr (Δ[0] : SSet.{u}) pastingConeShape ≫ gridConeIso.hom) =
      gridMiddleTriangle ≫ pastingConeInclusion := by
  rw [← Category.assoc, map_comp_joinInr, Category.assoc, gridConeIso_middle,
    ← Category.assoc, joinZeroRight, gridMiddleChart_tail]
private theorem gridCone_top_right :
    gridTopTriangle ≫ (joinInr (Δ[0] : SSet.{u}) pastingConeShape ≫ gridConeIso.hom) =
      gridTopTriangle ≫ pastingConeInclusion := by
  rw [← Category.assoc, map_comp_joinInr, Category.assoc, gridConeIso_top,
    ← Category.assoc, joinZeroRight, gridTopChart_tail]

/-- The entire right factor is exactly the original five-point inclusion,
including all original higher simplices. -/
theorem gridConeIso_right : joinInr (Δ[0] : SSet.{u}) pastingConeShape ≫ gridConeIso.hom =
    pastingConeInclusion := by
  apply gridLeftFinalAttachment_isPushout.hom_ext
  · apply gridFilled_isPushout.hom_ext
    · exact (congrArg (fun c : (Δ[2] : SSet.{u}) ⟶ pastingConeShape =>
        c ≫ (joinInr Δ[0] pastingConeShape ≫ gridConeIso.hom) = c ≫ pastingConeInclusion)
          gridLowerFilled_ι).mpr gridCone_lower_right
    · exact (congrArg (fun c : (Δ[2] : SSet.{u}) ⟶ pastingConeShape =>
        c ≫ (joinInr Δ[0] pastingConeShape ≫ gridConeIso.hom) = c ≫ pastingConeInclusion)
          gridMiddleFilled_ι).mpr gridCone_middle_right
  · exact gridCone_top_right

/-- The original initial grid vertex00, as its whole zero-simplex map. -/
def gridInitialPoint : (Δ[0] : SSet.{u}) ⟶ pastingGridShape.{u} :=
  yonedaEquiv.symm (ComposableArrows.mk₀ (⟨(0, 0)⟩ : PastingGridObjects.{u}))
private theorem gridTopChart_initial :
    SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋3⦌ 0) ≫ gridTopChart.{u} = gridInitialPoint := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i
  rfl

/-- The entire left factor is the same original initial grid vertex00. -/
theorem gridConeIso_left : joinInl (Δ[0] : SSet.{u}) pastingConeShape ≫ gridConeIso.hom =
    gridInitialPoint := by
  rw [← joinInl_comp_map (Δ[0] : SSet.{u}) gridTopTriangle, Category.assoc,
    gridConeIso_top, ← Category.assoc, joinZeroLeft, gridTopChart_initial]

/-!
## The whole left and outer square cone comparisons
-/

private theorem leftCospan_rightChart : cospanRightChart.{u} ≫ gridLeftCospan =
    stdSimplex.δ (2 : Fin 3) ≫ gridMiddleTriangle := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl
private theorem leftCospan_leftChart : cospanLeftChart.{u} ≫ gridLeftCospan =
    stdSimplex.δ (2 : Fin 3) ≫ (gridBottomTriangle ≫ pastingBaseInclusion) := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl
private theorem outerCospan_rightChart : cospanRightChart.{u} ≫
    (gridOuterCospan ≫ pastingBaseInclusion) = stdSimplex.δ (0 : Fin 3) ≫ gridTopTriangle := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl
private theorem outerCospan_leftChart : cospanLeftChart.{u} ≫
    (gridOuterCospan ≫ pastingBaseInclusion) =
      stdSimplex.δ (1 : Fin 3) ≫ (gridBottomTriangle ≫ pastingBaseInclusion) := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

private theorem gridLeft_rightTriangle : stdSimplex.δ (3 : Fin 4) ≫ gridMiddleChart.{u} =
    rightTriangle ≫ gridLeftSquare := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl
private theorem gridLeft_leftTriangle : stdSimplex.δ (3 : Fin 4) ≫ gridLowerChart.{u} =
    leftTriangle ≫ gridLeftSquare := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl
private theorem gridOuter_rightTriangle : stdSimplex.δ (1 : Fin 4) ≫ gridTopChart.{u} =
    rightTriangle ≫ gridOuterSquare := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl
private theorem gridOuter_leftTriangle : stdSimplex.δ (2 : Fin 4) ≫ gridLowerChart.{u} =
    leftTriangle ≫ gridOuterSquare := by
  apply yonedaEquiv.injective
  apply nerve.ext_of_isThin
  funext i
  fin_cases i <;> rfl

private theorem joinedRightTriangle :
    (join.obj (Δ[0] : SSet.{u})).map cospanRightChart ≫ shapeJoinIso.inv =
      (joinStdSimplexIso 0 1).hom ≫ rightTriangle := by
  apply (cancel_epi (joinStdSimplexIso.{u} 0 1).inv).mp
  rw [← Category.assoc, ← rightTriangle_comp_shapeJoinIso_hom,
    Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
private theorem joinedLeftTriangle :
    (join.obj (Δ[0] : SSet.{u})).map cospanLeftChart ≫ shapeJoinIso.inv =
      (joinStdSimplexIso 0 1).hom ≫ leftTriangle := by
  apply (cancel_epi (joinStdSimplexIso.{u} 0 1).inv).mp
  rw [← Category.assoc, ← leftTriangle_comp_shapeJoinIso_hom,
    Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]

private theorem joinedIndexedFace (c : (Δ[1] : SSet.{u}) ⟶ cospanShape.{u})
    (l : cospanShape.{u} ⟶ pastingConeShape.{u}) (i : Fin 3)
    (t : (Δ[2] : SSet.{u}) ⟶ pastingConeShape.{u})
    (T : (Δ[3] : SSet.{u}) ⟶ pastingGridShape.{u})
    (hc : c ≫ l = stdSimplex.δ i ≫ t)
    (ht : (join.obj (Δ[0] : SSet.{u})).map t ≫ gridConeIso.hom =
      (joinStdSimplexIso 0 2).hom ≫ T) :
    (join.obj (Δ[0] : SSet.{u})).map c ≫
        (join.obj Δ[0]).map l ≫ gridConeIso.hom =
      (joinStdSimplexIso 0 1).hom ≫ stdSimplex.δ i.succ ≫ T := by
  rw [← Category.assoc, ← Functor.map_comp, hc, Functor.map_comp,
    Category.assoc, ht, ← Category.assoc, joinZeroFace, Category.assoc]

/-- The whole joined left cospan is exactly the original left square cone,
with both original triangles and the original apex. -/
theorem gridConeIso_leftCospan :
    (join.obj (Δ[0] : SSet.{u})).map gridLeftCospan ≫ gridConeIso.hom =
      shapeJoinIso.inv ≫ gridLeftSquare := by
  apply (cospanShape_isPushout.map (join.obj (Δ[0] : SSet.{u}))).hom_ext
  · rw [← Category.assoc _ shapeJoinIso.inv, joinedRightTriangle, Category.assoc]
    have h := joinedIndexedFace cospanRightChart gridLeftCospan 2 gridMiddleTriangle
      gridMiddleChart leftCospan_rightChart gridConeIso_middle
    simpa only [Category.assoc, show (2 : Fin 3).succ = (3 : Fin 4) from by decide,
      gridLeft_rightTriangle] using h
  · rw [← Category.assoc _ shapeJoinIso.inv, joinedLeftTriangle, Category.assoc]
    have h := joinedIndexedFace cospanLeftChart gridLeftCospan 2
      (gridBottomTriangle ≫ pastingBaseInclusion) gridLowerChart leftCospan_leftChart gridConeIso_lower
    simpa only [Category.assoc, show (2 : Fin 3).succ = (3 : Fin 4) from by decide,
      gridLeft_leftTriangle] using h

/-- The whole joined outer cospan is exactly the original outer square cone,
with both original triangles and the original apex. -/
theorem gridConeIso_outerCospan :
    (join.obj (Δ[0] : SSet.{u})).map (gridOuterCospan ≫ pastingBaseInclusion) ≫ gridConeIso.hom =
      shapeJoinIso.inv ≫ gridOuterSquare := by
  apply (cospanShape_isPushout.map (join.obj (Δ[0] : SSet.{u}))).hom_ext
  · rw [← Category.assoc _ shapeJoinIso.inv, joinedRightTriangle, Category.assoc]
    have h := joinedIndexedFace cospanRightChart (gridOuterCospan ≫ pastingBaseInclusion) 0
      gridTopTriangle gridTopChart outerCospan_rightChart gridConeIso_top
    simpa only [Category.assoc, show (0 : Fin 3).succ = (1 : Fin 4) from by decide,
      gridOuter_rightTriangle] using h
  · rw [← Category.assoc _ shapeJoinIso.inv, joinedLeftTriangle, Category.assoc]
    have h := joinedIndexedFace cospanLeftChart (gridOuterCospan ≫ pastingBaseInclusion) 1
      (gridBottomTriangle ≫ pastingBaseInclusion) gridLowerChart outerCospan_leftChart gridConeIso_lower
    simpa only [Category.assoc, show (1 : Fin 3).succ = (2 : Fin 4) from by decide,
      gridOuter_leftTriangle] using h

/-!
## The exact original cone point and its two restrictions
-/

/-- The complete original grid, expressed as its actual left cone. -/
def gridConeDiagram {X : SSet.{u}} (q : pastingGridShape.{u} ⟶ X) :
    (Δ[0] : SSet.{u}) ⋆ pastingConeShape ⟶ X := gridConeIso.hom ≫ q
/-- The whole right factor is exactly the original five-point diagram. -/
theorem gridConeDiagram_fixed {X : SSet.{u}} (q : pastingGridShape.{u} ⟶ X) :
    joinInr (Δ[0] : SSet.{u}) pastingConeShape ≫ gridConeDiagram q = pastingConeInclusion ≫ q := by
  rw [gridConeDiagram, ← Category.assoc, gridConeIso_right]
/-- The original entire grid cone gives its original point in the original diagram over-slice. -/
def gridConePoint {X : SSet.{u}} (q : pastingGridShape.{u} ⟶ X) :
    (Δ[0] : SSet.{u}) ⟶ sliceOver X (pastingConeInclusion ≫ q) :=
  sliceOver.conePoint _ (gridConeDiagram q) (gridConeDiagram_fixed q)

private theorem gridLeft_fixed {X : SSet.{u}} (q : pastingGridShape.{u} ⟶ X) :
    gridLeftCospan ≫ (pastingConeInclusion ≫ q) = cospanInclusion ≫ (gridLeftSquare ≫ q) := by
  rw [← Category.assoc, gridLeftCospan_comp, Category.assoc]
private theorem gridOuter_fixed {X : SSet.{u}} (q : pastingGridShape.{u} ⟶ X) :
    (gridOuterCospan ≫ pastingBaseInclusion) ≫ (pastingConeInclusion ≫ q) =
      cospanInclusion ≫ (gridOuterSquare ≫ q) := by
  rw [← Category.assoc, Category.assoc gridOuterCospan,
    gridOuterCospan_comp, Category.assoc]

/-- The actual original cone-to-left-cospan restriction, with the same literal fixed diagram. -/
def gridLeftRestriction {X : SSet.{u}} (q : pastingGridShape.{u} ⟶ X) :
    sliceOver X (pastingConeInclusion ≫ q) ⟶ sliceOver X (cospanInclusion ≫ (gridLeftSquare ≫ q)) :=
  sliceOver.restrict X (pastingConeInclusion ≫ q) gridLeftCospan ≫
    eqToHom (congrArg (sliceOver X) (gridLeft_fixed q))
/-- The actual original cone-to-outer-cospan restriction, with the same literal fixed diagram. -/
def gridOuterRestriction {X : SSet.{u}} (q : pastingGridShape.{u} ⟶ X) :
    sliceOver X (pastingConeInclusion ≫ q) ⟶ sliceOver X (cospanInclusion ≫ (gridOuterSquare ≫ q)) :=
  sliceOver.restrict X (pastingConeInclusion ≫ q) (gridOuterCospan ≫ pastingBaseInclusion) ≫
    eqToHom (congrArg (sliceOver X) (gridOuter_fixed q))

private theorem conePoint_fixedDiagram {X K : SSet.{u}} {f g : K ⟶ X} (h : f = g)
    {a b : (Δ[0] : SSet.{u}) ⋆ K ⟶ X} (ha : joinInr Δ[0] K ≫ a = f)
    (hb : joinInr Δ[0] K ≫ b = g) (hab : a = b) :
    sliceOver.conePoint f a ha ≫ eqToHom (congrArg (sliceOver X) h) = sliceOver.conePoint g b hb := by
  cases h
  cases hab
  rw [eqToHom_refl, Category.comp_id]

/-- Restriction takes the entire original grid cone point to the entire
original left-square cone point, with its original apex and all four legs. -/
theorem gridConePoint_left {X : SSet.{u}} (q : pastingGridShape.{u} ⟶ X) :
    gridConePoint q ≫ gridLeftRestriction q =
      sliceOver.conePoint (cospanInclusion ≫ (gridLeftSquare ≫ q))
        (coneDiagram (gridLeftSquare ≫ q)) (coneDiagram_fixed (gridLeftSquare ≫ q)) := by
  have hp := sliceOver.conePoint_restrict (pastingConeInclusion ≫ q)
    (gridConeDiagram q) (gridConeDiagram_fixed q) gridLeftCospan
  have ht := congrArg (fun p : (Δ[0] : SSet.{u}) ⟶
      sliceOver X (gridLeftCospan ≫ (pastingConeInclusion ≫ q)) =>
    p ≫ eqToHom (congrArg (sliceOver X) (gridLeft_fixed q))) hp
  apply ht.trans
  apply conePoint_fixedDiagram
  · exact gridLeft_fixed q
  · rw [gridConeDiagram, ← Category.assoc, gridConeIso_leftCospan]
    rfl

/-- Restriction takes the entire original grid cone point to the entire
original outer-square cone point, with its original apex and all four legs. -/
theorem gridConePoint_outer {X : SSet.{u}} (q : pastingGridShape.{u} ⟶ X) :
    gridConePoint q ≫ gridOuterRestriction q =
      sliceOver.conePoint (cospanInclusion ≫ (gridOuterSquare ≫ q))
        (coneDiagram (gridOuterSquare ≫ q)) (coneDiagram_fixed (gridOuterSquare ≫ q)) := by
  have hp := sliceOver.conePoint_restrict (pastingConeInclusion ≫ q)
    (gridConeDiagram q) (gridConeDiagram_fixed q) (gridOuterCospan ≫ pastingBaseInclusion)
  have ht := congrArg (fun p : (Δ[0] : SSet.{u}) ⟶
      sliceOver X ((gridOuterCospan ≫ pastingBaseInclusion) ≫ (pastingConeInclusion ≫ q)) =>
    p ≫ eqToHom (congrArg (sliceOver X) (gridOuter_fixed q))) hp
  apply ht.trans
  apply conePoint_fixedDiagram
  · exact gridOuter_fixed q
  · rw [gridConeDiagram, ← Category.assoc, gridConeIso_outerCospan]
    rfl

/-- The literal left restriction lifts every boundary for the whole original grid. -/
theorem gridLeftRestriction_I_rlp {X : SSet.{u}} [Quasicategory X]
    (q : pastingGridShape.{u} ⟶ X) : modelCategoryQuillen.I.rlp (gridLeftRestriction q) := by
  dsimp only [gridLeftRestriction]
  exact modelCategoryQuillen.I.rlp.comp_mem _ _
    (gridConeLeftRestriction_I_rlp _) (modelCategoryQuillen.I.rlp.of_isIso _)
/-- The literal outer restriction lifts every boundary under the original right-square PB. -/
theorem gridOuterRestriction_I_rlp {X : SSet.{u}} [Quasicategory X]
    (q : pastingGridShape.{u} ⟶ X)
    (hq : IsPullbackSquare (pastingRightSquare ≫ pastingConeInclusion ≫ q)) :
    modelCategoryQuillen.I.rlp (gridOuterRestriction q) := by
  dsimp only [gridOuterRestriction]
  exact modelCategoryQuillen.I.rlp.comp_mem _ _
    (gridConeOuterRestriction_I_rlp _ hq) (modelCategoryQuillen.I.rlp.of_isIso _)

/-!
## The source pullback pasting law at the same original point
-/

private theorem gridLeft_terminality {X : SSet.{u}} [Quasicategory X]
    (q : pastingGridShape.{u} ⟶ X) :
    IsTerminalVertex (gridConePoint q) ↔ IsTerminalVertex (gridConePoint q ≫ gridLeftRestriction q) := by
  let : Quasicategory (sliceOver X (pastingConeInclusion ≫ q)) :=
    quasicategory_sliceOver X _
  let : Quasicategory (sliceOver X (cospanInclusion ≫ (gridLeftSquare ≫ q))) :=
    quasicategory_sliceOver X _
  exact WalkingAdjunction.rightTerminalVertex_iff_map_of_categoricalEquivalence
    (gridLeftRestriction q)
    (modelCategoryQuillen_I_rlp_le_categoricalEquivalences _ (gridLeftRestriction_I_rlp q))
    (gridConePoint q)
private theorem gridOuter_terminality {X : SSet.{u}} [Quasicategory X]
    (q : pastingGridShape.{u} ⟶ X)
    (hq : IsPullbackSquare (pastingRightSquare ≫ pastingConeInclusion ≫ q)) :
    IsTerminalVertex (gridConePoint q) ↔ IsTerminalVertex (gridConePoint q ≫ gridOuterRestriction q) := by
  let : Quasicategory (sliceOver X (pastingConeInclusion ≫ q)) :=
    quasicategory_sliceOver X _
  let : Quasicategory (sliceOver X (cospanInclusion ≫ (gridOuterSquare ≫ q))) :=
    quasicategory_sliceOver X _
  exact WalkingAdjunction.rightTerminalVertex_iff_map_of_categoricalEquivalence
    (gridOuterRestriction q)
    (modelCategoryQuillen_I_rlp_le_categoricalEquivalences _ (gridOuterRestriction_I_rlp q hq))
    (gridConePoint q)

/-- For the entire original coherent grid, an original pullback right square
makes the original left square cartesian exactly when the original outer square is cartesian.
All boundary dimensions and the original apex/four-leg cone points are retained. -/
theorem isPullbackSquare_grid_left_iff_outer {X : SSet.{u}} [Quasicategory X]
    (q : pastingGridShape.{u} ⟶ X)
    (hq : IsPullbackSquare (pastingRightSquare ≫ pastingConeInclusion ≫ q)) :
    IsPullbackSquare (gridLeftSquare ≫ q) ↔ IsPullbackSquare (gridOuterSquare ≫ q) := by
  have hL := gridLeft_terminality q
  have hO := gridOuter_terminality q hq
  rw [gridConePoint_left] at hL
  rw [gridConePoint_outer] at hO
  exact (isPullbackSquare_iff_isTerminalVertex (gridLeftSquare ≫ q)).trans
    (hL.symm.trans (hO.trans (isPullbackSquare_iff_isTerminalVertex (gridOuterSquare ≫ q)).symm))

/-- Pasting the two original pullback squares gives the original outer pullback square. -/
theorem isPullbackSquare_grid_paste {X : SSet.{u}} [Quasicategory X]
    (q : pastingGridShape.{u} ⟶ X)
    (hL : IsPullbackSquare (gridLeftSquare ≫ q))
    (hR : IsPullbackSquare (pastingRightSquare ≫ pastingConeInclusion ≫ q)) :
    IsPullbackSquare (gridOuterSquare ≫ q) :=
  (isPullbackSquare_grid_left_iff_outer q hR).mp hL
/-- Cancelling the original right pullback from the original outer pullback
recovers the original left pullback square. -/
theorem isPullbackSquare_grid_cancel {X : SSet.{u}} [Quasicategory X]
    (q : pastingGridShape.{u} ⟶ X)
    (hR : IsPullbackSquare (pastingRightSquare ≫ pastingConeInclusion ≫ q))
    (hO : IsPullbackSquare (gridOuterSquare ≫ q)) :
    IsPullbackSquare (gridLeftSquare ≫ q) :=
  (isPullbackSquare_grid_left_iff_outer q hR).mpr hO

/-!
## The same original maps under vertical coordinate transposition
-/

/-- The full original vertical two-square grid. -/
abbrev VerticalGridObjects := ULift.{u} (Fin 2 × Fin 3)
/-- The full native vertical grid nerve, including all original higher simplices. -/
abbrev verticalGridShape : SSet.{u} := nerve VerticalGridObjects.{u}
private def transposeFunctor : PastingGridObjects.{u} ⥤ VerticalGridObjects.{u} :=
  (show Monotone (fun v : PastingGridObjects.{u} =>
    (⟨(v.down.2, v.down.1)⟩ : VerticalGridObjects.{u})) from fun _ _ h => ⟨h.2, h.1⟩).functor
private def transposeInverseFunctor : VerticalGridObjects.{u} ⥤ PastingGridObjects.{u} :=
  (show Monotone (fun v : VerticalGridObjects.{u} =>
    (⟨(v.down.2, v.down.1)⟩ : PastingGridObjects.{u})) from fun _ _ h => ⟨h.2, h.1⟩).functor

private theorem transpose_hom_inv_id :
    nerveMap transposeFunctor.{u} ≫ nerveMap transposeInverseFunctor = 𝟙 pastingGridShape := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext i
  rfl

private theorem transpose_inv_hom_id :
    nerveMap transposeInverseFunctor.{u} ≫ nerveMap transposeFunctor = 𝟙 verticalGridShape := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext i
  rfl

/-- The literal coordinate transpose preserves every original grid simplex. -/
def gridTransposeIso : pastingGridShape.{u} ≅ verticalGridShape.{u} where
  hom := nerveMap transposeFunctor
  inv := nerveMap transposeInverseFunctor
  hom_inv_id := transpose_hom_inv_id
  inv_hom_id := transpose_inv_hom_id

private def verticalTopFunctor : DiamondObjects.{u} ⥤ VerticalGridObjects.{u} :=
  nativeSquareOfCone (PullbackCone.mk
    (homOfLE (show (⟨(0, 0)⟩ : VerticalGridObjects.{u}) ≤ ⟨(1, 0)⟩ from ⟨by decide, le_rfl⟩))
    (homOfLE (show (⟨(0, 0)⟩ : VerticalGridObjects.{u}) ≤ ⟨(0, 1)⟩ from ⟨le_rfl, by decide⟩))
    (f := homOfLE (show (⟨(1, 0)⟩ : VerticalGridObjects.{u}) ≤ ⟨(1, 1)⟩ from ⟨le_rfl, by decide⟩))
    (g := homOfLE (show (⟨(0, 1)⟩ : VerticalGridObjects.{u}) ≤ ⟨(1, 1)⟩ from ⟨by decide, le_rfl⟩))
    (Subsingleton.elim _ _))

private def verticalBottomFunctor : DiamondObjects.{u} ⥤ VerticalGridObjects.{u} :=
  nativeSquareOfCone (PullbackCone.mk
    (homOfLE (show (⟨(0, 1)⟩ : VerticalGridObjects.{u}) ≤ ⟨(1, 1)⟩ from ⟨by decide, le_rfl⟩))
    (homOfLE (show (⟨(0, 1)⟩ : VerticalGridObjects.{u}) ≤ ⟨(0, 2)⟩ from ⟨le_rfl, by decide⟩))
    (f := homOfLE (show (⟨(1, 1)⟩ : VerticalGridObjects.{u}) ≤ ⟨(1, 2)⟩ from ⟨le_rfl, by decide⟩))
    (g := homOfLE (show (⟨(0, 2)⟩ : VerticalGridObjects.{u}) ≤ ⟨(1, 2)⟩ from ⟨by decide, le_rfl⟩))
    (Subsingleton.elim _ _))

private def verticalOuterFunctor : DiamondObjects.{u} ⥤ VerticalGridObjects.{u} :=
  nativeSquareOfCone (PullbackCone.mk
    (homOfLE (show (⟨(0, 0)⟩ : VerticalGridObjects.{u}) ≤ ⟨(1, 0)⟩ from ⟨by decide, le_rfl⟩))
    (homOfLE (show (⟨(0, 0)⟩ : VerticalGridObjects.{u}) ≤ ⟨(0, 2)⟩ from ⟨le_rfl, by decide⟩))
    (f := homOfLE (show (⟨(1, 0)⟩ : VerticalGridObjects.{u}) ≤ ⟨(1, 2)⟩ from ⟨le_rfl, by decide⟩))
    (g := homOfLE (show (⟨(0, 2)⟩ : VerticalGridObjects.{u}) ≤ ⟨(1, 2)⟩ from ⟨by decide, le_rfl⟩))
    (Subsingleton.elim _ _))

/-- The entire original upper square of the vertical grid. -/
def verticalTopSquare : squareShape.{u} ⟶ verticalGridShape.{u} :=
  nerveMapHomDown.{u, 0, u} verticalTopFunctor
/-- The entire original lower square of the vertical grid. -/
def verticalBottomSquare : squareShape.{u} ⟶ verticalGridShape.{u} :=
  nerveMapHomDown.{u, 0, u} verticalBottomFunctor
/-- The entire original outer square of the vertical grid. -/
def verticalOuterSquare : squareShape.{u} ⟶ verticalGridShape.{u} :=
  nerveMapHomDown.{u, 0, u} verticalOuterFunctor

/-- The whole original left square becomes the upper square with its coordinates transposed. -/
theorem gridLeftSquare_transpose : gridLeftSquare.{u} ≫ gridTransposeIso.hom =
    squareSwapIso.hom ≫ verticalTopSquare := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext i
  change transposeFunctor.obj (gridLeftFunctor.obj (s.obj i)) =
    verticalTopFunctor.obj (swapFunctor.obj (s.obj i))
  cases s.obj i with
  | star => rfl
  | of v =>
    rcases v with ⟨v⟩
    cases v with
    | none => rfl
    | some v => cases v <;> rfl
/-- The whole original right square becomes the lower square with its coordinates transposed. -/
theorem gridRightSquare_transpose : pastingRightSquare.{u} ≫ pastingConeInclusion ≫ gridTransposeIso.hom =
    squareSwapIso.hom ≫ verticalBottomSquare := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext i
  apply ULift.ext
  change ((((pastingRightSquare.app n) s).obj i).val.down.2,
    (((pastingRightSquare.app n) s).obj i).val.down.1) =
      (verticalBottomFunctor.obj (swapFunctor.obj (s.obj i))).down
  rw [pastingRightSquare_app_obj]
  cases s.obj i with
  | star => rfl
  | of v =>
    rcases v with ⟨v⟩
    cases v with
    | none => rfl
    | some v => cases v <;> rfl
/-- The whole original outer square becomes the vertical outer square with transposed coordinates. -/
theorem gridOuterSquare_transpose : gridOuterSquare.{u} ≫ gridTransposeIso.hom =
    squareSwapIso.hom ≫ verticalOuterSquare := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext i
  change transposeFunctor.obj (gridOuterFunctor.obj (s.obj i)) =
    verticalOuterFunctor.obj (swapFunctor.obj (s.obj i))
  cases s.obj i with
  | star => rfl
  | of v =>
    rcases v with ⟨v⟩
    cases v with
    | none => rfl
    | some v => cases v <;> rfl

/-- The full original vertical grid has the same source pasting law:
a pullback lower square makes the upper square cartesian exactly when the outer square is. -/
theorem isPullbackSquare_vertical_top_iff_outer {X : SSet.{u}} [Quasicategory X]
    (q : verticalGridShape.{u} ⟶ X) (hq : IsPullbackSquare (verticalBottomSquare ≫ q)) :
    IsPullbackSquare (verticalTopSquare ≫ q) ↔ IsPullbackSquare (verticalOuterSquare ≫ q) := by
  have hR : IsPullbackSquare (pastingRightSquare ≫ pastingConeInclusion ≫ (gridTransposeIso.hom ≫ q)) := by
    have hi := congrArg (fun i : squareShape.{u} ⟶ verticalGridShape.{u} =>
      IsPullbackSquare (i ≫ q)) gridRightSquare_transpose
    exact hi.mpr ((isPullbackSquare_swap_iff (verticalBottomSquare ≫ q)).mp hq)
  have h := isPullbackSquare_grid_left_iff_outer (gridTransposeIso.hom ≫ q) hR
  rw [← Category.assoc gridLeftSquare, gridLeftSquare_transpose, Category.assoc,
    ← Category.assoc gridOuterSquare, gridOuterSquare_transpose, Category.assoc] at h
  exact (isPullbackSquare_swap_iff (verticalTopSquare ≫ q)).trans
    (h.trans (isPullbackSquare_swap_iff (verticalOuterSquare ≫ q)).symm)

/-- Pasting the two original vertical pullback squares gives the original outer square. -/
theorem isPullbackSquare_vertical_paste {X : SSet.{u}} [Quasicategory X]
    (q : verticalGridShape.{u} ⟶ X)
    (hT : IsPullbackSquare (verticalTopSquare ≫ q))
    (hB : IsPullbackSquare (verticalBottomSquare ≫ q)) : IsPullbackSquare (verticalOuterSquare ≫ q) :=
  (isPullbackSquare_vertical_top_iff_outer q hB).mp hT
/-- Cancelling the original lower pullback from the original vertical outer pullback
recovers the original upper pullback square. -/
theorem isPullbackSquare_vertical_cancel {X : SSet.{u}} [Quasicategory X]
    (q : verticalGridShape.{u} ⟶ X)
    (hB : IsPullbackSquare (verticalBottomSquare ≫ q))
    (hO : IsPullbackSquare (verticalOuterSquare ≫ q)) : IsPullbackSquare (verticalTopSquare ≫ q) :=
  (isPullbackSquare_vertical_top_iff_outer q hB).mpr hO

end SSet.NativePullback
