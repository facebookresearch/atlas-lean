/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.NatTrans.Cardinality
public import Mathlib.CategoryTheory.SmallObject.Construction
public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-! # Original terminal attachment total-point bound

The native unit and full original labelled cells jointly cover the actual
one-step attachment. Terminal uniqueness and the original Hom bound give
the fixed γ envelope without generator monicity.
-/

public section
set_option autoImplicit false
noncomputable section
universe u w v s
open CategoryTheory CategoryTheory.Limits Cardinal Opposite
namespace CategoryTheory.SmallObject
variable {D : Type w} [Category.{v} D] {I : Type s} [Small.{max u w} I]
    {A B : I → Dᵒᵖ ⥤ Type (max u w)} (j : ∀ i, A i ⟶ B i)
    (X : Dᵒᵖ ⥤ Type (max u w))
    [HasColimitsOfShape (Discrete (FunctorObjIndex j (terminal.from X)))
      (Dᵒᵖ ⥤ Type (max u w))]
    [HasPushout (functorObjTop j (terminal.from X))
      (functorObjLeft j (terminal.from X))]

/-- The original terminal one-step attachment fits the fixed γ envelope. -/
theorem presheafAttachment_terminal_mk_elements_le
    (ξ : Cardinal.{max u w}) (hξ : ℵ₀ ≤ ξ)
    (hI : Cardinal.mk (Shrink.{max u w} I) ≤ ξ)
    (hA : ∀ i, Cardinal.mk (A i).Elements ≤ ξ)
    (hB : ∀ i, Cardinal.mk (B i).Elements ≤ ξ)
    (hX : Cardinal.mk X.Elements ≤ 2 ^ ξ) :
    Cardinal.mk (functorObj j (terminal.from X)).Elements ≤ 2 ^ ξ := by
  classical
  let attachmentCover :
      X.Elements ⊕ (Σ q : FunctorObjIndex j (terminal.from X), (B q.i).Elements) →
        (functorObj j (terminal.from X)).Elements :=
    Sum.elim
      (fun e => Functor.elementsMk _ e.obj ((ιFunctorObj j (terminal.from X)).app e.obj e.val))
      (fun e => Functor.elementsMk _ e.2.obj
        ((Sigma.ι (functorObjTgtFamily j (terminal.from X)) e.1 ≫
          ρFunctorObj j (terminal.from X)).app e.2.obj e.2.val))
  have attachmentCover_surjective : Function.Surjective (attachmentCover) := by
    intro e
    let E := (evaluation Dᵒᵖ (Type (max u w))).obj e.obj
    have hp := (functorObj_isPushout j (terminal.from X)).map E
    obtain ⟨x, hx⟩ | ⟨b, hb⟩ := Types.eq_or_eq_of_isPushout hp e.val
    · refine ⟨Sum.inl (Functor.elementsMk X e.obj x), ?_⟩
      change Functor.elementsMk (functorObj j (terminal.from X)) e.obj
        ((ιFunctorObj j (terminal.from X)).app e.obj x) = e
      apply Functor.Elements.ext
        (Functor.elementsMk (functorObj j (terminal.from X)) e.obj
          ((ιFunctorObj j (terminal.from X)).app e.obj x)) e rfl
      simpa only [E, evaluation_obj_obj, evaluation_obj_map,
        eqToHom_refl, Functor.map_id, types_id_apply] using hx
    · let c : Cofan (fun q : FunctorObjIndex j (terminal.from X) => (B q.i).obj e.obj) :=
        Cofan.mk ((∐ functorObjTgtFamily j (terminal.from X)).obj e.obj)
          (fun q => (Sigma.ι (functorObjTgtFamily j (terminal.from X)) q).app e.obj)
      have hc : IsColimit c := isColimitCofanMkObjOfIsColimit E
        (functorObjTgtFamily j (terminal.from X))
        (fun q => Sigma.ι (functorObjTgtFamily j (terminal.from X)) q)
        (coproductIsCoproduct _)
      obtain ⟨q, z, hz⟩ := Cofan.inj_jointly_surjective_of_isColimit hc b
      refine ⟨Sum.inr ⟨q, Functor.elementsMk (B q.i) e.obj z⟩, ?_⟩
      change Functor.elementsMk (functorObj j (terminal.from X)) e.obj
        ((Sigma.ι (functorObjTgtFamily j (terminal.from X)) q ≫
          ρFunctorObj j (terminal.from X)).app e.obj z) = e
      apply Functor.Elements.ext
        (Functor.elementsMk (functorObj j (terminal.from X)) e.obj
          ((Sigma.ι (functorObjTgtFamily j (terminal.from X)) q ≫
            ρFunctorObj j (terminal.from X)).app e.obj z)) e rfl
      simp only [eqToHom_refl, Functor.map_id, types_id_apply]
      change (Sigma.ι (functorObjTgtFamily j (terminal.from X)) q ≫
        ρFunctorObj j (terminal.from X)).app e.obj z = e.val
      change (ρFunctorObj j (terminal.from X)).app e.obj
        ((Sigma.ι (functorObjTgtFamily j (terminal.from X)) q).app e.obj z) = e.val
      exact (congrArg (fun z => (ρFunctorObj j (terminal.from X)).app e.obj z) hz).trans hb
  let γ : Cardinal.{max u w} := 2 ^ ξ
  have hξγ : ξ ≤ γ := (Cardinal.cantor ξ).le
  have hγ : ℵ₀ ≤ γ := hξ.trans hξγ
  have hγ0 : γ ≠ 0 := ne_of_gt ((show 0 ≤ ξ from zero_le).trans_lt (Cardinal.cantor ξ))
  have hHom (i : I) : Cardinal.mk (A i ⟶ X) ≤ γ := by
    calc
      _ ≤ Cardinal.mk X.Elements ^ Cardinal.mk (A i).Elements :=
        CategoryTheory.mk_hom_le_elements_power (A i) X
      _ ≤ γ ^ Cardinal.mk (A i).Elements := Cardinal.power_le_power_right hX
      _ ≤ γ ^ ξ := Cardinal.power_le_power_left hγ0 (hA i)
      _ = γ := by dsimp [γ]; rw [← Cardinal.power_mul, Cardinal.mul_eq_self hξ]
  let e : I ≃ Shrink.{max u w} I := equivShrink I
  let T : Type (max u w) :=
    Σ k : Shrink.{max u w} I, ((A (e.symm k) ⟶ X) × (B (e.symm k)).Elements)
  let φ : (Σ q : FunctorObjIndex j (terminal.from X), (B q.i).Elements) → T := fun z =>
    ⟨e z.1.i, (eqToHom (congrArg A (e.symm_apply_apply z.1.i)) ≫ z.1.t,
      cast (congrArg (fun i => (B i).Elements) (e.symm_apply_apply z.1.i).symm) z.2)⟩
  have hφ : Function.Injective φ := by
    rintro ⟨⟨i, top, bottom, square⟩, point⟩ ⟨⟨i', top', bottom', square'⟩, point'⟩ h
    have hi : i = i' := e.injective (congrArg Sigma.fst h)
    cases hi
    dsimp only [φ, T] at h
    have hp := eq_of_heq (Sigma.mk.inj h).2
    have htMap : eqToHom (congrArg A (e.symm_apply_apply i)) ≫ top =
        eqToHom (congrArg A (e.symm_apply_apply i)) ≫ top' :=
      congrArg (fun z : (A (e.symm (e i)) ⟶ X) × (B (e.symm (e i))).Elements => z.1) hp
    have ht : top = top' :=
      (cancel_epi (eqToHom (congrArg A (e.symm_apply_apply i)))).1 htMap
    cases ht
    have hb : bottom = bottom' := terminalIsTerminal.hom_ext _ _
    cases hb
    have hzCast :
        cast (congrArg (fun i => (B i).Elements) (e.symm_apply_apply i).symm) point =
        cast (congrArg (fun i => (B i).Elements) (e.symm_apply_apply i).symm) point' :=
      congrArg (fun z : (A (e.symm (e i)) ⟶ X) × (B (e.symm (e i))).Elements => z.2) hp
    have hz : point = point' := (cast_inj _).1 hzCast
    cases hz
    rfl
  let sourceSmall : Type (max u w) := X.Elements ⊕ T
  let injection : (X.Elements ⊕ Σ q : FunctorObjIndex j (terminal.from X), (B q.i).Elements) →
      sourceSmall := Sum.map (fun e => e) φ
  have hinj : Function.Injective injection := Function.injective_id.sumMap hφ
  have hcover := Cardinal.lift_mk_le_lift_mk_of_surjective (attachmentCover_surjective)
  have hinjCard := Cardinal.lift_mk_le_lift_mk_of_injective hinj
  have hOut : Cardinal.mk (functorObj j (terminal.from X)).Elements ≤ Cardinal.mk sourceSmall := by
    apply Cardinal.lift_le.1
    simpa only [Cardinal.lift_lift, Cardinal.lift_id] using hcover.trans hinjCard
  have hPair (k : Shrink.{max u w} I) :
      Cardinal.mk ((A (e.symm k) ⟶ X) × (B (e.symm k)).Elements) ≤ γ := by
    rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.mul_le_of_le hγ (hHom _) ((hB _).trans hξγ)
  have hT : Cardinal.mk T ≤ γ := by
    dsimp [T]
    rw [Cardinal.mk_sigma]
    calc
      _ ≤ Cardinal.sum (fun _ : Shrink.{max u w} I => γ) := Cardinal.sum_le_sum _ _ hPair
      _ = Cardinal.mk (Shrink.{max u w} I) * γ := Cardinal.sum_const' _ _
      _ ≤ γ := Cardinal.mul_le_of_le hγ (hI.trans hξγ) le_rfl
  exact hOut.trans (by
    change Cardinal.mk (X.Elements ⊕ T) ≤ γ
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_le_of_le hγ hX hT)

end CategoryTheory.SmallObject
