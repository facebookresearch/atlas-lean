/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.SmallObject.IsCardinalForSmallObjectArgument
public import Mathlib.SetTheory.Cardinal.HasCardinalLT

@[expose] public section
set_option autoImplicit false
noncomputable section
universe U uC vC
open CategoryTheory CategoryTheory.Limits Cardinal Opposite
namespace CategoryTheory.SmallObject
variable {C : Type uC} [Category.{vC} C]
    (M : MorphismProperty C) (κ : Cardinal.{U})
    [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [M.IsCardinalForSmallObjectArgument κ]

section AbsolutePresentability
variable [IsAccessibleCategory.{U} C]
include κ

/-- Absolute presentability of BOTH original endpoints, at a regular cardinal
also larger than the actual supplied fixed point/operator type. -/
theorem original_endpoints_have_common_presentability_cardinal
    (fixed : Type U) :
    ∃ (μ : Cardinal.{U}) (hμ : Fact μ.IsRegular),
      letI : Fact μ.IsRegular := hμ
      ℵ₀ < μ ∧ HasCardinalLT fixed μ ∧
        ∀ i : M.toSet,
          IsCardinalPresentable.{U} i.1.left μ ∧
            IsCardinalPresentable.{U} i.1.right μ := by
  let _ : MorphismProperty.IsSmall.{U} M := SmallObject.isSmall M κ
  let E := M.toSet ⊕ M.toSet
  let _ : Small.{U} E := inferInstance
  let endpoints : E → C := fun s =>
    match s with
    | .inl i => i.1.left
    | .inr i => i.1.right
  let P : ObjectProperty C := ObjectProperty.ofObj endpoints
  let _ : ObjectProperty.Small.{U} P := inferInstance
  let _ : ObjectProperty.EssentiallySmall.{U} P := inferInstance
  obtain ⟨μ₀, hμ₀, hP⟩ := ObjectProperty.le_isCardinalPresentable P
  let _ : Fact μ₀.IsRegular := hμ₀
  let Upper := μ₀.ord.ToType ⊕ ((ℵ₀ : Cardinal.{U}).ord.ToType ⊕ fixed)
  obtain ⟨μ, hμ, hUpper⟩ := HasCardinalLT.exists_regular_cardinal.{U} Upper
  let _ : Fact μ.IsRegular := ⟨hμ⟩
  have hμ₀ : μ₀ < μ := by
    have h := hUpper.of_injective
      (Sum.inl : μ₀.ord.ToType → Upper) Sum.inl_injective
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h
  have hω : (ℵ₀ : Cardinal.{U}) < μ := by
    have h := hUpper.of_injective
      (fun x : (ℵ₀ : Cardinal.{U}).ord.ToType =>
        (Sum.inr (Sum.inl x) : Upper))
      (Sum.inr_injective.comp Sum.inl_injective)
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h
  have hfixed : HasCardinalLT fixed μ :=
    hUpper.of_injective (fun x : fixed => (Sum.inr (Sum.inr x) : Upper))
      (Sum.inr_injective.comp Sum.inr_injective)
  have h₀ (s : E) : IsCardinalPresentable (endpoints s) μ₀ :=
    hP _ (ObjectProperty.ofObj_apply endpoints s)
  have h (s : E) : IsCardinalPresentable (endpoints s) μ := by
    let _ : IsCardinalPresentable (endpoints s) μ₀ := h₀ s
    exact isCardinalPresentable_of_le (endpoints s) hμ₀.le
  refine ⟨μ, inferInstance, hω, hfixed, ?_⟩
  intro i
  exact ⟨h (.inl i), h (.inr i)⟩

end AbsolutePresentability

section NumericProfile
universe u w vD

/-- An infinite fixed numeric profile for the same original family and κ. It
bounds κ, μ, the working index copy, both endpoint total-point types, and the
supplied fixed type. It gives no bound on a replacement output and constructs
no replacement functor or `Q`. -/
theorem exists_original_fixed_total_point_profile
    (M : MorphismProperty C) (κ : Cardinal.{max u w})
    [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [M.IsCardinalForSmallObjectArgument κ]
    {D : Type w} [Category.{vD} D]
    (F : C ⥤ Dᵒᵖ ⥤ Type (max u w))
    (μ : Cardinal.{max u w}) (fixed : Type (max u w)) :
    ∃ ξ : Cardinal.{max u w},
      ℵ₀ ≤ ξ ∧ κ ≤ ξ ∧ μ ≤ ξ ∧
      (letI : MorphismProperty.IsSmall.{max u w} M := SmallObject.isSmall M κ
       Cardinal.mk (Shrink.{max u w} M.toSet) ≤ ξ) ∧
      (∀ i : M.toSet, Cardinal.mk (F.obj i.1.left).Elements ≤ ξ) ∧
      (∀ i : M.toSet, Cardinal.mk (F.obj i.1.right).Elements ≤ ξ) ∧
      Cardinal.mk fixed ≤ ξ ∧ ((2 : Cardinal.{max u w}) ^ ξ) ^ ξ =
          (2 : Cardinal.{max u w}) ^ ξ ∧ ξ < 2 ^ ξ := by
  let _ : MorphismProperty.IsSmall.{max u w} M := SmallObject.isSmall M κ
  let K : Type (max u w) := Shrink.{max u w} M.toSet
  let e : M.toSet ≃ K := equivShrink.{max u w} M.toSet
  let constants : Fin 5 → Type (max u w) := fun n =>
    match n.val with
    | 0 => (ℵ₀ : Cardinal.{max u w}).ord.ToType
    | 1 => κ.ord.ToType
    | 2 => μ.ord.ToType
    | 3 => K
    | _ => fixed
  let profile : (Fin 5 ⊕ (K ⊕ K)) → Type (max u w) := fun s =>
    match s with
    | .inl n => constants n
    | .inr (.inl k) => (F.obj (e.symm k).1.left).Elements
    | .inr (.inr k) => (F.obj (e.symm k).1.right).Elements
  obtain ⟨ξ, _hξ, hprofile⟩ :=
    HasCardinalLT.exists_regular_cardinal_forall.{max u w} profile
  have hbound (s : Fin 5 ⊕ (K ⊕ K)) : Cardinal.mk (profile s) ≤ ξ :=
    ((hasCardinalLT_iff_cardinal_mk_lt (profile s) ξ).mp (hprofile s)).le
  have hω : (ℵ₀ : Cardinal.{max u w}) ≤ ξ := by
    simpa only [profile, constants, Cardinal.mk_ord_toType] using
      hbound (.inl ⟨0, by decide⟩)
  have hκ : κ ≤ ξ := by
    simpa only [profile, constants, Cardinal.mk_ord_toType] using
      hbound (.inl ⟨1, by decide⟩)
  have hμ : μ ≤ ξ := by
    simpa only [profile, constants, Cardinal.mk_ord_toType] using
      hbound (.inl ⟨2, by decide⟩)
  have hK : Cardinal.mk K ≤ ξ := by
    simpa only [profile, constants] using hbound (.inl ⟨3, by decide⟩)
  have hA (i : M.toSet) : Cardinal.mk (F.obj i.1.left).Elements ≤ ξ := by
    simpa only [profile, Equiv.symm_apply_apply] using hbound (.inr (.inl (e i)))
  have hB (i : M.toSet) : Cardinal.mk (F.obj i.1.right).Elements ≤ ξ := by
    simpa only [profile, Equiv.symm_apply_apply] using hbound (.inr (.inr (e i)))
  have hfixed : Cardinal.mk fixed ≤ ξ := by
    simpa only [profile, constants] using hbound (.inl ⟨4, by decide⟩)
  refine ⟨ξ, hω, hκ, hμ, hK, hA, hB, hfixed, ?_, Cardinal.cantor ξ⟩
  rw [← Cardinal.power_mul, Cardinal.mul_eq_self hω]

end NumericProfile

end CategoryTheory.SmallObject
