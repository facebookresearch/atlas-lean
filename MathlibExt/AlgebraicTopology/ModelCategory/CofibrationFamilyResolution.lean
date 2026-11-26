/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantSpanReplacement
public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.MorphismProperty.IsSmall
public import Mathlib.CategoryTheory.SmallObject.Basic
public import Mathlib.SetTheory.Cardinal.HasCardinalLT

/-!
# Small original families resolved by cofibrations

The original indexing type is retained. Both comparison legs are trivial
fibrations, and one constructed regular cardinal controls every original and
resolved endpoint and the actual native small-object argument.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe w u v s

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [IsLocallyPresentable.{w} C] {I : Type s} [Small.{w} I]

/-- Every original small family has actual cofibration resolutions, with both
comparison legs, all four endpoint ranks and native SOA at one produced cardinal. -/
theorem exists_small_cofibration_family_resolution
    (S : I → Arrow C) (fixed : Type w) :
    ∃ (T : I → Arrow C) (r : ∀ i, T i ⟶ S i)
      (κ : Cardinal.{w}) (hκ : Fact κ.IsRegular) (hbot : OrderBot κ.ord.ToType),
      letI : Fact κ.IsRegular := hκ
      letI : OrderBot κ.ord.ToType := hbot
      ℵ₀ < κ ∧ HasCardinalLT (Shrink.{w} I) κ ∧ HasCardinalLT fixed κ ∧
        (∀ i, IsCofibrant (T i).left ∧ cofibrations C (T i).hom ∧
          trivialFibrations C (r i).left ∧ trivialFibrations C (r i).right) ∧
        (∀ i, IsCardinalPresentable (S i).left κ ∧
          IsCardinalPresentable (S i).right κ ∧
          IsCardinalPresentable (T i).left κ ∧
          IsCardinalPresentable (T i).right κ) ∧
        (MorphismProperty.ofHoms (fun i => (T i).hom)).IsSmall.{w} ∧
        (MorphismProperty.ofHoms (fun i => (T i).hom)).IsCardinalForSmallObjectArgument κ ∧
        (MorphismProperty.ofHoms (fun i => (T i).hom)).HasSmallObjectArgument.{w} ∧
        Nonempty (MorphismProperty.FunctorialFactorizationData
          (MorphismProperty.ofHoms (fun i => (T i).hom)).rlp.llp
          (MorphismProperty.ofHoms (fun i => (T i).hom)).rlp) := by
  let _ : HasColimitsOfSize.{w, w} C := by
    obtain ⟨μ₀, hμ₀, hC⟩ := IsLocallyPresentable.exists_cardinal.{w} C
    let _ : Fact μ₀.IsRegular := hμ₀
    let _ := hC
    infer_instance
  let R (i : I) : CofibrantSpanReplacement (span (S i).hom (𝟙 (S i).left)) :=
    (CofibrantSpanReplacement.nonempty _).some
  let T (i : I) : Arrow C := Arrow.mk ((R i).Q.map WalkingSpan.Hom.fst)
  let r (i : I) : T i ⟶ S i :=
    Arrow.homMk ((R i).counit.app WalkingSpan.zero)
      ((R i).counit.app WalkingSpan.left)
      ((R i).counit.naturality WalkingSpan.Hom.fst).symm
  have hResolution (i : I) :
      IsCofibrant (T i).left ∧ cofibrations C (T i).hom ∧
        trivialFibrations C (r i).left ∧ trivialFibrations C (r i).right :=
    ⟨(R i).isCofibrant_zero, (R i).cofibration_fst.mem,
      (R i).counit_app_mem_trivialFibrations WalkingSpan.zero,
      (R i).counit_app_mem_trivialFibrations WalkingSpan.left⟩
  let endpoints : I × Fin 4 → C := fun z =>
    match z.2.val with
    | 0 => (S z.1).left
    | 1 => (S z.1).right
    | 2 => (T z.1).left
    | _ => (T z.1).right
  let P : ObjectProperty C := ObjectProperty.ofObj endpoints
  let _ : ObjectProperty.Small.{w} P := inferInstance
  let _ : ObjectProperty.EssentiallySmall.{w} P := inferInstance
  obtain ⟨μ, hμ, hP⟩ := ObjectProperty.le_isCardinalPresentable P
  let _ : Fact μ.IsRegular := hμ
  let Upper := μ.ord.ToType ⊕ ((ℵ₀ : Cardinal.{w}).ord.ToType ⊕
    (Shrink.{w} I ⊕ fixed))
  obtain ⟨κ, hk, hUpper⟩ := HasCardinalLT.exists_regular_cardinal.{w} Upper
  let _ : Fact κ.IsRegular := ⟨hk⟩
  have hμκ : μ < κ := by
    have h := hUpper.of_injective (Sum.inl : μ.ord.ToType → Upper) Sum.inl_injective
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h
  have hω : (ℵ₀ : Cardinal.{w}) < κ := by
    have h := hUpper.of_injective
      (fun x : (ℵ₀ : Cardinal.{w}).ord.ToType => (Sum.inr (Sum.inl x) : Upper))
      (Sum.inr_injective.comp Sum.inl_injective)
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h
  have hIndex : HasCardinalLT (Shrink.{w} I) κ :=
    hUpper.of_injective (fun x => (Sum.inr (Sum.inr (Sum.inl x)) : Upper))
      (Sum.inr_injective.comp (Sum.inr_injective.comp Sum.inl_injective))
  have hFixed : HasCardinalLT fixed κ :=
    hUpper.of_injective (fun x => (Sum.inr (Sum.inr (Sum.inr x)) : Upper))
      (Sum.inr_injective.comp (Sum.inr_injective.comp Sum.inr_injective))
  have hEndpoint (i : I) (n : Fin 4) : IsCardinalPresentable (endpoints (i, n)) κ := by
    have h : IsCardinalPresentable (endpoints (i, n)) μ :=
      hP _ (ObjectProperty.ofObj_apply endpoints (i, n))
    let _ := h
    exact isCardinalPresentable_of_le (endpoints (i, n)) hμκ.le
  have hRanks (i : I) : IsCardinalPresentable (S i).left κ ∧
      IsCardinalPresentable (S i).right κ ∧ IsCardinalPresentable (T i).left κ ∧
        IsCardinalPresentable (T i).right κ := by
    exact ⟨hEndpoint i 0, hEndpoint i 1, hEndpoint i 2, hEndpoint i 3⟩
  have : Nonempty κ.ord.ToType := by simpa using hk.ne_zero
  let _ : OrderBot κ.ord.ToType := WellFoundedLT.toOrderBot κ.ord.ToType
  let M : MorphismProperty C := MorphismProperty.ofHoms (fun i => (T i).hom)
  let _ : M.IsSmall.{w} := inferInstance
  have hEligible : M.IsCardinalForSmallObjectArgument κ :=
    { isSmall := inferInstance
      locallySmall := inferInstance
      hasPushouts := inferInstance
      hasCoproducts := inferInstance
      hasIterationOfShape := inferInstance
      preservesColimit := by
        intro A B X Y f hf p c
        change MorphismProperty.ofHoms (fun i => (T i).hom) f at hf
        cases hf with
        | mk i =>
          let _ : IsCardinalPresentable (T i).left κ := (hRanks i).2.2.1
          let _ : PreservesColimitsOfShape κ.ord.ToType
              (coyoneda.obj (op (T i).left)) :=
            preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySmall
              (T i).left κ κ.ord.ToType
          infer_instance }
  let _ := hEligible
  have hSOA : M.HasSmallObjectArgument.{w} := ⟨κ, inferInstance, inferInstance, hEligible⟩
  exact ⟨T, r, κ, inferInstance, inferInstance, hω, hIndex, hFixed,
    hResolution, hRanks, inferInstance, hEligible, hSOA,
    ⟨SmallObject.functorialFactorizationData M κ⟩⟩

end HomotopicalAlgebra
