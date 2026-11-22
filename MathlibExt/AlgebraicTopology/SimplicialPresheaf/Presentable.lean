/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.Basic
import MathlibExt.AlgebraicTopology.SimplicialSet.Presentable
import Mathlib.CategoryTheory.ObjectProperty.Small
import Mathlib.CategoryTheory.Presentable.StrongGenerator
import Mathlib.SetTheory.Cardinal.HasCardinalLT

/-!
# Same-universe local presentability of simplicial presheaves

The original presheaf category is transported to the native small model of its site before
applying presheaf presentability. The coefficient universe stays fixed. For each small original
Arrow family, one larger regular cardinal bounds both endpoints and any supplied small profile,
while preserving local presentability at that same cardinal.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v w z s

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

namespace SimplicialPresheaf

variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]

/-- The literal original simplicial-presheaf category is locally presentable in its fixed
value universe, using the actual small-model transport of both site objects and Hom types. -/
theorem isLocallyPresentable : IsLocallyPresentable.{u} (SimplicialPresheaf.{u} D) := by
  let _ : IsLocallyPresentable.{u} SSet.{u} := SSet.isLocallyPresentable
  let _ : IsLocallyPresentable.{u} (SimplicialPresheaf.{u} (SmallModel.{u} D)) :=
    inferInstance
  exact (smallModelTransport (D := D)).symm.isLocallyPresentable

/-- A supplied small family has one larger regular cardinal for local presentability, both
original endpoints and the supplied small profile, above any prescribed lower bound. -/
theorem exists_regular_cardinal_for_family {ι : Type z} [Small.{u} ι]
    (F : ι → Arrow (SimplicialPresheaf.{u} D)) (lower : Cardinal.{u})
    (fixed : Type s) [Small.{u} fixed] :
    ∃ (κ : Cardinal.{u}) (hκ : Fact κ.IsRegular),
      letI : Fact κ.IsRegular := hκ
      lower < κ ∧ ℵ₀ < κ ∧ HasCardinalLT ι κ ∧ HasCardinalLT fixed κ ∧
        IsCardinalLocallyPresentable (SimplicialPresheaf.{u} D) κ ∧
        ∀ i : ι, IsCardinalPresentable (F i).left κ ∧
          IsCardinalPresentable (F i).right κ := by
  let _ : IsLocallyPresentable.{u} (SimplicialPresheaf.{u} D) := isLocallyPresentable
  obtain ⟨ν, hν, hLP⟩ := IsLocallyPresentable.exists_cardinal.{u} (SimplicialPresheaf.{u} D)
  let _ : Fact ν.IsRegular := hν
  let _ : IsCardinalLocallyPresentable (SimplicialPresheaf.{u} D) ν := hLP
  let endpoints : ι ⊕ ι → SimplicialPresheaf.{u} D :=
    Sum.elim (fun i => (F i).left) (fun i => (F i).right)
  let P : ObjectProperty (SimplicialPresheaf.{u} D) := ObjectProperty.ofObj endpoints
  let _ : ObjectProperty.Small.{u} P := inferInstance
  let _ : ObjectProperty.EssentiallySmall.{u} P := inferInstance
  obtain ⟨μ, hμ, hP⟩ := ObjectProperty.le_isCardinalPresentable P
  let _ : Fact μ.IsRegular := hμ
  let Upper := (lower.ord.ToType ⊕ ν.ord.ToType) ⊕
    (μ.ord.ToType ⊕ ((ℵ₀ : Cardinal.{u}).ord.ToType ⊕ (ι ⊕ fixed)))
  obtain ⟨κ, hκ, hUpper⟩ := HasCardinalLT.exists_regular_cardinal.{u} Upper
  let _ : Fact κ.IsRegular := ⟨hκ⟩
  have hlower : lower < κ := by
    have h := hUpper.of_injective
      (fun x : lower.ord.ToType => (Sum.inl (Sum.inl x) : Upper))
      (Sum.inl_injective.comp Sum.inl_injective)
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h
  have hνκ : ν < κ := by
    have h := hUpper.of_injective
      (fun x : ν.ord.ToType => (Sum.inl (Sum.inr x) : Upper))
      (Sum.inl_injective.comp Sum.inr_injective)
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h
  have hμκ : μ < κ := by
    have h := hUpper.of_injective
      (fun x : μ.ord.ToType => (Sum.inr (Sum.inl x) : Upper))
      (Sum.inr_injective.comp Sum.inl_injective)
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h
  have hω : (ℵ₀ : Cardinal.{u}) < κ := by
    have h := hUpper.of_injective
      (fun x : (ℵ₀ : Cardinal.{u}).ord.ToType => (Sum.inr (Sum.inr (Sum.inl x)) : Upper))
      (Sum.inr_injective.comp (Sum.inr_injective.comp Sum.inl_injective))
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h
  have hlabels : HasCardinalLT ι κ :=
    hUpper.of_injective (fun x : ι => (Sum.inr (Sum.inr (Sum.inr (Sum.inl x))) : Upper))
      (Sum.inr_injective.comp
        (Sum.inr_injective.comp (Sum.inr_injective.comp Sum.inl_injective)))
  have hfixed : HasCardinalLT fixed κ :=
    hUpper.of_injective (fun x : fixed => (Sum.inr (Sum.inr (Sum.inr (Sum.inr x))) : Upper))
      (Sum.inr_injective.comp
        (Sum.inr_injective.comp (Sum.inr_injective.comp Sum.inr_injective)))
  have hLPκ : IsCardinalLocallyPresentable (SimplicialPresheaf.{u} D) κ :=
    IsCardinalLocallyPresentable.of_le (SimplicialPresheaf.{u} D) hνκ.le
  have h (i : ι ⊕ ι) : IsCardinalPresentable (endpoints i) κ := by
    let _ : IsCardinalPresentable (endpoints i) μ :=
      hP _ (ObjectProperty.ofObj_apply endpoints i)
    exact isCardinalPresentable_of_le (endpoints i) hμκ.le
  exact ⟨κ, inferInstance, hlower, hω, hlabels, hfixed, hLPκ,
    fun i => ⟨h (.inl i), h (.inr i)⟩⟩

end SimplicialPresheaf
