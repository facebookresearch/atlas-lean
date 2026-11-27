/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.PresheafAttachmentNormalForm

/-! # Consumers of original presheaf attachment labels and maps -/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u w s
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.SmallObject.PresheafAttachmentTest
variable {D : Type w} [SmallCategory D] {I : Type s} [Small.{max u w} I]
    {A B : I → Dᵒᵖ ⥤ Type (max u w)} (j : ∀ i, A i ⟶ B i)

/-- Both top and bottom maps of the original square remain. -/
theorem original_cell_both_equations {X Y : Dᵒᵖ ⥤ Type (max u w)}
    (p : X ⟶ Y) (q : FunctorObjIndex j p) :
    j q.i ≫ Sigma.ι (functorObjTgtFamily j p) q ≫ ρFunctorObj j p = q.t ≫ ιFunctorObj j p ∧
    (Sigma.ι (functorObjTgtFamily j p) q ≫ ρFunctorObj j p) ≫ πFunctorObj j p = q.b :=
  ⟨presheafAttachmentEquiv_cell_boundary j p q,
    presheafAttachmentEquiv_cell_projection j p q⟩

/-- Every point is originally old or comes from a full labelled complement. -/
theorem original_old_or_new {X Y : Dᵒᵖ ⥤ Type (max u w)}
    (p : X ⟶ Y) (d : Dᵒᵖ) [∀ i, Mono (j i)] (x : (functorObj j p).obj d) :
    (∃ y : X.obj d, (ιFunctorObj j p).app d y = x) ∨
    (∃ q : FunctorObjIndex j p, ∃ z : (B q.i).obj d,
      z ∉ Set.range ((j q.i).app d) ∧
      (Sigma.ι (functorObjTgtFamily j p) q ≫ ρFunctorObj j p).app d z = x) := by
  obtain ⟨z, hz⟩ := (presheafAttachmentEquiv j p d).surjective x
  rcases z with y | ⟨q, z, hnew⟩
  · exact Or.inl ⟨y, hz⟩
  · exact Or.inr ⟨q, z, hnew, hz⟩

/-- Empty objectwise complements leave the actual old-point unit bijective. -/
theorem empty_complements_give_original_unit_bijection {X Y : Dᵒᵖ ⥤ Type (max u w)}
    (p : X ⟶ Y) (d : Dᵒᵖ) [∀ i, Mono (j i)]
    (hSurj : ∀ i, Function.Surjective ((j i).app d)) :
    Function.Bijective ((ιFunctorObj j p).app d) := by
  constructor
  · intro x y hxy
    have h : (Sum.inl x : X.obj d ⊕ Σ q : FunctorObjIndex j p,
        {z : (B q.i).obj d // z ∉ Set.range ((j q.i).app d)}) = Sum.inl y :=
      (presheafAttachmentEquiv j p d).injective hxy
    exact Sum.inl.inj h
  · intro x
    obtain ⟨z, hz⟩ := (presheafAttachmentEquiv j p d).surjective x
    rcases z with y | ⟨q, z, hnew⟩
    · exact ⟨y, hz⟩
    · obtain ⟨a, ha⟩ := hSurj q.i z
      exact False.elim (hnew ⟨a, ha⟩)

/-- The original right-factor and right Arrow-map equations remain. -/
theorem original_right_factor_and_arrow_map {X Y X' Y' : Dᵒᵖ ⥤ Type (max u w)}
    (p : X ⟶ Y) (p' : X' ⟶ Y') (τ : Arrow.mk p ⟶ Arrow.mk p') :
    ιFunctorObj j p ≫ πFunctorObj j p = p ∧
    functorMap j τ ≫ πFunctorObj j p' = πFunctorObj j p ≫ τ.right :=
  ⟨ιFunctorObj_πFunctorObj j p, functorMap_π j τ⟩


/-- The whole original label transports both top and bottom maps. -/
theorem original_square_label_naturality {X Y X' Y' : Dᵒᵖ ⥤ Type (max u w)}
    {p : X ⟶ Y} {p' : X' ⟶ Y'} (τ : Arrow.mk p ⟶ Arrow.mk p')
    (d : Dᵒᵖ) [∀ i, Mono (j i)] (q : FunctorObjIndex j p)
    (z : (B q.i).obj d) (hz : z ∉ Set.range ((j q.i).app d)) :
    (functorMap j τ).app d
      (presheafAttachmentEquiv j p d (Sum.inr ⟨q, z, hz⟩)) =
    presheafAttachmentEquiv j p' d
      (Sum.inr ⟨FunctorObjIndex.mk q.i (q.t ≫ τ.left) (q.b ≫ τ.right)
        (by
          have hτ : τ.left ≫ p' = p ≫ τ.right := by simpa only [Arrow.mk_hom] using τ.w
          rw [Category.assoc, hτ, ← Category.assoc, q.w, Category.assoc]), z, hz⟩) :=
  presheafAttachmentEquiv_naturality j τ d (Sum.inr ⟨q, z, hz⟩)

end CategoryTheory.SmallObject.PresheafAttachmentTest
