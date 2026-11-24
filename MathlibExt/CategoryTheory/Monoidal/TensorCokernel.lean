/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Monoidal.Limits.Cokernels

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory MonoidalPreadditive

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [MonoidalCategory C] [MonoidalPreadditive C]

namespace CokernelCofork

variable {X₁ Y₁ X₂ Y₂ : C} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂}
  (c₁ : CokernelCofork f₁) (hc₁ : IsColimit c₁)
  (c₂ : CokernelCofork f₂) (hc₂ : IsColimit c₂)
  [PreservesColimit (parallelPair f₂ 0) (tensorLeft c₁.pt)]
  [PreservesColimit (parallelPair f₁ 0) (tensorRight Y₂)]

include hc₁ hc₂ in
/-- Morphisms out of the tensor product of two chosen cokernel presentations
are determined after precomposition by the tensor of their projections.
This requires only preservation of the two cokernels being projected. -/
lemma tensor_hom_ext {Z : C} {g h : c₁.pt ⊗ c₂.pt ⟶ Z}
    (w : (c₁.π ⊗ₘ c₂.π) ≫ g = (c₁.π ⊗ₘ c₂.π) ≫ h) : g = h := by
  apply CokernelCofork.isColimitMapBifunctor.hom_ext hc₁ hc₂ (curriedTensor C)
  change c₁.π ▷ Y₂ ≫ c₁.pt ◁ c₂.π ≫ g =
    c₁.π ▷ Y₂ ≫ c₁.pt ◁ c₂.π ≫ h
  simpa only [tensorHom_def, Category.assoc] using w

include hc₁ hc₂ in
/-- The tensor product of the projections in two chosen cokernel
presentations is an epimorphism. No coproduct presentation is needed. -/
lemma epi_tensor_π : Epi (c₁.π ⊗ₘ c₂.π) := by
  constructor
  intro Z g h w
  exact tensor_hom_ext c₁ hc₁ c₂ hc₂ w

variable [HasBinaryCoproduct (X₁ ⊗ Y₂) (Y₁ ⊗ X₂)]
  [PreservesColimit (parallelPair f₁ 0) (tensorRight X₂)]

/-- Descend a morphism through the tensor product of two chosen cokernel
presentations. Unlike `tensorCokernelDesc`, the quotient objects and
projections need not be the category's selected cokernels. -/
noncomputable def tensorDesc {Z : C} (k : Y₁ ⊗ Y₂ ⟶ Z)
    (hk : coprod.desc (f₁ ▷ Y₂) (Y₁ ◁ f₂) ≫ k = 0) :
    c₁.pt ⊗ c₂.pt ⟶ Z :=
  (CokernelCofork.isColimitTensor hc₁ hc₂).desc
    (CokernelCofork.ofπ k hk)

/-- The tensor of the two quotient projections followed by `tensorDesc` is
the morphism before descent. -/
@[reassoc (attr := simp)]
lemma tensor_π_desc {Z : C} (k : Y₁ ⊗ Y₂ ⟶ Z)
    (hk : coprod.desc (f₁ ▷ Y₂) (Y₁ ◁ f₂) ≫ k = 0) :
    (c₁.π ⊗ₘ c₂.π) ≫ tensorDesc c₁ hc₁ c₂ hc₂ k hk = k :=
  (CokernelCofork.isColimitTensor hc₁ hc₂).fac
    (CokernelCofork.ofπ k hk) WalkingParallelPair.one

/-- A morphism with a prescribed composite with the tensor quotient
projection is the corresponding `tensorDesc`. -/
lemma tensorDesc_unique {Z : C} (k : Y₁ ⊗ Y₂ ⟶ Z)
    (hk : coprod.desc (f₁ ▷ Y₂) (Y₁ ◁ f₂) ≫ k = 0)
    (d : c₁.pt ⊗ c₂.pt ⟶ Z)
    (hd : (c₁.π ⊗ₘ c₂.π) ≫ d = k) :
    d = tensorDesc c₁ hc₁ c₂ hc₂ k hk := by
  apply tensor_hom_ext c₁ hc₁ c₂ hc₂
  rw [hd, tensor_π_desc]

/-- Tensor descent commutes with postcomposition. -/
@[reassoc]
lemma tensorDesc_comp {Z Z' : C} (k : Y₁ ⊗ Y₂ ⟶ Z)
    (hk : coprod.desc (f₁ ▷ Y₂) (Y₁ ◁ f₂) ≫ k = 0)
    (z : Z ⟶ Z') :
    tensorDesc c₁ hc₁ c₂ hc₂ k hk ≫ z =
      tensorDesc c₁ hc₁ c₂ hc₂ (k ≫ z) (by
        rw [← Category.assoc, hk, zero_comp]) := by
  apply tensor_hom_ext c₁ hc₁ c₂ hc₂
  rw [← Category.assoc, tensor_π_desc, tensor_π_desc]

/-- Naturality of tensor descent with respect to maps of both quotient
presentations and a map of targets. -/
lemma tensorDesc_naturality
    {X₁' Y₁' X₂' Y₂' Z Z' : C}
    {f₁' : X₁' ⟶ Y₁'} {f₂' : X₂' ⟶ Y₂'}
    (c₁' : CokernelCofork f₁') (hc₁' : IsColimit c₁')
    (c₂' : CokernelCofork f₂') (hc₂' : IsColimit c₂')
    [HasBinaryCoproduct (X₁' ⊗ Y₂') (Y₁' ⊗ X₂')]
    [PreservesColimit (parallelPair f₂' 0) (tensorLeft c₁'.pt)]
    [PreservesColimit (parallelPair f₁' 0) (tensorRight Y₂')]
    [PreservesColimit (parallelPair f₁' 0) (tensorRight X₂')]
    (a₁ : Y₁ ⟶ Y₁') (a₂ : Y₂ ⟶ Y₂')
    (q₁ : c₁.pt ⟶ c₁'.pt) (q₂ : c₂.pt ⟶ c₂'.pt)
    (hq₁ : c₁.π ≫ q₁ = a₁ ≫ c₁'.π)
    (hq₂ : c₂.π ≫ q₂ = a₂ ≫ c₂'.π)
    (k : Y₁ ⊗ Y₂ ⟶ Z)
    (hk : coprod.desc (f₁ ▷ Y₂) (Y₁ ◁ f₂) ≫ k = 0)
    (k' : Y₁' ⊗ Y₂' ⟶ Z')
    (hk' : coprod.desc (f₁' ▷ Y₂') (Y₁' ◁ f₂') ≫ k' = 0)
    (z : Z ⟶ Z') (hz : (a₁ ⊗ₘ a₂) ≫ k' = k ≫ z) :
    (q₁ ⊗ₘ q₂) ≫ tensorDesc c₁' hc₁' c₂' hc₂' k' hk' =
      tensorDesc c₁ hc₁ c₂ hc₂ k hk ≫ z := by
  apply tensor_hom_ext c₁ hc₁ c₂ hc₂
  calc
    (c₁.π ⊗ₘ c₂.π) ≫
          ((q₁ ⊗ₘ q₂) ≫ tensorDesc c₁' hc₁' c₂' hc₂' k' hk') =
        ((c₁.π ≫ q₁) ⊗ₘ (c₂.π ≫ q₂)) ≫
          tensorDesc c₁' hc₁' c₂' hc₂' k' hk' := by
            rw [← Category.assoc,
              MonoidalCategory.tensorHom_comp_tensorHom]
    _ = ((a₁ ≫ c₁'.π) ⊗ₘ (a₂ ≫ c₂'.π)) ≫
          tensorDesc c₁' hc₁' c₂' hc₂' k' hk' := by
            rw [hq₁, hq₂]
    _ = (a₁ ⊗ₘ a₂) ≫ k' := by
      rw [← MonoidalCategory.tensorHom_comp_tensorHom_assoc,
        tensor_π_desc]
    _ = k ≫ z := hz
    _ = (c₁.π ⊗ₘ c₂.π) ≫
        (tensorDesc c₁ hc₁ c₂ hc₂ k hk ≫ z) := by
      rw [← Category.assoc, tensor_π_desc]

/-- The tensor product of two chosen cokernel presentations is canonically
isomorphic to any chosen cokernel presentation of the combined tensor
relation. -/
noncomputable def tensorIso
    (c : CokernelCofork (coprod.desc (f₁ ▷ Y₂) (Y₁ ◁ f₂)))
    (hc : IsColimit c) : c₁.pt ⊗ c₂.pt ≅ c.pt :=
  IsColimit.coconePointUniqueUpToIso
    (CokernelCofork.isColimitTensor hc₁ hc₂) hc

/-- The hom of `tensorIso` carries the tensor quotient projection to the
target cokernel projection. -/
@[reassoc (attr := simp)]
lemma tensor_π_comp_tensorIso_hom
    (c : CokernelCofork (coprod.desc (f₁ ▷ Y₂) (Y₁ ◁ f₂)))
    (hc : IsColimit c) :
    (c₁.π ⊗ₘ c₂.π) ≫ (tensorIso c₁ hc₁ c₂ hc₂ c hc).hom = c.π :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (CokernelCofork.isColimitTensor hc₁ hc₂) hc WalkingParallelPair.one

/-- The inverse of `tensorIso` carries the target cokernel projection back to
the tensor quotient projection. -/
@[reassoc (attr := simp)]
lemma π_comp_tensorIso_inv
    (c : CokernelCofork (coprod.desc (f₁ ▷ Y₂) (Y₁ ◁ f₂)))
    (hc : IsColimit c) :
    c.π ≫ (tensorIso c₁ hc₁ c₂ hc₂ c hc).inv = c₁.π ⊗ₘ c₂.π := by
  rw [← tensor_π_comp_tensorIso_hom c₁ hc₁ c₂ hc₂ c hc,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

end CokernelCofork

variable
  {X₁ Y₁ X₂ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
  [HasCokernel f₁] [HasCokernel f₂]
  [HasBinaryCoproduct (X₁ ⊗ Y₂) (Y₁ ⊗ X₂)]
  [PreservesColimit (parallelPair f₂ 0) (tensorLeft (cokernel f₁))]
  [PreservesColimit (parallelPair f₁ 0) (tensorRight Y₂)]
  [PreservesColimit (parallelPair f₁ 0) (tensorRight X₂)]

/-- Descend a morphism from `Y₁ ⊗ Y₂` through the tensor product of the cokernels
of `f₁` and `f₂`. -/
noncomputable def tensorCokernelDesc {Z : C} (k : Y₁ ⊗ Y₂ ⟶ Z)
    (hk : coprod.desc (f₁ ▷ Y₂) (Y₁ ◁ f₂) ≫ k = 0) :
    cokernel f₁ ⊗ cokernel f₂ ⟶ Z := by
  let c₁ : CokernelCofork f₁ :=
    CokernelCofork.ofπ (cokernel.π f₁) (cokernel.condition f₁)
  let c₂ : CokernelCofork f₂ :=
    CokernelCofork.ofπ (cokernel.π f₂) (cokernel.condition f₂)
  let _ : PreservesColimit (parallelPair f₂ 0) (tensorLeft c₁.pt) := by
    dsimp [c₁]
    infer_instance
  exact CokernelCofork.tensorDesc c₁ (cokernelIsCokernel f₁)
    c₂ (cokernelIsCokernel f₂) k hk

@[reassoc (attr := simp)]
lemma tensor_cokernel_π_comp_tensorCokernelDesc {Z : C} (k : Y₁ ⊗ Y₂ ⟶ Z)
    (hk : coprod.desc (f₁ ▷ Y₂) (Y₁ ◁ f₂) ≫ k = 0) :
    (cokernel.π f₁ ⊗ₘ cokernel.π f₂) ≫ tensorCokernelDesc f₁ f₂ k hk = k := by
  let c₁ : CokernelCofork f₁ :=
    CokernelCofork.ofπ (cokernel.π f₁) (cokernel.condition f₁)
  let c₂ : CokernelCofork f₂ :=
    CokernelCofork.ofπ (cokernel.π f₂) (cokernel.condition f₂)
  let _ : PreservesColimit (parallelPair f₂ 0) (tensorLeft c₁.pt) := by
    dsimp [c₁]
    infer_instance
  exact CokernelCofork.tensor_π_desc c₁ (cokernelIsCokernel f₁)
    c₂ (cokernelIsCokernel f₂) k hk

omit [HasBinaryCoproduct (X₁ ⊗ Y₂) (Y₁ ⊗ X₂)]
  [PreservesColimit (parallelPair f₁ 0) (tensorRight X₂)] in
/-- The tensor product of the two selected cokernel projections is an
epimorphism. -/
lemma epi_tensor_cokernel_π : Epi (cokernel.π f₁ ⊗ₘ cokernel.π f₂) := by
  let c₁ : CokernelCofork f₁ :=
    CokernelCofork.ofπ (cokernel.π f₁) (cokernel.condition f₁)
  let c₂ : CokernelCofork f₂ :=
    CokernelCofork.ofπ (cokernel.π f₂) (cokernel.condition f₂)
  let _ : PreservesColimit (parallelPair f₂ 0) (tensorLeft c₁.pt) := by
    dsimp [c₁]
    infer_instance
  exact CokernelCofork.epi_tensor_π c₁ (cokernelIsCokernel f₁)
    c₂ (cokernelIsCokernel f₂)

/-- A morphism out of the tensor product of two cokernels is determined by its composite
with the tensor product of the cokernel projections. -/
lemma tensorCokernelDesc_unique {Z : C} (k : Y₁ ⊗ Y₂ ⟶ Z)
    (hk : coprod.desc (f₁ ▷ Y₂) (Y₁ ◁ f₂) ≫ k = 0)
    (d : cokernel f₁ ⊗ cokernel f₂ ⟶ Z)
    (hd : (cokernel.π f₁ ⊗ₘ cokernel.π f₂) ≫ d = k) :
    d = tensorCokernelDesc f₁ f₂ k hk := by
  let c₁ : CokernelCofork f₁ :=
    CokernelCofork.ofπ (cokernel.π f₁) (cokernel.condition f₁)
  let c₂ : CokernelCofork f₂ :=
    CokernelCofork.ofπ (cokernel.π f₂) (cokernel.condition f₂)
  let _ : PreservesColimit (parallelPair f₂ 0) (tensorLeft c₁.pt) := by
    dsimp [c₁]
    infer_instance
  exact CokernelCofork.tensorDesc_unique c₁ (cokernelIsCokernel f₁)
    c₂ (cokernelIsCokernel f₂) k hk d hd

/-- Naturality of descent through the tensor product of the selected
cokernels. The quotient maps are characterized only by their composites with
the cokernel projections. -/
lemma tensorCokernelDesc_naturality
    {X₁' Y₁' X₂' Y₂' Z Z' : C}
    {f₁' : X₁' ⟶ Y₁'} {f₂' : X₂' ⟶ Y₂'}
    [HasCokernel f₁'] [HasCokernel f₂']
    [HasBinaryCoproduct (X₁' ⊗ Y₂') (Y₁' ⊗ X₂')]
    [PreservesColimit (parallelPair f₂' 0) (tensorLeft (cokernel f₁'))]
    [PreservesColimit (parallelPair f₁' 0) (tensorRight Y₂')]
    [PreservesColimit (parallelPair f₁' 0) (tensorRight X₂')]
    (a₁ : Y₁ ⟶ Y₁') (a₂ : Y₂ ⟶ Y₂')
    (q₁ : cokernel f₁ ⟶ cokernel f₁')
    (q₂ : cokernel f₂ ⟶ cokernel f₂')
    (hq₁ : cokernel.π f₁ ≫ q₁ = a₁ ≫ cokernel.π f₁')
    (hq₂ : cokernel.π f₂ ≫ q₂ = a₂ ≫ cokernel.π f₂')
    (k : Y₁ ⊗ Y₂ ⟶ Z)
    (hk : coprod.desc (f₁ ▷ Y₂) (Y₁ ◁ f₂) ≫ k = 0)
    (k' : Y₁' ⊗ Y₂' ⟶ Z')
    (hk' : coprod.desc (f₁' ▷ Y₂') (Y₁' ◁ f₂') ≫ k' = 0)
    (z : Z ⟶ Z') (hz : (a₁ ⊗ₘ a₂) ≫ k' = k ≫ z) :
    (q₁ ⊗ₘ q₂) ≫ tensorCokernelDesc f₁' f₂' k' hk' =
      tensorCokernelDesc f₁ f₂ k hk ≫ z := by
  let c₁ : CokernelCofork f₁ :=
    CokernelCofork.ofπ (cokernel.π f₁) (cokernel.condition f₁)
  let c₂ : CokernelCofork f₂ :=
    CokernelCofork.ofπ (cokernel.π f₂) (cokernel.condition f₂)
  let c₁' : CokernelCofork f₁' :=
    CokernelCofork.ofπ (cokernel.π f₁') (cokernel.condition f₁')
  let c₂' : CokernelCofork f₂' :=
    CokernelCofork.ofπ (cokernel.π f₂') (cokernel.condition f₂')
  let _ : PreservesColimit (parallelPair f₂ 0) (tensorLeft c₁.pt) := by
    dsimp [c₁]
    infer_instance
  let _ : PreservesColimit (parallelPair f₂' 0) (tensorLeft c₁'.pt) := by
    dsimp [c₁']
    infer_instance
  exact CokernelCofork.tensorDesc_naturality
    c₁ (cokernelIsCokernel f₁) c₂ (cokernelIsCokernel f₂)
    c₁' (cokernelIsCokernel f₁') c₂' (cokernelIsCokernel f₂')
    a₁ a₂ q₁ q₂ hq₁ hq₂ k hk k' hk' z hz

variable [HasCokernel (coprod.desc (f₁ ▷ Y₂) (Y₁ ◁ f₂))]

/-- The tensor product of two cokernels is canonically the cokernel of the sum of
the two tensor relations. -/
noncomputable def tensorCokernelIso :
    cokernel f₁ ⊗ cokernel f₂ ≅
      cokernel (coprod.desc (f₁ ▷ Y₂) (Y₁ ◁ f₂)) := by
  let c₁ : CokernelCofork f₁ :=
    CokernelCofork.ofπ (cokernel.π f₁) (cokernel.condition f₁)
  let c₂ : CokernelCofork f₂ :=
    CokernelCofork.ofπ (cokernel.π f₂) (cokernel.condition f₂)
  let c : CokernelCofork (coprod.desc (f₁ ▷ Y₂) (Y₁ ◁ f₂)) :=
    CokernelCofork.ofπ
      (cokernel.π (coprod.desc (f₁ ▷ Y₂) (Y₁ ◁ f₂)))
      (cokernel.condition _)
  let _ : PreservesColimit (parallelPair f₂ 0) (tensorLeft c₁.pt) := by
    dsimp [c₁]
    infer_instance
  exact CokernelCofork.tensorIso c₁ (cokernelIsCokernel f₁)
    c₂ (cokernelIsCokernel f₂) c (cokernelIsCokernel _)

@[reassoc (attr := simp)]
lemma tensor_cokernel_π_comp_tensorCokernelIso_hom :
    (cokernel.π f₁ ⊗ₘ cokernel.π f₂) ≫ (tensorCokernelIso f₁ f₂).hom =
      cokernel.π (coprod.desc (f₁ ▷ Y₂) (Y₁ ◁ f₂)) := by
  let c₁ : CokernelCofork f₁ :=
    CokernelCofork.ofπ (cokernel.π f₁) (cokernel.condition f₁)
  let c₂ : CokernelCofork f₂ :=
    CokernelCofork.ofπ (cokernel.π f₂) (cokernel.condition f₂)
  let c : CokernelCofork (coprod.desc (f₁ ▷ Y₂) (Y₁ ◁ f₂)) :=
    CokernelCofork.ofπ
      (cokernel.π (coprod.desc (f₁ ▷ Y₂) (Y₁ ◁ f₂)))
      (cokernel.condition _)
  let _ : PreservesColimit (parallelPair f₂ 0) (tensorLeft c₁.pt) := by
    dsimp [c₁]
    infer_instance
  exact CokernelCofork.tensor_π_comp_tensorIso_hom
    c₁ (cokernelIsCokernel f₁) c₂ (cokernelIsCokernel f₂)
    c (cokernelIsCokernel _)

end CategoryTheory.Limits
