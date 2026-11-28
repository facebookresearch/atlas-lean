/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Monoidal.Limits.Cokernels

/-!
# Tensor cokernel descent and naturality

For two cokernel presentations in a monoidal preadditive category, their tensor projections
jointly determine a map from the tensor of the cokernels. This uniqueness requires preservation
of two specified cokernels. The native tensor-cokernel colimit additionally uses the relation
coproduct and a third preservation hypothesis. Its standard colimit descents are natural in the
presentations and the target. The chosen-cokernel conveniences below use that same colimit.
-/

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
/-- Let `C` be preadditive monoidal with tensor product additive in both
variables. For cokernel presentations `π₁ : Y₁ → C₁` of `f₁`,
`π₂ : Y₂ → C₂` of `f₂`, assume `C₁ ⊗ -` preserves this
cokernel of `f₂` and `- ⊗ Y₂` preserves this cokernel of `f₁`. Two maps
`C₁ ⊗ C₂ → Z` are equal if their composites with `π₁ ⊗ π₂`
are equal. -/
lemma tensor_hom_ext {Z : C} {g h : c₁.pt ⊗ c₂.pt ⟶ Z}
    (w : (c₁.π ⊗ₘ c₂.π) ≫ g = (c₁.π ⊗ₘ c₂.π) ≫ h) : g = h := by
  apply CokernelCofork.isColimitMapBifunctor.hom_ext hc₁ hc₂ (curriedTensor C)
  change c₁.π ▷ Y₂ ≫ c₁.pt ◁ c₂.π ≫ g =
    c₁.π ▷ Y₂ ≫ c₁.pt ◁ c₂.π ≫ h
  simpa only [tensorHom_def, Category.assoc] using w

include hc₁ hc₂ in
/-- Let `C` be preadditive monoidal with tensor product additive in both
variables. For cokernel presentations `π₁ : Y₁ → C₁` of `f₁`,
`π₂ : Y₂ → C₂` of `f₂`, assume `C₁ ⊗ -` preserves this
cokernel of `f₂` and `- ⊗ Y₂` preserves this cokernel of `f₁`. The tensor
projection `π₁ ⊗ π₂ : Y₁ ⊗ Y₂ → C₁ ⊗ C₂` is an epimorphism. -/
lemma epi_tensor_π : Epi (c₁.π ⊗ₘ c₂.π) := by
  constructor
  intro Z g h w
  exact tensor_hom_ext c₁ hc₁ c₂ hc₂ w

variable [HasBinaryCoproduct (X₁ ⊗ Y₂) (Y₁ ⊗ X₂)]
  [PreservesColimit (parallelPair f₁ 0) (tensorRight X₂)]

private lemma tensor_fac {Z : C} (k : Y₁ ⊗ Y₂ ⟶ Z)
    (hk : coprod.desc (f₁ ▷ Y₂) (Y₁ ◁ f₂) ≫ k = 0) :
    (c₁.π ⊗ₘ c₂.π) ≫
      (CokernelCofork.isColimitTensor hc₁ hc₂).desc (CokernelCofork.ofπ k hk) = k :=
  (CokernelCofork.isColimitTensor hc₁ hc₂).fac
    (CokernelCofork.ofπ k hk) WalkingParallelPair.one

/-- Let `C` be preadditive monoidal with tensor product additive in both
variables. For cokernel presentations `π₁ : Y₁ → C₁` of `f₁`,
`π₂ : Y₂ → C₂` of `f₂`, assume `C₁ ⊗ -` preserves this
cokernel of `f₂` and `- ⊗ Y₂` preserves this cokernel of `f₁`. Also assume the relation coproduct
`(X₁ ⊗ Y₂) ⨿ (Y₁ ⊗ X₂)` exists and `- ⊗ X₂` preserves
the cokernel of `f₁`. Take a second pair of
cokernel presentations satisfying the same preservation conditions, and assume the primed
relation coproduct `(X₁′ ⊗ Y₂′) ⨿ (Y₁′ ⊗ X₂′)` also exists.
If `aᵢ : Yᵢ → Yᵢ′`, `qᵢ : Cᵢ → Cᵢ′` commute with the
quotient maps and `(a₁ ⊗ a₂) ≫ k′ = k ≫ z`, then
`(q₁ ⊗ q₂) ≫ d′ = d ≫ z`, where `d,d′` are the standard tensor-cofork colimit
descents of `k,k′`. -/
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
    (q₁ ⊗ₘ q₂) ≫ (CokernelCofork.isColimitTensor hc₁' hc₂').desc (CokernelCofork.ofπ k' hk') =
      (CokernelCofork.isColimitTensor hc₁ hc₂).desc (CokernelCofork.ofπ k hk) ≫ z := by
  apply tensor_hom_ext c₁ hc₁ c₂ hc₂
  calc
    (c₁.π ⊗ₘ c₂.π) ≫
          ((q₁ ⊗ₘ q₂) ≫ (CokernelCofork.isColimitTensor hc₁' hc₂').desc (CokernelCofork.ofπ k'
            hk')) =
        ((c₁.π ≫ q₁) ⊗ₘ (c₂.π ≫ q₂)) ≫
          (CokernelCofork.isColimitTensor hc₁' hc₂').desc (CokernelCofork.ofπ k' hk') := by
            rw [← Category.assoc,
              MonoidalCategory.tensorHom_comp_tensorHom]
    _ = ((a₁ ≫ c₁'.π) ⊗ₘ (a₂ ≫ c₂'.π)) ≫
          (CokernelCofork.isColimitTensor hc₁' hc₂').desc (CokernelCofork.ofπ k' hk') := by
            rw [hq₁, hq₂]
    _ = (a₁ ⊗ₘ a₂) ≫ k' := by
      rw [← MonoidalCategory.tensorHom_comp_tensorHom_assoc,
        tensor_fac]
    _ = k ≫ z := hz
    _ = (c₁.π ⊗ₘ c₂.π) ≫
        ((CokernelCofork.isColimitTensor hc₁ hc₂).desc (CokernelCofork.ofπ k hk) ≫ z) := by
      rw [← Category.assoc, tensor_fac]

end CokernelCofork

variable
  {X₁ Y₁ X₂ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
  [HasCokernel f₁] [HasCokernel f₂]
  [HasBinaryCoproduct (X₁ ⊗ Y₂) (Y₁ ⊗ X₂)]
  [PreservesColimit (parallelPair f₂ 0) (tensorLeft (cokernel f₁))]
  [PreservesColimit (parallelPair f₁ 0) (tensorRight Y₂)]
  [PreservesColimit (parallelPair f₁ 0) (tensorRight X₂)]

noncomputable def tensorCokernelIsColimit :
    IsColimit ((CokernelCofork.ofπ (cokernel.π f₁) (cokernel.condition f₁)).tensor
      (CokernelCofork.ofπ (cokernel.π f₂) (cokernel.condition f₂))) := by
  let _ : PreservesColimit (parallelPair f₂ 0)
      (tensorLeft
        (CokernelCofork.ofπ (cokernel.π f₁) (cokernel.condition f₁)).pt) := by
    change PreservesColimit (parallelPair f₂ 0) (tensorLeft (cokernel f₁))
    infer_instance
  exact CokernelCofork.isColimitTensor (cokernelIsCokernel f₁) (cokernelIsCokernel f₂)

/- Let `C` be preadditive monoidal with tensor additive in both variables,
and let `f₁ : X₁ → Y₁`, `f₂ : X₂ → Y₂` have cokernels.
Assume `(X₁ ⊗ Y₂) ⨿ (Y₁ ⊗ X₂)` exists,
`cokernel(f₁) ⊗ -` preserves the cokernel of `f₂`, and
`- ⊗ Y₂`, `- ⊗ X₂` preserve the cokernel of `f₁`. Every map
`k : Y₁ ⊗ Y₂ → Z` that kills the sum of the two tensor relations
descends to `cokernel f₁ ⊗ cokernel f₂ → Z`. -/
noncomputable def tensorCokernelDesc {Z : C} (k : Y₁ ⊗ Y₂ ⟶ Z)
    (hk : coprod.desc (f₁ ▷ Y₂) (Y₁ ◁ f₂) ≫ k = 0) :
    cokernel f₁ ⊗ cokernel f₂ ⟶ Z :=
  (tensorCokernelIsColimit f₁ f₂).desc (CokernelCofork.ofπ k hk)

@[reassoc (attr := simp)]
lemma tensor_cokernel_π_comp_tensorCokernelDesc {Z : C} (k : Y₁ ⊗ Y₂ ⟶ Z)
    (hk : coprod.desc (f₁ ▷ Y₂) (Y₁ ◁ f₂) ≫ k = 0) :
    (cokernel.π f₁ ⊗ₘ cokernel.π f₂) ≫ tensorCokernelDesc f₁ f₂ k hk = k := by
  simpa only [tensorCokernelDesc, CokernelCofork.tensor, CokernelCofork.π_ofπ] using
    Cofork.IsColimit.π_desc (tensorCokernelIsColimit f₁ f₂) (CokernelCofork.ofπ k hk)

omit [HasBinaryCoproduct (X₁ ⊗ Y₂) (Y₁ ⊗ X₂)]
  [PreservesColimit (parallelPair f₁ 0) (tensorRight X₂)] in
/-- Let `C` be preadditive monoidal with tensor additive in both variables,
and let `f₁ : X₁ → Y₁`, `f₂ : X₂ → Y₂` have cokernels.
Assume `cokernel(f₁) ⊗ -` preserves the cokernel of `f₂`, and
`- ⊗ Y₂` preserves the cokernel of `f₁`. The tensor
`cokernel.π f₁ ⊗ cokernel.π f₂` of the quotient maps is an epimorphism. -/
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

/- Let `C` be preadditive monoidal with tensor additive in both variables,
and let `f₁ : X₁ → Y₁`, `f₂ : X₂ → Y₂` have cokernels.
Assume `(X₁ ⊗ Y₂) ⨿ (Y₁ ⊗ X₂)` exists,
`cokernel(f₁) ⊗ -` preserves the cokernel of `f₂`, and
`- ⊗ Y₂`, `- ⊗ X₂` preserve the cokernel of `f₁`. A map from
`cokernel f₁ ⊗ cokernel f₂` with prescribed composite `k` under
the two quotient maps is the canonical descent of `k`. -/
lemma tensorCokernelDesc_unique {Z : C} (k : Y₁ ⊗ Y₂ ⟶ Z)
    (hk : coprod.desc (f₁ ▷ Y₂) (Y₁ ◁ f₂) ≫ k = 0)
    (d : cokernel f₁ ⊗ cokernel f₂ ⟶ Z)
    (hd : (cokernel.π f₁ ⊗ₘ cokernel.π f₂) ≫ d = k) :
    d = tensorCokernelDesc f₁ f₂ k hk := by
  let _ := epi_tensor_cokernel_π f₁ f₂
  apply (cancel_epi (cokernel.π f₁ ⊗ₘ cokernel.π f₂)).1
  rw [hd, tensor_cokernel_π_comp_tensorCokernelDesc]

/- Let `C` be preadditive monoidal with tensor additive in both variables,
and let `f₁ : X₁ → Y₁`, `f₂ : X₂ → Y₂` have cokernels.
Assume `(X₁ ⊗ Y₂) ⨿ (Y₁ ⊗ X₂)` exists,
`cokernel(f₁) ⊗ -` preserves the cokernel of `f₂`, and
`- ⊗ Y₂`, `- ⊗ X₂` preserve the cokernel of `f₁`. For a second pair
of cokernels satisfying the same conditions, maps commuting with
the two quotient projections and the maps `k`, `k′` induce the
naturality square of their tensor descents. -/
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
  simpa only [tensorCokernelDesc, tensorCokernelIsColimit] using
    (CokernelCofork.tensorDesc_naturality
      c₁ (cokernelIsCokernel f₁) c₂ (cokernelIsCokernel f₂)
      c₁' (cokernelIsCokernel f₁') c₂' (cokernelIsCokernel f₂')
      a₁ a₂ q₁ q₂ hq₁ hq₂ k hk k' hk' z hz)

variable [HasCokernel (coprod.desc (f₁ ▷ Y₂) (Y₁ ◁ f₂))]

/- Let `C` be preadditive monoidal with tensor additive in both variables,
and let `f₁ : X₁ → Y₁`, `f₂ : X₂ → Y₂` have cokernels.
Assume `(X₁ ⊗ Y₂) ⨿ (Y₁ ⊗ X₂)` exists,
`cokernel(f₁) ⊗ -` preserves the cokernel of `f₂`, and
`- ⊗ Y₂`, `- ⊗ X₂` preserve the cokernel of `f₁`. If the sum
of the two tensor relations has a cokernel, there is a canonical
isomorphism from `cokernel f₁ ⊗ cokernel f₂` to that cokernel. -/
noncomputable def tensorCokernelIso :
    cokernel f₁ ⊗ cokernel f₂ ≅
      cokernel (coprod.desc (f₁ ▷ Y₂) (Y₁ ◁ f₂)) := by
  let c : CokernelCofork (coprod.desc (f₁ ▷ Y₂) (Y₁ ◁ f₂)) :=
    CokernelCofork.ofπ (cokernel.π (coprod.desc (f₁ ▷ Y₂) (Y₁ ◁ f₂)))
      (cokernel.condition _)
  let hc : IsColimit c := cokernelIsCokernel _
  exact IsColimit.coconePointUniqueUpToIso (tensorCokernelIsColimit f₁ f₂) hc

@[reassoc (attr := simp)]
lemma tensor_cokernel_π_comp_tensorCokernelIso_hom :
    (cokernel.π f₁ ⊗ₘ cokernel.π f₂) ≫ (tensorCokernelIso f₁ f₂).hom =
      cokernel.π (coprod.desc (f₁ ▷ Y₂) (Y₁ ◁ f₂)) := by
  let c : CokernelCofork (coprod.desc (f₁ ▷ Y₂) (Y₁ ◁ f₂)) :=
    CokernelCofork.ofπ (cokernel.π (coprod.desc (f₁ ▷ Y₂) (Y₁ ◁ f₂)))
      (cokernel.condition _)
  let hc : IsColimit c := cokernelIsCokernel _
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    (tensorCokernelIsColimit f₁ f₂) hc WalkingParallelPair.one
  change ((CokernelCofork.ofπ (cokernel.π f₁) (cokernel.condition f₁)).tensor
      (CokernelCofork.ofπ (cokernel.π f₂) (cokernel.condition f₂))).π ≫
      (IsColimit.coconePointUniqueUpToIso (tensorCokernelIsColimit f₁ f₂) hc).hom = c.π at h
  simpa only [tensorCokernelIso, c, hc, CokernelCofork.tensor,
    CokernelCofork.π_ofπ] using h

end CategoryTheory.Limits
