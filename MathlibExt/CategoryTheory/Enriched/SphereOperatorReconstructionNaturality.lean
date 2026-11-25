/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Enriched.SphereOperatorActionReconstruction

/-!
# Entire enriched coefficient naturality for the actual reverse action fields

The complete coefficient equation is determined by the actual unit separator
on the index Hom parameter. Every spectrum value and sphere object remains
entire. The target is the original fixed-right-tensor functor composed with
the genuine I-space, exactly as in the original operator coend weight.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.Enriched.SphereOperator.Reconstruction

open Limits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]

private theorem unitPoint_associator (X A H : V) (p : 𝟙_ V ⟶ H) :
    ((ρ_ (X ⊗ A)).inv ≫ (X ⊗ A) ◁ p) ≫ (α_ X A H).hom =
      X ◁ ((ρ_ A).inv ≫ A ◁ p) := by
  rw [Category.assoc, associator_naturality_right,
    ← whiskerLeft_rightUnitor_inv_assoc, ← whiskerLeft_comp]

private theorem hom_eq_of_rightUnitPoints [MonoidalClosed V]
    (hU : IsSeparator (𝟙_ V)) {A H Z : V} {f g : A ⊗ H ⟶ Z}
    (h : ∀ (p : 𝟙_ V ⟶ H),
      ((ρ_ A).inv ≫ A ◁ p) ≫ f = ((ρ_ A).inv ≫ A ◁ p) ≫ g) : f = g := by
  apply MonoidalClosed.curry_injective
  apply hU.def
  intro p
  apply MonoidalClosed.uncurry_injective
  have hf : MonoidalClosed.uncurry (p ≫ MonoidalClosed.curry f) = (A ◁ p) ≫ f :=
    (MonoidalClosed.uncurry_natural_left p (MonoidalClosed.curry f)).trans
      (congrArg (fun q => (A ◁ p) ≫ q) (MonoidalClosed.uncurry_curry f))
  have hg : MonoidalClosed.uncurry (p ≫ MonoidalClosed.curry g) = (A ◁ p) ≫ g :=
    (MonoidalClosed.uncurry_natural_left p (MonoidalClosed.curry g)).trans
      (congrArg (fun q => (A ◁ p) ≫ q) (MonoidalClosed.uncurry_curry g))
  have hPoint : (A ◁ p) ≫ f = (A ◁ p) ≫ g :=
    (cancel_epi (ρ_ A).inv).1 (by simpa only [Category.assoc] using h p)
  exact hf.trans (hPoint.trans hg.symm)

variable [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [BraidedCategory I]
  [EnrichedOrdinaryCategory V I]
  (d : EnrichedMonoidalCategoryData V I) (S X : EnrichedFunctor V I V)

attribute [local instance] Enriched.prodCategory

variable (t : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V))
    (X.externalTensor S) (d.tensorEnrichedFunctor.comp V X))

/-- The actual coefficient is genuinely natural on every entire continuous index Hom. -/
theorem coefficient_full_naturality (hU : IsSeparator (𝟙_ V))
    (n a b : I) :
    (α_ (X.obj n) (S.obj a) (a ⟶[V] b)).hom ≫
        (X.obj n ◁ MonoidalClosed.uncurry (S.map a b)) ≫ coefficient d S X t n b =
      (coefficient d S X t n a ▷ (a ⟶[V] b)) ≫ MonoidalClosed.uncurry
        (((fixedRightTensor d n).comp V X).map a b) := by
  let A := X.obj n ⊗ S.obj a
  let H : V := a ⟶[V] b
  let Y := X.obj (a ⊗ n)
  let J := (fixedRightTensor d n).comp V X
  let c := coefficient d S X t n a
  apply hom_eq_of_rightUnitPoints hU
  intro p
  let f : a ⟶ b := (eHomEquiv V).symm p
  have hp : eHomEquiv V f = p := Equiv.apply_symm_apply _ p
  let r := S.toOrdinaryFunctor.map f
  let s := X.toOrdinaryFunctor.map (f ▷ n)
  let e := MonoidalClosed.uncurry (S.map a b)
  let j := MonoidalClosed.uncurry (J.map a b)
  let pre := (ρ_ A).inv ≫ A ◁ p
  let insertS := (ρ_ (S.obj a)).inv ≫ S.obj a ◁ p
  let insertJ := (ρ_ Y).inv ≫ Y ◁ p
  have hSMap : p ≫ S.map a b = eHomEquiv V r := by
    have h := EnrichedFunctor.toOrdinaryFunctor_map S f
    rw [hp] at h
    exact h.symm
  have hJValue : J.map a b =
      (fixedRightTensor d n).map a b ≫ X.map (a ⊗ n) (b ⊗ n) := rfl
  have hFixed : p ≫ (fixedRightTensor d n).map a b = eHomEquiv V (f ▷ n) := by
    have h := fixedRightTensor_point d n f
    rw [hp] at h
    exact h
  have hJMap : p ≫ J.map a b = eHomEquiv V s :=
    (congrArg (fun q => p ≫ q) hJValue).trans
      ((Category.assoc p ((fixedRightTensor d n).map a b)
        (X.map (a ⊗ n) (b ⊗ n))).symm.trans
          ((congrArg (fun q => q ≫ X.map (a ⊗ n) (b ⊗ n)) hFixed).trans
            (EnrichedFunctor.toOrdinaryFunctor_map X (f ▷ n)).symm))
  have hSPoint : (S.obj a ◁ p) ≫ e = (ρ_ (S.obj a)).hom ≫ r :=
    uncurry_unitPoint p (S.map a b) r hSMap
  have hJPoint : (Y ◁ p) ≫ j = (ρ_ Y).hom ≫ s :=
    uncurry_unitPoint p (J.map a b) s hJMap
  have hSBound : insertS ≫ e = r :=
    (Category.assoc (ρ_ (S.obj a)).inv (S.obj a ◁ p) e).trans
      ((congrArg (fun q => (ρ_ (S.obj a)).inv ≫ q) hSPoint).trans
        (Iso.inv_hom_id_assoc (ρ_ (S.obj a)) r))
  have hJBound : insertJ ≫ j = s :=
    (Category.assoc (ρ_ Y).inv (Y ◁ p) j).trans
      ((congrArg (fun q => (ρ_ Y).inv ≫ q) hJPoint).trans
        (Iso.inv_hom_id_assoc (ρ_ Y) s))
  have hPrefix : pre ≫ (α_ (X.obj n) (S.obj a) H).hom = X.obj n ◁ insertS :=
    unitPoint_associator (X.obj n) (S.obj a) H p
  have hLeftPrefix : pre ≫ (α_ (X.obj n) (S.obj a) H).hom ≫ (X.obj n ◁ e) =
      X.obj n ◁ r :=
    (Category.assoc pre (α_ (X.obj n) (S.obj a) H).hom (X.obj n ◁ e)).symm.trans
      ((congrArg (fun q => q ≫ (X.obj n ◁ e)) hPrefix).trans
        ((whiskerLeft_comp (X.obj n) insertS e).symm.trans
          (congrArg (fun q => X.obj n ◁ q) hSBound)))
  have hTensor : (A ◁ p) ≫ (c ▷ H) = c ⊗ₘ p := (tensorHom_def' c p).symm
  have hRightPrefix : pre ≫ (c ▷ H) = c ≫ insertJ :=
    (Category.assoc (ρ_ A).inv (A ◁ p) (c ▷ H)).trans
      ((congrArg (fun q => (ρ_ A).inv ≫ q) hTensor).trans
        (rightUnitor_inv_comp_tensorHom c p))
  have hLeft : pre ≫ (α_ (X.obj n) (S.obj a) H).hom ≫
      (X.obj n ◁ e) ≫ coefficient d S X t n b =
    (X.obj n ◁ r) ≫ coefficient d S X t n b := by
    let cb := coefficient d S X t n b
    have hAppend : (pre ≫ (α_ (X.obj n) (S.obj a) H).hom ≫ (X.obj n ◁ e)) ≫ cb =
        (X.obj n ◁ r) ≫ cb := congrArg (fun q => q ≫ cb) hLeftPrefix
    have hAssoc : (pre ≫ (α_ (X.obj n) (S.obj a) H).hom ≫ (X.obj n ◁ e)) ≫ cb =
        pre ≫ (α_ (X.obj n) (S.obj a) H).hom ≫ (X.obj n ◁ e) ≫ cb :=
      (Category.assoc pre ((α_ (X.obj n) (S.obj a) H).hom ≫ (X.obj n ◁ e)) cb).trans
        (congrArg (fun q => pre ≫ q)
          (Category.assoc (α_ (X.obj n) (S.obj a) H).hom (X.obj n ◁ e) cb))
    exact hAssoc.symm.trans hAppend
  have hRight : pre ≫ (c ▷ H) ≫ j = c ≫ s :=
    (Category.assoc pre (c ▷ H) j).symm.trans
      ((congrArg (fun q => q ≫ j) hRightPrefix).trans
        ((Category.assoc c insertJ j).trans (congrArg (fun q => c ≫ q) hJBound)))
  have hOrdinary : (X.obj n ◁ r) ≫ coefficient d S X t n b = c ≫ s :=
    (coefficient_natural d S X t n a b f).trans
      (congrArg (fun q => c ≫ X.toOrdinaryFunctor.map q) (tensorHom_id f n))
  exact hLeft.trans (hOrdinary.trans hRight.symm)

end CategoryTheory.Enriched.SphereOperator.Reconstruction
