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

public import MathlibExt.Algebra.Category.ModuleCat.Bimodule.MoritaCoordinates

/-!
# Morita equivalence of bimodule categories

The two tensor functors use coefficient orders `Q–M–P` and `P–N–Q`.
Their return isomorphisms contract the outer tensor pairs and respect the
supplied bimodule actions. The resulting equivalence retains this counit
and adjusts the unit to satisfy the triangle identity.
-/

@[expose] public section

noncomputable section

open CategoryTheory MulOpposite TensorProduct.Balanced
open scoped TensorProduct

universe r s v

namespace ModuleCat.Bimodule.Morita

variable (R : Type r) (S : Type s) [Ring R] [Ring S]
  (P Q : Type v) [AddCommGroup P] [AddCommGroup Q]
  [Module R P] [Module Sᵐᵒᵖ P] [SMulCommClass R Sᵐᵒᵖ P]
  [Module S Q] [Module Rᵐᵒᵖ Q] [SMulCommClass S Rᵐᵒᵖ Q]
  (u : letI := TensorProduct.Balanced.leftModule ℤ S R P Q
    letI := TensorProduct.Balanced.rightModule ℤ S R P Q
    TensorProduct.Balanced ℤ S P Q ≃ₗ[Rᵐᵒᵖ] R)
  (hu : letI := TensorProduct.Balanced.leftModule ℤ S R P Q
    letI := TensorProduct.Balanced.rightModule ℤ S R P Q
    ∀ (r : R) (b : TensorProduct.Balanced ℤ S P Q), u (r • b) = r * u b)

include u hu in
/-- The earned complete return to the original native enveloping-module object. -/
def returnIso (X : ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ)) :
    ((tensorFunctor R S P Q) ⋙ (tensorFunctor S R Q P)).obj X ≅ X := by
  letI := ModuleCat.Bimodule.leftModule R X
  letI := ModuleCat.Bimodule.rightModule R X
  letI := ModuleCat.Bimodule.commute R X
  exact (returnCoordinates R S P Q X).trans
    ((rawReturnModuleIso R S P Q X u hu).trans (ModuleCat.Bimodule.reconstructedIso R X))

/-- The actual return contracts the two outer pairs and uses the original stored R-bimodule
action. -/
@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem returnIso_mk (X : ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ))
    (p₀ : P) (q₀ : Q) (x : X) (p₁ : P) (q₁ : Q) :
    letI := ModuleCat.Bimodule.leftModule R X
    letI := ModuleCat.Bimodule.rightModule R X
    letI := ModuleCat.Bimodule.commute R X
    letI := TensorProduct.Balanced.rightModule ℤ R R Q X
    (returnIso R S P Q u hu X).hom.hom
        (returnOuterMk R S P Q X p₀
          (mk ℤ R (TensorProduct.Balanced ℤ R Q X) P (mk ℤ R Q X q₀ x) p₁) q₁) =
      (u (mk ℤ S P Q p₀ q₀) ⊗ₜ[ℤ] op (u (mk ℤ S P Q p₁ q₁))) • x := by
  let := ModuleCat.Bimodule.leftModule R X
  let := ModuleCat.Bimodule.rightModule R X
  let := ModuleCat.Bimodule.commute R X
  let := TensorProduct.Balanced.rightModule ℤ R R Q X
  let c : tensorObj R S P Q X :=
    mk ℤ R (TensorProduct.Balanced ℤ R Q X) P (mk ℤ R Q X q₀ x) p₁
  let b : rawReturnObject R S P Q X := rawReturnOuterMk R S P Q X p₀ c q₁
  let C := returnCoordinates R S P Q X
  let F := (rawReturnModuleIso R S P Q X u hu).hom
  let H := (ModuleCat.Bimodule.reconstructedIso R X).hom
  have hC : C.hom.hom (returnOuterMk R S P Q X p₀ c q₁) = b :=
    returnCoordinates_mk R S P Q X p₀ c q₁
  have hF : F.hom b =
      u (mk ℤ S P Q p₀ q₀) • (op (u (mk ℤ S P Q p₁ q₁)) • x) :=
    rawReturnModuleIso_hom_mk R S P Q X u hu p₀ q₀ x p₁ q₁
  change H.hom (F.hom (C.hom.hom (returnOuterMk R S P Q X p₀ c q₁))) = _
  exact (congrArg (fun y : rawReturnObject R S P Q X => H.hom (F.hom y)) hC).trans
    ((ModuleCat.Bimodule.reconstructedIso_hom_apply R X (F.hom b)).trans
      (hF.trans (ModuleCat.Bimodule.smul_tmul R X
        (u (mk ℤ S P Q p₀ q₀)) (op (u (mk ℤ S P Q p₁ q₁))) x)))

include u hu in
/-- The actual composite contraction is natural in the original native bimodule morphism. -/
def returnNatIso :
    (tensorFunctor R S P Q) ⋙ (tensorFunctor S R Q P) ≅
      𝟭 (ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ)) :=
  NatIso.ofComponents (returnIso R S P Q u hu) (by
    intro X Y f
    let := ModuleCat.Bimodule.leftModule R X
    let := ModuleCat.Bimodule.rightModule R X
    let := ModuleCat.Bimodule.commute R X
    let := ModuleCat.Bimodule.leftModule R Y
    let := ModuleCat.Bimodule.rightModule R Y
    let := ModuleCat.Bimodule.commute R Y
    let := TensorProduct.Balanced.rightModule ℤ R R Q X
    let := TensorProduct.Balanced.rightModule ℤ R R Q Y
    apply ModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    apply returnHom_ext R S P Q X
    intro p₀ q₀ x p₁ q₁
    let c : tensorObj R S P Q X :=
      mk ℤ R (TensorProduct.Balanced ℤ R Q X) P (mk ℤ R Q X q₀ x) p₁
    let cY : tensorObj R S P Q Y :=
      mk ℤ R (TensorProduct.Balanced ℤ R Q Y) P (mk ℤ R Q Y q₀ (f.hom x)) p₁
    let T := (tensorFunctor R S P Q) ⋙ (tensorFunctor S R Q P)
    let x₀ : T.obj X := returnOuterMk R S P Q X p₀ c q₁
    let x₁ : T.obj Y := returnOuterMk R S P Q Y p₀ cY q₁
    let a : R ⊗[ℤ] Rᵐᵒᵖ :=
      u (mk ℤ S P Q p₀ q₀) ⊗ₜ[ℤ] op (u (mk ℤ S P Q p₁ q₁))
    have hOuter : (T.map f).hom x₀ =
        returnOuterMk R S P Q Y p₀ ((tensorMap R S P Q f).hom c) q₁ :=
      returnOuterMap_mk R S P Q f p₀ c q₁
    have hInner : (tensorMap R S P Q f).hom c = cY :=
      tensorMap_mk R S P Q f q₀ x p₁
    have hMap : (T.map f).hom x₀ = x₁ :=
      hOuter.trans (congrArg
        (fun y : tensorObj R S P Q Y => returnOuterMk R S P Q Y p₀ y q₁) hInner)
    have hY : (returnIso R S P Q u hu Y).hom.hom x₁ = a • f.hom x :=
      returnIso_mk R S P Q u hu Y p₀ q₀ (f.hom x) p₁ q₁
    have hX : (returnIso R S P Q u hu X).hom.hom x₀ = a • x :=
      returnIso_mk R S P Q u hu X p₀ q₀ x p₁ q₁
    change (returnIso R S P Q u hu Y).hom.hom ((T.map f).hom x₀) =
      f.hom ((returnIso R S P Q u hu X).hom.hom x₀)
    exact (congrArg (fun y : T.obj Y => (returnIso R S P Q u hu Y).hom.hom y) hMap).trans
      (hY.trans ((f.hom.map_smul a x).symm.trans
        (congrArg (fun y : X => f.hom y) hX.symm))))

variable
  (w : letI := TensorProduct.Balanced.leftModule ℤ R S Q P
    letI := TensorProduct.Balanced.rightModule ℤ R S Q P
    TensorProduct.Balanced ℤ R Q P ≃ₗ[Sᵐᵒᵖ] S)
  (hw : letI := TensorProduct.Balanced.leftModule ℤ R S Q P
    letI := TensorProduct.Balanced.rightModule ℤ R S Q P
    ∀ (s : S) (b : TensorProduct.Balanced ℤ R Q P), w (s • b) = s * w b)

include u hu w hw in
/-- The actual bimodule-category equivalence from the two invertible contractions. -/
def equivalence :
    ModuleCat.{v} (R ⊗[ℤ] Rᵐᵒᵖ) ≌ ModuleCat.{v} (S ⊗[ℤ] Sᵐᵒᵖ) :=
  CategoryTheory.Equivalence.mk (tensorFunctor R S P Q) (tensorFunctor S R Q P)
    (returnNatIso R S P Q u hu).symm (returnNatIso S R Q P w hw)

@[simp]
theorem equivalence_functor : (equivalence R S P Q u hu w hw).functor =
    tensorFunctor R S P Q := rfl

@[simp]
theorem equivalence_inverse : (equivalence R S P Q u hu w hw).inverse =
    tensorFunctor S R Q P := rfl

/-- Native adjointification keeps the actual symmetric return counit. -/
theorem equivalence_counitIso : (equivalence R S P Q u hu w hw).counitIso =
    returnNatIso S R Q P w hw := rfl

/-- The actual chosen unit is the native adjointified unit, not an assumed normalized
contraction. -/
theorem equivalence_unitIso : (equivalence R S P Q u hu w hw).unitIso =
    Equivalence.adjointifyη (returnNatIso R S P Q u hu).symm
      (returnNatIso S R Q P w hw) := rfl

/-- The retained counit has the original two-contraction coefficient value. -/
@[simp, nolint simpNF] -- stated with Balanced.mk for rw; Balanced.mk_apply simplifies LHS
theorem equivalence_counitIso_mk (Y : ModuleCat.{v} (S ⊗[ℤ] Sᵐᵒᵖ))
    (q₀ : Q) (p₀ : P) (y : Y) (q₁ : Q) (p₁ : P) :
    letI := ModuleCat.Bimodule.leftModule S Y
    letI := ModuleCat.Bimodule.rightModule S Y
    letI := ModuleCat.Bimodule.commute S Y
    letI := TensorProduct.Balanced.rightModule ℤ S S P Y
    ((equivalence R S P Q u hu w hw).counitIso.hom.app Y).hom
        (returnOuterMk S R Q P Y q₀
          (mk ℤ S (TensorProduct.Balanced ℤ S P Y) Q (mk ℤ S P Y p₀ y) q₁) p₁) =
      (w (mk ℤ R Q P q₀ p₀) ⊗ₜ[ℤ] op (w (mk ℤ R Q P q₁ p₁))) • y :=
  returnIso_mk S R Q P w hw Y q₀ p₀ y q₁ p₁

end ModuleCat.Bimodule.Morita
