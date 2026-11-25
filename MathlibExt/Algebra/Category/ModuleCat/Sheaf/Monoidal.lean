/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @junekim623, Muse
-/

module

public import MathlibExt.Algebra.Category.Grp.Monoidal
public import MathlibExt.Algebra.Category.ModuleCat.Presheaf.MonoidalCompat
public import MathlibExt.Algebra.Category.ModuleCat.Presheaf.SheafificationCompat
public import MathlibExt.Algebra.Category.ModuleCat.Sheaf.MonoidalCore
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Preadditive
public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import MathlibExt.CategoryTheory.Localization.BousfieldCompat
public import MathlibExt.Algebra.Category.ModuleCat.Presheaf.Closed
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import Mathlib.CategoryTheory.Localization.Monoidal.Basic

/-!
# Monoidal structure for sheaves of modules

For a sheaf of commutative rings, sheafification localizes the presheaf
tensor product to the tensor product of module sheaves. The resulting
comparisons give colimit preservation, free-sheaf tensor formulas, tensor
products of generating families, and compatibility with pushforward and
restriction.
-/

@[expose] public section

universe v u

open _root_.CategoryTheory CategoryTheory MonoidalCategory Limits
open scoped _root_.AddCommGrpCat AddCommGrpCat
open scoped MonoidalCategory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}


namespace SheafOfModules

variable (R : Sheaf J CommRingCat.{u})
variable [(J.W (A := Ab.{u})).IsMonoidal] [J.WEqualsLocallyBijective Ab.{u}]
variable [HasWeakSheafify J Ab.{u}] [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- The sheafification functor over a sheaf of commutative rings is monoidal,
via the localization monoidal structure. -/
noncomputable instance sheafificationCommIdMonoidal :
    (PresheafOfModules.sheafificationCommId R).Monoidal :=
  inferInstanceAs
    (Localization.Monoidal.toMonoidalCategory
      (PresheafOfModules.sheafificationCommId R)
      (J.W.inverseImage (PresheafOfModules.toPresheaf _)) (.refl _)).Monoidal

/-- Monoidal closed structure on sheaves of modules, by Day reflection from
presheaves. Moved here from `Sheaf/Closed` so colimit preservation of
`tensorLeft` below is derived from the closed structure
(`ihom.adjunction`) instead of a bespoke counit transport argument. -/
noncomputable instance monoidalClosed :
    MonoidalClosed
      (SheafOfModules.{u} ((sheafCompose J (forget₂ _ _)).obj R)) :=
  Monoidal.Reflective.monoidalClosed
    (PresheafOfModules.sheafificationAdjunction (Sheaf.commRingCatForget₂Id R))

/-- The comparison isomorphism `tensorLeft A ⋙ L ≅ L ⋙ tensorLeft (L.obj A)`
induced by the localized monoidal structure (`Localization.Monoidal.μ`). -/
noncomputable def tensorLeftSheafificationIso
    (A : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})) :
    tensorLeft A ⋙ PresheafOfModules.sheafificationCommId R ≅
      PresheafOfModules.sheafificationCommId R ⋙
        tensorLeft ((PresheafOfModules.sheafificationCommId R).obj A) :=
  _root_.CategoryTheory.NatIso.ofComponents
    (fun Y => (Localization.Monoidal.μ (PresheafOfModules.sheafificationCommId R)
      (J.W.inverseImage
        (PresheafOfModules.toPresheaf (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})))
      (.refl _) A Y).symm)
    (by intro Y₁ Y₂ g
        exact (Localization.Monoidal.μ_inv_natural_right
          (PresheafOfModules.sheafificationCommId R)
          (J.W.inverseImage
            (PresheafOfModules.toPresheaf (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})))
          (.refl _) A g).symm)

/-- For a presheaf `A`, tensoring with its sheafification preserves colimits:
`tensorLeft` is a left adjoint by the monoidal closed structure above. -/
noncomputable instance preservesColimitsOfSize_tensorLeft_sheafification
    (A : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})) :
    _root_.CategoryTheory.Limits.PreservesColimitsOfSize.{u, u}
      (tensorLeft ((PresheafOfModules.sheafificationCommId R).obj A)) :=
  (ihom.adjunction _).leftAdjoint_preservesColimits

/-- Tensoring with an arbitrary sheaf of modules preserves colimits:
`tensorLeft M` is a left adjoint by the monoidal closed structure above. -/
noncomputable instance preservesColimitsOfSize_tensorLeft
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    _root_.CategoryTheory.Limits.PreservesColimitsOfSize.{u, u} (tensorLeft M) :=
  (ihom.adjunction M).leftAdjoint_preservesColimits

/-- Tensoring on the right with a sheaf of modules preserves colimits. -/
noncomputable instance preservesColimitsOfSize_tensorRight
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    _root_.CategoryTheory.Limits.PreservesColimitsOfSize.{u, u} (tensorRight M) :=
  preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)

/-- The tensor unit of sheaves of modules is the structure sheaf. -/
noncomputable def tensorUnitIso :
    𝟙_ (SheafOfModules.{u} ((sheafCompose J (forget₂ _ _)).obj R)) ≅
      SheafOfModules.unit ((sheafCompose J (forget₂ _ _)).obj R) :=
  (asIso ((PresheafOfModules.sheafificationAdjunction
    (Sheaf.commRingCatForget₂Id R)).counit)).app
    (SheafOfModules.unit ((sheafCompose J (forget₂ _ _)).obj R))

namespace FreeTensor

/-- Inner leg `unit ⊗ unit ⟶ free (A × B)` at `(a, b)`. -/
noncomputable def innerLeg (A B : Type u) (a : A) (b : B) :
    SheafOfModules.unit (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ⊗
      SheafOfModules.unit (R :=
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ⟶
    SheafOfModules.free (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (A × B) :=
  ((tensorUnitIso R).inv ⊗ₘ 𝟙 _) ≫ (λ_ _).hom ≫ SheafOfModules.ιFree (a, b)

/-- Outer leg `unit ⟶ free A ⊗ free B` at `(a, b)`. -/
noncomputable def outerLeg (A B : Type u) (a : A) (b : B) :
    SheafOfModules.unit (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ⟶
      SheafOfModules.free (R :=
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) A ⊗
      SheafOfModules.free (R :=
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) B :=
  (λ_ _).inv ≫ ((tensorUnitIso R).hom ⊗ₘ 𝟙 _) ≫
    (SheafOfModules.ιFree a ⊗ₘ SheafOfModules.ιFree b)

/-- Inner colimit: tensoring the free cofan on `A` on the right by `unit`. -/
noncomputable def innerIsColimit (A : Type u) :
    _root_.CategoryTheory.Limits.IsColimit (Cofan.mk
      ((tensorRight (SheafOfModules.unit (R :=
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))).obj
        (SheafOfModules.free (R :=
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) A))
      (fun a ↦ (tensorRight (SheafOfModules.unit (R :=
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))).map
        (SheafOfModules.ιFree a))) :=
  isColimitCofanMkObjOfIsColimit _ _ _ (SheafOfModules.isColimitFreeCofan A)

/-- Outer colimit: tensoring the free cofan on `B` on the left by `free A`. -/
noncomputable def outerIsColimit (A B : Type u) :
    _root_.CategoryTheory.Limits.IsColimit (Cofan.mk
      ((tensorLeft (SheafOfModules.free (R :=
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) A)).obj
        (SheafOfModules.free (R :=
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) B))
      (fun b ↦ (tensorLeft (SheafOfModules.free (R :=
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) A)).map
        (SheafOfModules.ιFree b))) :=
  isColimitCofanMkObjOfIsColimit _ _ _ (SheafOfModules.isColimitFreeCofan B)

/-- Inner descendant `free A ⊗ unit ⟶ free (A × B)` at fixed `b : B`. -/
noncomputable def innerDesc (A B : Type u) (b : B) :
    (tensorRight (SheafOfModules.unit (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))).obj
      (SheafOfModules.free (R :=
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) A) ⟶
    SheafOfModules.free (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (A × B) :=
  Cofan.IsColimit.desc (innerIsColimit R A) (fun a ↦ innerLeg R A B a b)

/-- Forward map `free A ⊗ free B ⟶ free (A × B)`. -/
noncomputable def forwardHom (A B : Type u) :
    SheafOfModules.free (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) A ⊗
    SheafOfModules.free (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) B ⟶
    SheafOfModules.free (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (A × B) :=
  Cofan.IsColimit.desc (outerIsColimit R A B) (fun b ↦ innerDesc R A B b)

/-- Backward map `free (A × B) ⟶ free A ⊗ free B`. -/
noncomputable def backwardHom (A B : Type u) :
    SheafOfModules.free (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (A × B) ⟶
    SheafOfModules.free (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) A ⊗
    SheafOfModules.free (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) B :=
  Cofan.IsColimit.desc (SheafOfModules.isColimitFreeCofan (A × B))
    (fun p ↦ outerLeg R A B p.1 p.2)

/-- The outer leg of `forwardHom` at `b`. -/
theorem forwardHom_fac (A B : Type u) (b : B) :
    (tensorLeft (SheafOfModules.free (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) A)).map
      (SheafOfModules.ιFree b) ≫ forwardHom R A B = innerDesc R A B b :=
  Cofan.IsColimit.fac (outerIsColimit R A B) _ b

/-- The inner leg of `innerDesc` at `a`. -/
theorem innerDesc_fac (A B : Type u) (a : A) (b : B) :
    (tensorRight (SheafOfModules.unit (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))).map
      (SheafOfModules.ιFree a) ≫ innerDesc R A B b = innerLeg R A B a b :=
  Cofan.IsColimit.fac (innerIsColimit R A) _ a

/-- The basis leg of `backwardHom` at `p`. -/
theorem backwardHom_fac (A B : Type u) (p : A × B) :
    SheafOfModules.ιFree p ≫ backwardHom R A B = outerLeg R A B p.1 p.2 :=
  Cofan.IsColimit.fac (SheafOfModules.isColimitFreeCofan (A × B)) _ p

/-- Basis characterization: the outer leg followed by `forwardHom` is the basis inclusion. -/
@[simp]
theorem outerLeg_forwardHom (A B : Type u) (a : A) (b : B) :
    outerLeg R A B a b ≫ forwardHom R A B = SheafOfModules.ιFree (a, b) := by
  have h1 : (tensorLeft (SheafOfModules.free (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) A)).map
      (SheafOfModules.ιFree b) ≫ forwardHom R A B = innerDesc R A B b :=
    Cofan.IsColimit.fac (outerIsColimit R A B) _ b
  have h2 : (tensorRight (SheafOfModules.unit (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))).map
      (SheafOfModules.ιFree a) ≫ innerDesc R A B b = innerLeg R A B a b :=
    Cofan.IsColimit.fac (innerIsColimit R A) _ a
  have hT : (SheafOfModules.ιFree a ⊗ₘ SheafOfModules.ιFree b) =
      (tensorRight (SheafOfModules.unit (R :=
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))).map
        (SheafOfModules.ιFree a) ≫
      (tensorLeft (SheafOfModules.free (R :=
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) A)).map
        (SheafOfModules.ιFree b) :=
    tensorHom_def _ _
  have hU : ((tensorUnitIso R).hom ⊗ₘ (𝟙 _
      : SheafOfModules.unit (R :=
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ⟶
        SheafOfModules.unit (R :=
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))) ≫
      ((tensorUnitIso R).inv ⊗ₘ 𝟙 _) = 𝟙 _ := by simp
  change (λ_ _).inv ≫ ((tensorUnitIso R).hom ⊗ₘ 𝟙 _) ≫
    (SheafOfModules.ιFree a ⊗ₘ SheafOfModules.ιFree b) ≫ forwardHom R A B = _
  rw [hT]
  simp only [Category.assoc]
  rw [h1, h2]
  change (λ_ (SheafOfModules.unit (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))).inv ≫
    ((tensorUnitIso R).hom ⊗ₘ 𝟙 _) ≫
      (((tensorUnitIso R).inv ⊗ₘ 𝟙 _) ≫ (λ_ _).hom ≫
        SheafOfModules.ιFree (a, b)) = _
  rw [← Category.assoc ((tensorUnitIso R).hom ⊗ₘ 𝟙 _) ((tensorUnitIso R).inv ⊗ₘ 𝟙 _) _, hU,
    Category.id_comp, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The inner leg followed by `backwardHom` is the tensor of basis inclusions. -/
@[simp]
theorem innerLeg_backwardHom (A B : Type u) (a : A) (b : B) :
    innerLeg R A B a b ≫ backwardHom R A B =
      SheafOfModules.ιFree a ⊗ₘ SheafOfModules.ιFree b := by
  have hfac : SheafOfModules.ιFree (a, b) ≫ backwardHom R A B = outerLeg R A B a b :=
    Cofan.IsColimit.fac (SheafOfModules.isColimitFreeCofan (A × B)) _ (a, b)
  have hU : ((tensorUnitIso R).inv ⊗ₘ (𝟙 _
      : SheafOfModules.unit (R :=
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ⟶
        SheafOfModules.unit (R :=
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))) ≫
      ((tensorUnitIso R).hom ⊗ₘ 𝟙 _) = 𝟙 _ := by simp
  have hOuterLeg : outerLeg R A B a b = (λ_ _).inv ≫ ((tensorUnitIso R).hom ⊗ₘ 𝟙 _) ≫
      (SheafOfModules.ιFree a ⊗ₘ SheafOfModules.ιFree b) := rfl
  change ((tensorUnitIso R).inv ⊗ₘ 𝟙 _) ≫ (λ_ _).hom ≫ SheafOfModules.ιFree (a, b) ≫
    backwardHom R A B = _
  rw [hfac, hOuterLeg]
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, hU, Category.id_comp]

/-- Forward then backward is the identity, by colimit induction on the outer
cofan and then the inner cofan. -/
theorem forwardHom_backwardHom (A B : Type u) : forwardHom R A B ≫ backwardHom R A B = 𝟙 _ := by
  refine Cofan.IsColimit.hom_ext (outerIsColimit R A B) _ _ (fun b ↦ ?_)
  change (tensorLeft (SheafOfModules.free (R := _) A)).map
      (SheafOfModules.ιFree b) ≫ (forwardHom R A B ≫ backwardHom R A B) =
    (tensorLeft (SheafOfModules.free (R := _) A)).map
      (SheafOfModules.ιFree b) ≫ 𝟙 _
  have hfacOut : (tensorLeft (SheafOfModules.free (R := _) A)).map
        (SheafOfModules.ιFree b) ≫ forwardHom R A B = innerDesc R A B b :=
    Cofan.IsColimit.fac (outerIsColimit R A B) _ b
  have key : innerDesc R A B b ≫ backwardHom R A B =
      (tensorLeft (SheafOfModules.free (R := _) A)).map
        (SheafOfModules.ιFree b) := by
    refine Cofan.IsColimit.hom_ext (innerIsColimit R A) _ _ (fun a ↦ ?_)
    change (tensorRight (SheafOfModules.unit (R := _))).map
        (SheafOfModules.ιFree a) ≫ (innerDesc R A B b ≫ backwardHom R A B) =
      (tensorRight (SheafOfModules.unit (R := _))).map
        (SheafOfModules.ιFree a) ≫
        (tensorLeft (SheafOfModules.free (R := _) A)).map
          (SheafOfModules.ιFree b)
    have hfacIn : (tensorRight (SheafOfModules.unit (R := _))).map
          (SheafOfModules.ιFree a) ≫ innerDesc R A B b = innerLeg R A B a b :=
      Cofan.IsColimit.fac (innerIsColimit R A) _ a
    rw [← Category.assoc, hfacIn, innerLeg_backwardHom]
    exact tensorHom_def _ _
  rw [← Category.assoc, hfacOut, key, Category.comp_id]

/-- Backward then forward is the identity, by colimit induction on the free
cofan on `A × B`. -/
theorem backwardHom_forwardHom (A B : Type u) : backwardHom R A B ≫ forwardHom R A B = 𝟙 _ := by
  refine Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan (A × B)) _ _
    (fun p ↦ ?_)
  change SheafOfModules.ιFree p ≫ (backwardHom R A B ≫ forwardHom R A B) =
    SheafOfModules.ιFree p ≫ 𝟙 _
  have hfac : SheafOfModules.ιFree p ≫ backwardHom R A B = outerLeg R A B p.1 p.2 :=
    Cofan.IsColimit.fac (SheafOfModules.isColimitFreeCofan (A × B)) _ p
  rw [← Category.assoc, hfac, outerLeg_forwardHom, Category.comp_id, Prod.mk.eta]

end FreeTensor

/-- The tensor product of two free sheaves of modules is free on the product:
`free A ⊗ free B ≅ free (A × B)`. -/
noncomputable def freeTensorIso (A B : Type u) :
    SheafOfModules.free (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) A ⊗
    SheafOfModules.free (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) B ≅
    SheafOfModules.free (R :=
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (A × B) where
  hom := FreeTensor.forwardHom R A B
  inv := FreeTensor.backwardHom R A B
  hom_inv_id := FreeTensor.forwardHom_backwardHom R A B
  inv_hom_id := FreeTensor.backwardHom_forwardHom R A B

/-- Basis characterization of the forward direction. -/
theorem freeTensorIso_hom_basis (A B : Type u) (a : A) (b : B) :
    FreeTensor.outerLeg R A B a b ≫ (freeTensorIso R A B).hom =
      SheafOfModules.ιFree (a, b) :=
  FreeTensor.outerLeg_forwardHom R A B a b

/-- Basis characterization of the backward direction. -/
theorem freeTensorIso_inv_basis (A B : Type u) (p : A × B) :
    SheafOfModules.ιFree p ≫ (freeTensorIso R A B).inv =
      FreeTensor.outerLeg R A B p.1 p.2 :=
  FreeTensor.backwardHom_fac R A B p

namespace GeneratingSections

variable {M N : SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)}

/-- Tensor product of two generating families is epi, since each leg is an epi
and tensoring with a fixed sheaf preserves epis (via colimit preservation). -/
theorem epi_tensorHom_π (G : M.GeneratingSections) (H : N.GeneratingSections) :
    Epi (G.π ⊗ₘ H.π) := by
  have : _root_.CategoryTheory.Limits.PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
    preservesColimitsOfSize_shrink _
  have : _root_.CategoryTheory.Limits.PreservesColimitsOfSize.{0, 0}
      (tensorRight (SheafOfModules.free
        (R := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) H.I)) :=
    preservesColimitsOfSize_shrink _
  have e1 : Epi ((tensorRight (SheafOfModules.free
      (R := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) H.I)).map
      G.π) :=
    inferInstance
  have e2 : Epi ((tensorLeft M).map H.π) := inferInstance
  have h : G.π ⊗ₘ H.π =
      (tensorRight (SheafOfModules.free
        (R := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) H.I)).map
        G.π ≫
        (tensorLeft M).map H.π :=
    tensorHom_def _ _
  rw [h]
  exact inferInstance

/-- Tensor product of two isomorphism-generating families: the index type is the
product, built from `freeTensorIso.inv ≫ (G.π ⊗ₘ H.π)`. -/
noncomputable def _root_.SheafOfModules.GeneratingSections.tensor (G : M.GeneratingSections)
    (H : N.GeneratingSections) :
    (M ⊗ N).GeneratingSections :=
  haveI : Epi (G.π ⊗ₘ H.π) := epi_tensorHom_π R G H
  haveI : Epi ((freeTensorIso R G.I H.I).inv ≫ (G.π ⊗ₘ H.π)) :=
    epi_comp _ _
  (SheafOfModules.free.generatingSections (G.I × H.I)).ofEpi
    ((freeTensorIso R G.I H.I).inv ≫ (G.π ⊗ₘ H.π))

/-- The index type of a tensor of generating families is the product. -/
@[simp]
theorem tensor_I (G : M.GeneratingSections) (H : N.GeneratingSections) :
    (tensor G (R := R) H).I = (G.I × H.I) :=
  rfl

/-- Reflexivity equivalence on the tensor index type. -/
def tensorIndexEquiv (G : M.GeneratingSections) (H : N.GeneratingSections) :
    (tensor G (R := R) H).I ≃ (G.I × H.I) :=
  Equiv.refl _

/-- Rank multiplication on indices: product of `Fin` equivalences through the
tensor index type. -/
def tensorRankEquiv {m n : ℕ} (G : M.GeneratingSections) (H : N.GeneratingSections)
    (eG : G.I ≃ Fin m) (eH : H.I ≃ Fin n) :
    (tensor G (R := R) H).I ≃ Fin (m * n) :=
  (tensorIndexEquiv R G H).trans ((eG.prodCongr eH).trans finProdFinEquiv)

/-- Formula for the presenting epi of a tensor of generating families. -/
@[simp]
theorem tensor_π (G : M.GeneratingSections) (H : N.GeneratingSections) :
    (tensor G (R := R) H).π =
      (freeTensorIso R G.I H.I).inv ≫ (G.π ⊗ₘ H.π) := by
  unfold _root_.SheafOfModules.GeneratingSections.tensor
  rw [_root_.SheafOfModules.GeneratingSections.ofEpi_π, SheafOfModules.free.generatingSections_π]
  exact Category.id_comp _

/-- Tensor of two iso-generating families is iso-generating. -/
instance tensor_isIso_π (G : M.GeneratingSections) (H : N.GeneratingSections)
    [IsIso G.π] [IsIso H.π] : IsIso (tensor G (R := R) H).π := by
  rw [tensor_π]
  exact IsIso.comp_isIso' (Iso.isIso_inv _)
    (MonoidalCategory.tensor_isIso _ _)

end GeneratingSections

end SheafOfModules

namespace SheafOfModules

variable (R : Sheaf J CommRingCat.{u})
variable [(J.W (A := Ab.{u})).IsMonoidal] [J.WEqualsLocallyBijective Ab.{u}]
variable [HasWeakSheafify J Ab.{u}] [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

namespace RestrictSheafification

variable (X : C)

omit [(J.W (A := Ab.{u})).IsMonoidal] [J.WEqualsLocallyBijective Ab.{u}]
  [HasWeakSheafify J Ab.{u}] [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Precomposition with `Over.forget` preserves local injectivity. -/
-- Stated above the site-variable blocks (with the `J`-level hypotheses
-- omitted) so no unneeded sheaf/monoidal hypotheses enter the signature
-- (the Mathlib whisker lemmas need none).
instance whiskerIsLocallyInjective (P Q : Cᵒᵖ ⥤ Ab.{u}) (f : P ⟶ Q)
    [Presheaf.IsLocallyInjective J f] :
    Presheaf.IsLocallyInjective (J.over X) ((Over.forget X).op.whiskerLeft f) :=
  CategoryTheory.Presheaf.isLocallyInjective_whisker _ J _ f

omit [(J.W (A := Ab.{u})).IsMonoidal] [J.WEqualsLocallyBijective Ab.{u}]
  [HasWeakSheafify J Ab.{u}] [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Precomposition with `Over.forget` preserves local surjectivity. -/
instance whiskerIsLocallySurjective (P Q : Cᵒᵖ ⥤ Ab.{u}) (f : P ⟶ Q)
    [Presheaf.IsLocallySurjective J f] :
    Presheaf.IsLocallySurjective (J.over X) ((Over.forget X).op.whiskerLeft f) :=
  CategoryTheory.Presheaf.isLocallySurjective_whisker _ J _ f

variable [((J.over X).W (A := Ab.{u})).IsMonoidal] [(J.over X).WEqualsLocallyBijective Ab.{u}]
variable [HasWeakSheafify (J.over X) Ab.{u}]
variable [(J.over X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable (A : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}))

/-- Rings stated once, so later applications are syntactically clean.
`restrictPresheaf` target ring = `sheafificationOver` source ring; `restrictSheaf` target ring =
`forgetRestrictOver` sheaf ring. -/
noncomputable abbrev overRing : (Over X)ᵒᵖ ⥤ RingCat.{u} :=
  (Sheaf.over R X).obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}
/-- `R` as a sheaf of rings, forgetting commutativity. -/
noncomputable abbrev sheafComposeRing :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R
/-- The restriction of `R` to `Over X`, as a sheaf of rings. -/
noncomputable abbrev overSheafComposeRing :=
  (sheafCompose (J.over X) (forget₂ CommRingCat.{u} RingCat.{u})).obj (Sheaf.over R X)

/-- Presheaf restriction to `Over X` (precomposition), with target ring stated
as the source ring of sheafification over `X` (definitionally equal). -/
noncomputable abbrev restrictPresheaf :
    PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) ⥤
    PresheafOfModules.{u} (overRing R X) :=
  PresheafOfModules.pushforward₀OfCommRingCat (Over.forget X) R.obj
/-- The sheafification functor for presheaves of modules over `R`. -/
noncomputable abbrev sheafificationBase := PresheafOfModules.sheafificationCommId R
/-- The `Over X` version of `sheafificationBase`. -/
noncomputable abbrev sheafificationOver := PresheafOfModules.sheafificationCommId (Sheaf.over R X)
/-- Sheaf restriction to `Over X`, with target ring stated as `overSheafComposeRing`. -/
noncomputable abbrev restrictSheaf : SheafOfModules.{u} (sheafComposeRing R) ⥤
    SheafOfModules.{u} (overSheafComposeRing R X) :=
  SheafOfModules.overFunctor (sheafComposeRing R) X
/-- Forgetful functor to presheaves of modules over `R.obj ⋙ forget₂ _ _`. -/
noncomputable abbrev forgetRestrictBase :=
  SheafOfModules.forget (sheafComposeRing R) ⋙
    PresheafOfModules.restrictScalars (CategoryTheory.Sheaf.commRingCatForget₂Id R)
/-- The `Over X` version of `forgetRestrictBase`. -/
noncomputable abbrev forgetRestrictOver :=
  SheafOfModules.forget (overSheafComposeRing R X) ⋙
    PresheafOfModules.restrictScalars
      (CategoryTheory.Sheaf.commRingCatForget₂Id (Sheaf.over R X))
/-- The sheafification adjunction for presheaves of modules over `R`. -/
noncomputable abbrev sheafificationAdjBase := PresheafOfModules.sheafificationAdjunction
  (CategoryTheory.Sheaf.commRingCatForget₂Id R)
/-- The `Over X` version of `sheafificationAdjBase`. -/
noncomputable abbrev sheafificationAdjOver := PresheafOfModules.sheafificationAdjunction
  (CategoryTheory.Sheaf.commRingCatForget₂Id (Sheaf.over R X))

/-- `restrictPresheaf` after forgetting from sheaves agrees with forgetting after `restrictSheaf`
(`rfl` on objects and maps). -/
noncomputable def forgetRestrictIso (S : SheafOfModules.{u} (sheafComposeRing R)) :
    (restrictPresheaf R X).obj ((forgetRestrictBase R).obj S) ≅
      (forgetRestrictOver R X).obj ((restrictSheaf R X).obj S) :=
  Iso.refl _

/-- Adjoint form of the comparison map. -/
noncomputable def comparisonAdjoint :
    (restrictPresheaf R X).obj A ⟶
      (forgetRestrictOver R X).obj ((restrictSheaf R X).obj ((sheafificationBase R).obj A)) :=
  (restrictPresheaf R X).map ((sheafificationAdjBase R).unit.app A) ≫
    (forgetRestrictIso R X ((sheafificationBase R).obj A)).hom

/-- Objectwise comparison `sheafificationOver.obj (restrictPresheaf.obj A) ⟶ restrictSheaf.obj
(sheafificationBase.obj A)`. -/
noncomputable def comparisonHom :
    (sheafificationOver R X).obj ((restrictPresheaf R X).obj A) ⟶
      (restrictSheaf R X).obj ((sheafificationBase R).obj A) :=
  ((sheafificationAdjOver R X).homEquiv _ _).symm (comparisonAdjoint R X A)

omit [(J.W (A := Ab.{u})).IsMonoidal] [((J.over X).W (A := Ab.{u})).IsMonoidal] in
/-- `comparisonHom` as sheafification of its adjoint followed by the counit. -/
theorem comparisonHom_eq :
    comparisonHom R X A =
      (sheafificationOver R X).map (comparisonAdjoint R X A) ≫
        (sheafificationAdjOver R X).counit.app
            ((restrictSheaf R X).obj ((sheafificationBase R).obj A)) :=
  (sheafificationAdjOver R X).homEquiv_counit _ _ _

omit [(J.W (A := Ab.{u})).IsMonoidal] [J.WEqualsLocallyBijective Ab.{u}]
  [HasWeakSheafify J Ab.{u}] [((J.over X).W (A := Ab.{u})).IsMonoidal]
  [(J.over X).WEqualsLocallyBijective Ab.{u}] [HasWeakSheafify (J.over X) Ab.{u}] in
/-- Naturality of the `rfl` identification on maps. -/
theorem forgetRestrictIso_naturality {S T : SheafOfModules.{u} (sheafComposeRing R)} (f : S ⟶ T) :
    (forgetRestrictIso R X S).hom ≫ (forgetRestrictOver R X).map ((restrictSheaf R X).map f) =
      (restrictPresheaf R X).map ((forgetRestrictBase R).map f) ≫
        (forgetRestrictIso R X T).hom := rfl

omit [(J.W (A := Ab.{u})).IsMonoidal] [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [((J.over X).W (A := Ab.{u})).IsMonoidal] [HasWeakSheafify (J.over X) Ab.{u}]
  [(J.over X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Whiskered sheafification units lie in `W` over `X`. -/
theorem whiskerToSheafify_memW (P : Cᵒᵖ ⥤ Ab.{u}) :
    (J.over X).W ((Over.forget X).op.whiskerLeft (CategoryTheory.toSheafify J P)) :=
  -- Whiskering preserves local bijectivity of the sheafification unit.
  
  GrothendieckTopology.W_of_isLocallyBijective _ _

omit [(J.W (A := Ab.{u})).IsMonoidal] [((J.over X).W (A := Ab.{u})).IsMonoidal]
  [HasWeakSheafify (J.over X) Ab.{u}]
  [(J.over X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
theorem comparisonAdjoint_memW : (J.over X).W ((PresheafOfModules.toPresheaf _).map
    ((restrictPresheaf R X).map ((sheafificationAdjBase R).unit.app A))) := by
  have h1 : (PresheafOfModules.toPresheaf _).map ((sheafificationAdjBase R).unit.app A) =
      CategoryTheory.toSheafify J ((PresheafOfModules.toPresheaf _).obj A) := rfl
  have h2 : (PresheafOfModules.toPresheaf _).map
      ((restrictPresheaf R X).map ((sheafificationAdjBase R).unit.app A)) =
      (Over.forget X).op.whiskerLeft
        ((PresheafOfModules.toPresheaf _).map ((sheafificationAdjBase R).unit.app A)) := rfl
  rw [h2, h1]
  have hLI : Presheaf.IsLocallyInjective J
      (CategoryTheory.toSheafify J ((PresheafOfModules.toPresheaf _).obj A)) :=
    inferInstance
  have hLS : Presheaf.IsLocallySurjective J
      (CategoryTheory.toSheafify J ((PresheafOfModules.toPresheaf _).obj A)) :=
    inferInstance
  -- The whiskered unit is locally injective and locally surjective.
  have hWLI : Presheaf.IsLocallyInjective (J.over X)
      ((Over.forget X).op.whiskerLeft
        (CategoryTheory.toSheafify J ((PresheafOfModules.toPresheaf _).obj A))) :=
    CategoryTheory.Presheaf.isLocallyInjective_whisker (J.over X) J
      (Over.forget X)
      (CategoryTheory.toSheafify J ((PresheafOfModules.toPresheaf _).obj A))
  have hWLS : Presheaf.IsLocallySurjective (J.over X)
      ((Over.forget X).op.whiskerLeft
        (CategoryTheory.toSheafify J ((PresheafOfModules.toPresheaf _).obj A))) :=
    CategoryTheory.Presheaf.isLocallySurjective_whisker (J.over X) J
      (Over.forget X)
      (CategoryTheory.toSheafify J ((PresheafOfModules.toPresheaf _).obj A))
  exact GrothendieckTopology.W_of_isLocallyBijective (J.over X)
    ((Over.forget X).op.whiskerLeft
      (CategoryTheory.toSheafify J ((PresheafOfModules.toPresheaf _).obj A)))

instance :
    IsIso ((sheafificationOver R X).map
      ((restrictPresheaf R X).map ((sheafificationAdjBase R).unit.app A))) := by
  have hW : ((J.over X).W.inverseImage (PresheafOfModules.toPresheaf _))
      ((restrictPresheaf R X).map ((sheafificationAdjBase R).unit.app A)) :=
    comparisonAdjoint_memW R X A
  exact Localization.inverts (sheafificationOver R X)
    ((J.over X).W.inverseImage (PresheafOfModules.toPresheaf _)) _ hW

omit [(J.W (A := Ab.{u})).IsMonoidal] [((J.over X).W (A := Ab.{u})).IsMonoidal] in
theorem comparisonAdjoint_map :
    (sheafificationOver R X).map (comparisonAdjoint R X A) =
      (sheafificationOver R X).map
          ((restrictPresheaf R X).map ((sheafificationAdjBase R).unit.app A)) ≫
        (sheafificationOver R X).map
          (forgetRestrictIso R X ((sheafificationBase R).obj A)).hom := by
  unfold comparisonAdjoint
  rw [Functor.map_comp]

instance : IsIso ((sheafificationOver R X).map (comparisonAdjoint R X A)) := by
  rw [comparisonAdjoint_map]
  infer_instance

instance : IsIso (comparisonHom R X A) := by
  rw [comparisonHom_eq]
  infer_instance

omit [(J.W (A := Ab.{u})).IsMonoidal] [((J.over X).W (A := Ab.{u})).IsMonoidal] in
theorem comparisonHom_natural {A B : PresheafOfModules.{u}
    (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})} (h : A ⟶ B) :
    (sheafificationOver R X).map ((restrictPresheaf R X).map h) ≫ comparisonHom R X B =
      comparisonHom R X A ≫ (restrictSheaf R X).map ((sheafificationBase R).map h) := by
  have hunit : h ≫ (sheafificationAdjBase R).unit.app B =
      (sheafificationAdjBase R).unit.app A ≫
          (forgetRestrictBase R).map ((sheafificationBase R).map h) := by
    have h0 := (sheafificationAdjBase R).unit.naturality h
    simp only [Functor.id_map, _root_.CategoryTheory.Functor.comp_map] at h0
    exact h0
  have hcounit : (sheafificationOver R X).map
      ((forgetRestrictOver R X).map ((restrictSheaf R X).map ((sheafificationBase R).map h))) ≫
        (sheafificationAdjOver R X).counit.app
            ((restrictSheaf R X).obj ((sheafificationBase R).obj B)) =
      (sheafificationAdjOver R X).counit.app
          ((restrictSheaf R X).obj ((sheafificationBase R).obj A)) ≫
        (restrictSheaf R X).map ((sheafificationBase R).map h) := by
    have h0 := (sheafificationAdjOver R X).counit.naturality
        ((restrictSheaf R X).map ((sheafificationBase R).map h))
    simp only [_root_.CategoryTheory.Functor.comp_map, Functor.id_map] at h0
    exact h0
  have key : (restrictPresheaf R X).map h ≫ comparisonAdjoint R X B =
      comparisonAdjoint R X A ≫
        (forgetRestrictOver R X).map ((restrictSheaf R X).map ((sheafificationBase R).map h)) := by
    unfold comparisonAdjoint
    rw [← Category.assoc _ _
      (forgetRestrictIso R X ((sheafificationBase R).obj B)).hom,
      ← Functor.map_comp, hunit, Functor.map_comp,
      Category.assoc _ (forgetRestrictIso R X ((sheafificationBase R).obj A)).hom _,
      forgetRestrictIso_naturality,
      Category.assoc]
  simp only [comparisonHom_eq, Category.assoc]
  conv_lhs => rw [← Category.assoc, ← Functor.map_comp, key, Functor.map_comp,
    Category.assoc]
  rw [hcounit]

/-- Restriction commutes with sheafification, through the natural isomorphism
`restrictPresheaf ⋙ sheafificationOver ≅ sheafificationBase ⋙ restrictSheaf`. -/
noncomputable def commIso : (restrictPresheaf R X) ⋙ (sheafificationOver R X) ≅
    (sheafificationBase R) ⋙ (restrictSheaf R X) :=
  _root_.CategoryTheory.NatIso.ofComponents (fun A => asIso (comparisonHom R X A))
    (fun {A B} h => by
    have hn := comparisonHom_natural R X h
    simpa only [_root_.CategoryTheory.Functor.comp_map, asIso_hom] using hn)

/-- Presheaf restriction is monoidal by precomposition. -/
noncomputable instance pfMonoidal : (restrictPresheaf R X).Monoidal :=
  inferInstanceAs
    ((PresheafOfModules.pushforward₀OfCommRingCat (Over.forget X) R.obj).Monoidal)

/-- The monoidal structure on module sheaves over the restricted commutative-ring sheaf. -/
noncomputable instance overMonoidalCategory :
    MonoidalCategory (SheafOfModules.{u} ((sheafComposeRing R).over X)) :=
  inferInstanceAs (MonoidalCategory (SheafOfModules.{u} (overSheafComposeRing R X)))

/-- Monoidal structure on sheaf restriction, by lifting along sheafification.

`restrictPresheaf ⋙ sheafificationOver` is monoidal (a composite of monoidal functors) and is
identified with `sheafificationBase ⋙ restrictSheaf` by `commIso`; the localization API
(`Localization.Monoidal.functorMonoidalOfComp`) then equips `restrictSheaf` with its
monoidal structure. All coherence comes from that construction rather than
being asserted by hand. Since `restrictSheaf` is the restriction (`over`) functor, this
is also the monoidal structure on restriction. -/
noncomputable instance ofMonoidal : (restrictSheaf R X).Monoidal := by
  haveI : (sheafificationBase R).Monoidal :=
    inferInstanceAs ((Localization.Monoidal.toMonoidalCategory (sheafificationBase R)
      (J.W.inverseImage
        (PresheafOfModules.toPresheaf (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})))
      (.refl _)).Monoidal)
  haveI : (sheafificationOver R X).Monoidal :=
    inferInstanceAs ((Localization.Monoidal.toMonoidalCategory (sheafificationOver R X)
      ((J.over X).W.inverseImage
        (PresheafOfModules.toPresheaf (overRing R X)))
      (.refl _)).Monoidal)
  haveI : Localization.Lifting (sheafificationBase R)
      (J.W.inverseImage
        (PresheafOfModules.toPresheaf (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})))
      (restrictPresheaf R X ⋙ sheafificationOver R X) (restrictSheaf R X) :=
    ⟨(commIso R X).symm⟩
  exact Localization.Monoidal.functorMonoidalOfComp (sheafificationBase R)
    (J.W.inverseImage
      (PresheafOfModules.toPresheaf (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})))
    (restrictSheaf R X) (restrictPresheaf R X ⋙ sheafificationOver R X)

/-- Monoidal structures restated for the tensor-chain proofs below.
These are the same terms as the proof-local `haveI`s in `ofMonoidal`;
they are needed at statement level for the comparison lemmas. -/
private noncomputable instance chainBaseMonoidal : (sheafificationBase R).Monoidal :=
  inferInstanceAs ((Localization.Monoidal.toMonoidalCategory (sheafificationBase R)
    (J.W.inverseImage
      (PresheafOfModules.toPresheaf (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})))
    (.refl _)).Monoidal)

private noncomputable instance chainOverMonoidal : (sheafificationOver R X).Monoidal :=
  inferInstanceAs ((Localization.Monoidal.toMonoidalCategory (sheafificationOver R X)
    ((J.over X).W.inverseImage
      (PresheafOfModules.toPresheaf (overRing R X)))
    (.refl _)).Monoidal)

private noncomputable instance chainLift :
    Localization.Lifting (sheafificationBase R)
      (J.W.inverseImage
        (PresheafOfModules.toPresheaf (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})))
      (restrictPresheaf R X ⋙ sheafificationOver R X) (restrictSheaf R X) :=
  ⟨(commIso R X).symm⟩

/-- Generic cancellation: from `p.symm ≪≫ X = Z` conclude `X = p ≪≫ Z`. -/
private theorem cancel_symm_left {D : Type*} [Category* D] {U V W : D}
    (p : U ≅ V) (X : U ≅ W) (Z : V ≅ W) (h : p.symm ≪≫ X = Z) :
    X = p ≪≫ Z := by
  calc X = p ≪≫ (p.symm ≪≫ X) := by simp
    _ = p ≪≫ Z := by rw [h]

/-- The structural `μIso` of sheafification is the localized `μ`. -/
private theorem μ_base_eq (A B : PresheafOfModules.{u}
    (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})) :
    (Functor.Monoidal.μIso (sheafificationBase R) A B) =
      Localization.Monoidal.μ (sheafificationBase R)
        (J.W.inverseImage
          (PresheafOfModules.toPresheaf (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})))
        (.refl _) A B := rfl

omit [(J.W (A := Ab.{u})).IsMonoidal] [J.WEqualsLocallyBijective Ab.{u}]
  [HasWeakSheafify J Ab.{u}] [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The structural `μIso` of sheafification over `X` is the localized `μ`. -/
private theorem μ_over_eq (A B : PresheafOfModules.{u} (overRing R X)) :
    (Functor.Monoidal.μIso (sheafificationOver R X) A B) =
      Localization.Monoidal.μ (sheafificationOver R X)
        ((J.over X).W.inverseImage
          (PresheafOfModules.toPresheaf (overRing R X)))
        (.refl _) A B := rfl

/-- Naturality square for `μIso (restrictSheaf R X)` along the sheafification
counits, as an isomorphism equation. -/
private theorem μIso_conj (M N : SheafOfModules.{u} (sheafComposeRing R)) :
    Functor.Monoidal.μIso (restrictSheaf R X) M N ≪≫
        (restrictSheaf R X).mapIso
          (MonoidalCategory.tensorIso
            (asIso ((sheafificationAdjBase R).counit.app M)).symm
            (asIso ((sheafificationAdjBase R).counit.app N)).symm) =
      MonoidalCategory.tensorIso
        ((restrictSheaf R X).mapIso
          (asIso ((sheafificationAdjBase R).counit.app M)).symm)
        ((restrictSheaf R X).mapIso
          (asIso ((sheafificationAdjBase R).counit.app N)).symm) ≪≫
      Functor.Monoidal.μIso (restrictSheaf R X) _ _ := by
  apply Iso.ext
  simp only [Iso.trans_hom, Functor.mapIso_hom, MonoidalCategory.tensorIso_hom,
    Functor.Monoidal.μIso_hom]
  exact (Functor.LaxMonoidal.μ_natural (restrictSheaf R X)
    (asIso ((sheafificationAdjBase R).counit.app M)).symm.hom
    (asIso ((sheafificationAdjBase R).counit.app N)).symm.hom).symm

/-- The lifted `μIso` at sheafified objects, unfolded via
`Localization.Monoidal.functorMonoidalOfComp_μ`. -/
private theorem μIso_sheafified (A B : PresheafOfModules.{u}
    (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})) :
    Functor.Monoidal.μIso (restrictSheaf R X)
      ((sheafificationBase R).obj A) ((sheafificationBase R).obj B) =
    MonoidalCategory.tensorIso
      (((commIso R X).symm).app A) (((commIso R X).symm).app B) ≪≫
    Functor.Monoidal.μIso
      (restrictPresheaf R X ⋙ sheafificationOver R X) A B ≪≫
    ((((commIso R X).symm).app (A ⊗ B)).symm) ≪≫
    ((restrictSheaf R X).mapIso
      (Functor.Monoidal.μIso (sheafificationBase R) A B)).symm := by
  have p6h : (Functor.Monoidal.μIso (restrictSheaf R X)
        ((sheafificationBase R).obj A) ((sheafificationBase R).obj B)).hom =
      (((commIso R X).symm.hom.app A) ⊗ₘ
        ((commIso R X).symm.hom.app B)) ≫
      (Functor.Monoidal.μIso
        (restrictPresheaf R X ⋙ sheafificationOver R X) A B).hom ≫
      ((commIso R X).symm.inv.app (A ⊗ B)) ≫
      (restrictSheaf R X).map
        (Functor.OplaxMonoidal.δ (sheafificationBase R) A B) :=
    Localization.Monoidal.functorMonoidalOfComp_μ
      (sheafificationBase R)
      (J.W.inverseImage
        (PresheafOfModules.toPresheaf (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})))
      (restrictSheaf R X)
      (restrictPresheaf R X ⋙ sheafificationOver R X) A B
  have qA : ((((commIso R X).symm).app A).hom) =
      (((commIso R X).symm.hom.app A)) := rfl
  have qB : ((((commIso R X).symm).app B).hom) =
      (((commIso R X).symm.hom.app B)) := rfl
  have qAB : (((((commIso R X).symm).app (A ⊗ B)).symm).hom) =
      (((commIso R X).symm.inv.app (A ⊗ B))) := rfl
  have qδ : (((Functor.Monoidal.μIso (sheafificationBase R) A B).symm.hom)) =
      (Functor.OplaxMonoidal.δ (sheafificationBase R) A B) := rfl
  apply Iso.ext
  simp only [Iso.trans_hom, Functor.mapIso_hom, MonoidalCategory.tensorIso_hom,
    Functor.Monoidal.μIso_hom, ← Functor.mapIso_symm]
  rw [qA, qB, qAB, qδ]
  exact p6h

omit [(J.W (A := Ab.{u})).IsMonoidal] [J.WEqualsLocallyBijective Ab.{u}]
  [HasWeakSheafify J Ab.{u}] [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The `μIso` of the composite `restrictPresheaf ⋙ sheafificationOver` splits. -/
private theorem μIso_comp (A B : PresheafOfModules.{u}
    (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})) :
    Functor.Monoidal.μIso
      (restrictPresheaf R X ⋙ sheafificationOver R X) A B =
    Functor.Monoidal.μIso (sheafificationOver R X) _ _ ≪≫
    (sheafificationOver R X).mapIso
      (Functor.Monoidal.μIso (restrictPresheaf R X) A B) := by
  apply Iso.ext
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.Monoidal.μIso_hom]
  rfl

/-- Unit comparison for restriction, from the lifted monoidal structure:
`restrictSheaf.obj 𝟙 ≅ 𝟙`. This is the canonical unit comparison (the symmetry
of `Functor.Monoidal.εIso` for the `ofMonoidal` instance). Together with
`ofTensorIso` this is the interface later dual arguments need (e.g. pushing an
evaluation `L ⊗ dual L ⟶ 𝟙` through restriction). -/
noncomputable def ofUnitIso :
    (restrictSheaf R X).obj (𝟙_ (SheafOfModules.{u} (sheafComposeRing R))) ≅
      𝟙_ (SheafOfModules.{u} (overSheafComposeRing R X)) :=
  (Functor.Monoidal.εIso (restrictSheaf R X)).symm

/-- Tensor comparison for restriction, in `restrictSheaf` spelling: the symmetry of
the structural `Functor.Monoidal.μIso` for the `ofMonoidal` instance,
so it agrees with the monoidal structure by definition. This is the single
canonical tensor comparison; its explicit counit/`μ`/`commIso` form is recorded
as `ofTensorIso_hom_eq` / `ofTensorIso_inv_eq` below. -/
noncomputable def ofTensorIso (M N : SheafOfModules.{u} (sheafComposeRing R)) :
    (restrictSheaf R X).obj (M ⊗ N) ≅ (restrictSheaf R X).obj M ⊗ (restrictSheaf R X).obj N :=
  (Functor.Monoidal.μIso (restrictSheaf R X) M N).symm

/-- The tensor comparison is the composite of the counit, monoidal multiplication
and the restriction-sheafification isomorphism `commIso`. -/
theorem ofTensorIso_symm_chain (M N : SheafOfModules.{u} (sheafComposeRing R)) :
    (Functor.Monoidal.μIso (restrictSheaf R X) M N).symm =
      (restrictSheaf R X).mapIso
        (MonoidalCategory.tensorIso
          (asIso ((sheafificationAdjBase R).counit.app M)).symm
          (asIso ((sheafificationAdjBase R).counit.app N)).symm) ≪≫
      (restrictSheaf R X).mapIso
        (Localization.Monoidal.μ (sheafificationBase R)
          (J.W.inverseImage
            (PresheafOfModules.toPresheaf (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})))
          (.refl _)
          ((forgetRestrictBase R).obj M)
          ((forgetRestrictBase R).obj N)) ≪≫
      (((commIso R X).app
        (((forgetRestrictBase R).obj M) ⊗
          ((forgetRestrictBase R).obj N))).symm) ≪≫
      (sheafificationOver R X).mapIso
        (Functor.Monoidal.μIso (restrictPresheaf R X)
          ((forgetRestrictBase R).obj M)
          ((forgetRestrictBase R).obj N)).symm ≪≫
      (Localization.Monoidal.μ (sheafificationOver R X)
        ((J.over X).W.inverseImage
          (PresheafOfModules.toPresheaf (overRing R X)))
        (.refl _)
        ((restrictPresheaf R X).obj ((forgetRestrictBase R).obj M))
        ((restrictPresheaf R X).obj ((forgetRestrictBase R).obj N))).symm ≪≫
      MonoidalCategory.tensorIso
        ((commIso R X).app ((forgetRestrictBase R).obj M))
        ((commIso R X).app ((forgetRestrictBase R).obj N)) ≪≫
      MonoidalCategory.tensorIso
        ((restrictSheaf R X).mapIso
          (asIso ((sheafificationAdjBase R).counit.app M)))
        ((restrictSheaf R X).mapIso
          (asIso ((sheafificationAdjBase R).counit.app N))) := by
  have sC := μIso_conj R X M N
  have hPsym : ((restrictSheaf R X).mapIso
            (MonoidalCategory.tensorIso
              (asIso ((sheafificationAdjBase R).counit.app M)).symm
              (asIso ((sheafificationAdjBase R).counit.app N)).symm)).symm ≪≫
        (Functor.Monoidal.μIso (restrictSheaf R X) M N).symm =
      (Functor.Monoidal.μIso (restrictSheaf R X)
        ((sheafificationBase R).obj ((forgetRestrictBase R).obj M))
        ((sheafificationBase R).obj ((forgetRestrictBase R).obj N))).symm ≪≫
        (MonoidalCategory.tensorIso
          ((restrictSheaf R X).mapIso
            (asIso ((sheafificationAdjBase R).counit.app M)).symm)
          ((restrictSheaf R X).mapIso
            (asIso ((sheafificationAdjBase R).counit.app N)).symm)).symm := by
    have h2 := congrArg Iso.symm sC
    simp only [Iso.trans_symm] at h2
    exact h2
  have hA : (Functor.Monoidal.μIso (restrictSheaf R X) M N).symm =
      (restrictSheaf R X).mapIso
        (MonoidalCategory.tensorIso
          (asIso ((sheafificationAdjBase R).counit.app M)).symm
          (asIso ((sheafificationAdjBase R).counit.app N)).symm) ≪≫
      (Functor.Monoidal.μIso (restrictSheaf R X)
        ((sheafificationBase R).obj ((forgetRestrictBase R).obj M))
        ((sheafificationBase R).obj ((forgetRestrictBase R).obj N))).symm ≪≫
      (MonoidalCategory.tensorIso
        ((restrictSheaf R X).mapIso
          (asIso ((sheafificationAdjBase R).counit.app M)).symm)
        ((restrictSheaf R X).mapIso
          (asIso ((sheafificationAdjBase R).counit.app N)).symm)).symm :=
    cancel_symm_left _ _ _ hPsym
  have hBsymm : (Functor.Monoidal.μIso (restrictSheaf R X)
        ((sheafificationBase R).obj ((forgetRestrictBase R).obj M))
        ((sheafificationBase R).obj ((forgetRestrictBase R).obj N))).symm =
      (restrictSheaf R X).mapIso
        (Functor.Monoidal.μIso (sheafificationBase R)
          ((forgetRestrictBase R).obj M) ((forgetRestrictBase R).obj N)) ≪≫
      (((commIso R X).symm).app
        (((forgetRestrictBase R).obj M) ⊗ ((forgetRestrictBase R).obj N))) ≪≫
      (Functor.Monoidal.μIso
        (restrictPresheaf R X ⋙ sheafificationOver R X)
        ((forgetRestrictBase R).obj M) ((forgetRestrictBase R).obj N)).symm ≪≫
      (MonoidalCategory.tensorIso
        (((commIso R X).symm).app ((forgetRestrictBase R).obj M))
        (((commIso R X).symm).app ((forgetRestrictBase R).obj N))).symm := by
    have h2 := congrArg Iso.symm (μIso_sheafified R X
      ((forgetRestrictBase R).obj M) ((forgetRestrictBase R).obj N))
    simp only [Iso.trans_symm, Iso.symm_symm_eq] at h2
    exact h2
  have hGsymm : (Functor.Monoidal.μIso
        (restrictPresheaf R X ⋙ sheafificationOver R X)
        ((forgetRestrictBase R).obj M) ((forgetRestrictBase R).obj N)).symm =
      ((sheafificationOver R X).mapIso
        (Functor.Monoidal.μIso (restrictPresheaf R X)
          ((forgetRestrictBase R).obj M) ((forgetRestrictBase R).obj N))).symm ≪≫
      (Functor.Monoidal.μIso (sheafificationOver R X)
        ((restrictPresheaf R X).obj ((forgetRestrictBase R).obj M))
        ((restrictPresheaf R X).obj ((forgetRestrictBase R).obj N))).symm := by
    have h2 := congrArg Iso.symm (μIso_comp R X
      ((forgetRestrictBase R).obj M) ((forgetRestrictBase R).obj N))
    simp only [Iso.trans_symm] at h2
    exact h2
  rw [hBsymm, hGsymm] at hA
  have pieceH2 : (restrictSheaf R X).mapIso
        (Functor.Monoidal.μIso (sheafificationBase R)
          ((forgetRestrictBase R).obj M) ((forgetRestrictBase R).obj N)) =
      (restrictSheaf R X).mapIso
        (Localization.Monoidal.μ (sheafificationBase R)
          (J.W.inverseImage
            (PresheafOfModules.toPresheaf (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})))
          (.refl _)
          ((forgetRestrictBase R).obj M) ((forgetRestrictBase R).obj N)) :=
    congrArg _ (μ_base_eq R
      ((forgetRestrictBase R).obj M) ((forgetRestrictBase R).obj N))
  have pieceH3 : ((((commIso R X).symm).app
        (((forgetRestrictBase R).obj M) ⊗ ((forgetRestrictBase R).obj N)))) =
      (((commIso R X).app
        (((forgetRestrictBase R).obj M) ⊗
          ((forgetRestrictBase R).obj N))).symm) := rfl
  have pieceH5 : (Functor.Monoidal.μIso (sheafificationOver R X)
        ((restrictPresheaf R X).obj ((forgetRestrictBase R).obj M))
        ((restrictPresheaf R X).obj ((forgetRestrictBase R).obj N))).symm =
      (Localization.Monoidal.μ (sheafificationOver R X)
        ((J.over X).W.inverseImage (PresheafOfModules.toPresheaf (overRing R X)))
        (.refl _)
        ((restrictPresheaf R X).obj ((forgetRestrictBase R).obj M))
        ((restrictPresheaf R X).obj ((forgetRestrictBase R).obj N))).symm :=
    congrArg Iso.symm (μ_over_eq R X
      ((restrictPresheaf R X).obj ((forgetRestrictBase R).obj M))
      ((restrictPresheaf R X).obj ((forgetRestrictBase R).obj N)))
  have pieceH6 : (MonoidalCategory.tensorIso
        (((commIso R X).symm).app ((forgetRestrictBase R).obj M))
        (((commIso R X).symm).app ((forgetRestrictBase R).obj N))).symm =
      MonoidalCategory.tensorIso
        ((commIso R X).app ((forgetRestrictBase R).obj M))
        ((commIso R X).app ((forgetRestrictBase R).obj N)) := rfl
  have pieceH7 : (MonoidalCategory.tensorIso
        ((restrictSheaf R X).mapIso
          (asIso ((sheafificationAdjBase R).counit.app M)).symm)
        ((restrictSheaf R X).mapIso
          (asIso ((sheafificationAdjBase R).counit.app N)).symm)).symm =
      MonoidalCategory.tensorIso
        ((restrictSheaf R X).mapIso
          (asIso ((sheafificationAdjBase R).counit.app M)))
        ((restrictSheaf R X).mapIso
          (asIso ((sheafificationAdjBase R).counit.app N))) := rfl
  rw [pieceH2, pieceH3, pieceH5, pieceH6, pieceH7] at hA
  exact hA

/-- The `hom` leg of the canonical tensor comparison, as the explicit
counit/`μ`/`commIso` composite. -/
theorem ofTensorIso_hom_eq (M N : SheafOfModules.{u} (sheafComposeRing R)) :
    (ofTensorIso R X M N).hom =
      ((restrictSheaf R X).mapIso
        (MonoidalCategory.tensorIso
          (asIso ((sheafificationAdjBase R).counit.app M)).symm
          (asIso ((sheafificationAdjBase R).counit.app N)).symm) ≪≫
      (restrictSheaf R X).mapIso
        (Localization.Monoidal.μ (sheafificationBase R)
          (J.W.inverseImage
            (PresheafOfModules.toPresheaf (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})))
          (.refl _)
          ((forgetRestrictBase R).obj M)
          ((forgetRestrictBase R).obj N)) ≪≫
      (((commIso R X).app
        (((forgetRestrictBase R).obj M) ⊗
          ((forgetRestrictBase R).obj N))).symm) ≪≫
      (sheafificationOver R X).mapIso
        (Functor.Monoidal.μIso (restrictPresheaf R X)
          ((forgetRestrictBase R).obj M)
          ((forgetRestrictBase R).obj N)).symm ≪≫
      (Localization.Monoidal.μ (sheafificationOver R X)
        ((J.over X).W.inverseImage (PresheafOfModules.toPresheaf (overRing R X)))
        (.refl _)
        ((restrictPresheaf R X).obj ((forgetRestrictBase R).obj M))
        ((restrictPresheaf R X).obj ((forgetRestrictBase R).obj N))).symm ≪≫
      MonoidalCategory.tensorIso
        ((commIso R X).app ((forgetRestrictBase R).obj M))
        ((commIso R X).app ((forgetRestrictBase R).obj N)) ≪≫
      MonoidalCategory.tensorIso
        ((restrictSheaf R X).mapIso
          (asIso ((sheafificationAdjBase R).counit.app M)))
        ((restrictSheaf R X).mapIso
          (asIso ((sheafificationAdjBase R).counit.app N)))).hom := by
  have h := congrArg Iso.hom (ofTensorIso_symm_chain R X M N)
  exact h

/-- The `inv` leg of the canonical tensor comparison, as the explicit
counit/`μ`/`commIso` composite in reverse. -/
theorem ofTensorIso_inv_eq (M N : SheafOfModules.{u} (sheafComposeRing R)) :
    (ofTensorIso R X M N).inv =
      ((restrictSheaf R X).mapIso
        (MonoidalCategory.tensorIso
          (asIso ((sheafificationAdjBase R).counit.app M)).symm
          (asIso ((sheafificationAdjBase R).counit.app N)).symm) ≪≫
      (restrictSheaf R X).mapIso
        (Localization.Monoidal.μ (sheafificationBase R)
          (J.W.inverseImage
            (PresheafOfModules.toPresheaf (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})))
          (.refl _)
          ((forgetRestrictBase R).obj M)
          ((forgetRestrictBase R).obj N)) ≪≫
      (((commIso R X).app
        (((forgetRestrictBase R).obj M) ⊗
          ((forgetRestrictBase R).obj N))).symm) ≪≫
      (sheafificationOver R X).mapIso
        (Functor.Monoidal.μIso (restrictPresheaf R X)
          ((forgetRestrictBase R).obj M)
          ((forgetRestrictBase R).obj N)).symm ≪≫
      (Localization.Monoidal.μ (sheafificationOver R X)
        ((J.over X).W.inverseImage (PresheafOfModules.toPresheaf (overRing R X)))
        (.refl _)
        ((restrictPresheaf R X).obj ((forgetRestrictBase R).obj M))
        ((restrictPresheaf R X).obj ((forgetRestrictBase R).obj N))).symm ≪≫
      MonoidalCategory.tensorIso
        ((commIso R X).app ((forgetRestrictBase R).obj M))
        ((commIso R X).app ((forgetRestrictBase R).obj N)) ≪≫
      MonoidalCategory.tensorIso
        ((restrictSheaf R X).mapIso
          (asIso ((sheafificationAdjBase R).counit.app M)))
        ((restrictSheaf R X).mapIso
          (asIso ((sheafificationAdjBase R).counit.app N)))).inv := by
  have h := congrArg Iso.inv (ofTensorIso_symm_chain R X M N)
  exact h

end RestrictSheafification

end SheafOfModules

end
