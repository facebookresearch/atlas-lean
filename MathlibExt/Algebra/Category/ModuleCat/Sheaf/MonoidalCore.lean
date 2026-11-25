/-
Copyright (c) 2026 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module







public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import MathlibExt.Algebra.Category.ModuleCat.Presheaf.MonoidalCompat
public import MathlibExt.Algebra.Category.ModuleCat.Presheaf.SheafificationCompat
public import MathlibExt.CategoryTheory.Localization.BousfieldCompat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# The monoidal structure on sheaves of modules
-/

universe u

open CategoryTheory MonoidalCategory TensorProduct

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}

/-- Additive maps from a tensor product agree if they agree on all pure tensors. -/
private theorem TensorProduct.extAdd {R : Type*} [CommSemiring R] {M N P₂ : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P₂] [Module R M] [Module R N]
    {F : Type*} [FunLike F (M ⊗[R] N) P₂] [AddMonoidHomClass F (M ⊗[R] N) P₂]
    {g h : F} (H : ∀ (x : M) (y : N), g (x ⊗ₜ y) = h (x ⊗ₜ y)) : g = h := by
  apply DFunLike.ext _ _ fun t ↦ t.inductionOn H fun x y ha hb ↦ by
    simp only [map_add, ha, hb]

/-- Additive maps from a threefold tensor product agree if they agree on
all pure tensors. -/
private theorem TensorProduct.ext_threefoldAdd {R R₂ : Type*} [CommSemiring R]
    [CommSemiring R₂] {M N M₂ P₃ : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid M₂] [AddCommMonoid P₃]
    [Module R M] [Module R N] [Module R₂ M₂]
    [Module R₂ M] [SMulCommClass R R₂ M]
    {F : Type*} [FunLike F (M ⊗[R] N ⊗[R₂] M₂) P₃]
    [AddMonoidHomClass F (M ⊗[R] N ⊗[R₂] M₂) P₃]
    {g h : F} (H : ∀ (x : M) (y : N) (z : M₂), g (x ⊗ₜ y ⊗ₜ z) = h (x ⊗ₜ y ⊗ₜ z)) :
    g = h := by
  apply TensorProduct.extAdd
  intro xy z
  induction xy using TensorProduct.inductionOn with
  | tmul m n => exact H m n z
  | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]

namespace PresheafOfModules

variable {R : Cᵒᵖ ⥤ CommRingCat.{u}} {M N P : PresheafOfModules.{u} (R ⋙ forget₂ ..)} {f : M ⟶ N}
variable [(J.W (A := Ab.{u})).IsMonoidal]

@[expose] public section

theorem W_toPresheaf_whiskerLeft (hf : J.W ((toPresheaf _).map f)) :
    J.W ((toPresheaf _).map (P ◁ f)) := by
  let pf := (toPresheaf _).map f
  refine ObjectProperty.isLocal_of_isColimit _ (colimitCoconeAb ..).2 (colimitCoconeAb ..).2
    (Limits.parallelPairHomMk (_ ◁ pf) (_ ◁ pf) ?_ ?_) _ ?_ ?_
  · ext U : 3; exact TensorProduct.ext_threefoldAdd fun _ _ _ ↦ rfl
  · ext U : 3; exact TensorProduct.ext_threefoldAdd fun p (r : R.obj U) m ↦ by
      exact congr(p ⊗ₜ $((f.app U).hom.map_smul r m))
  · ext (_ | _) U : 5
    · exact TensorProduct.ext_threefoldAdd fun _ _ _ ↦ rfl
    · exact TensorProduct.extAdd fun _ _ ↦ rfl
  · rintro (_ | _) <;> exact J.W.whiskerLeft_mem _ _ hf

theorem W_toPresheaf_whiskerRight (hf : J.W ((toPresheaf _).map f)) :
    J.W ((toPresheaf _).map (f ▷ P)) := by
  refine (J.W.arrow_mk_iso_iff <| Arrow.isoMk ((toPresheaf _).mapIso (β_ M P))
    ((toPresheaf _).mapIso (β_ N P)) ?_).2 (W_toPresheaf_whiskerLeft (P := P) hf)
  simp_rw [Arrow.mk, Arrow.hom, Functor.mapIso_hom]
  refine (Functor.map_comp ..).symm.trans (.trans ?_ (Functor.map_comp ..))
  congr 1; simp

instance : (J.W.inverseImage (toPresheaf (R ⋙ forget₂ ..))).IsMonoidal where
  whiskerLeft _ _ _ _ := W_toPresheaf_whiskerLeft
  whiskerRight _ h _ := W_toPresheaf_whiskerRight h

end

end PresheafOfModules

namespace SheafOfModules

@[expose] public section

variable (R : Sheaf J CommRingCat.{u})
variable [(J.W (A := Ab.{u})).IsMonoidal] [J.WEqualsLocallyBijective Ab.{u}]
variable [HasWeakSheafify J Ab.{u}] [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- The monoidal structure on the category of sheaves of modules over a sheaf of commutative
rings, obtained by localizing the monoidal category of presheaves of modules. -/
noncomputable instance monoidalCategory :
    MonoidalCategory (SheafOfModules.{u} ((sheafCompose J (forget₂ ..)).obj R)) :=
  inferInstanceAs <| MonoidalCategory <| LocalizedMonoidal
    (PresheafOfModules.sheafificationCommId R)
    (J.W.inverseImage (PresheafOfModules.toPresheaf _))
    (.refl _)

noncomputable instance symmetricCategory :
    SymmetricCategory (SheafOfModules.{u} ((sheafCompose J (forget₂ ..)).obj R)) :=
  inferInstanceAs <| SymmetricCategory <| LocalizedMonoidal
    (PresheafOfModules.sheafificationCommId R)
    (J.W.inverseImage (PresheafOfModules.toPresheaf _))
    (.refl _)

end

noncomputable section

variable {D : Type u} [SmallCategory D] (J : GrothendieckTopology D) (R : Sheaf J CommRingCat.{u})

example : MonoidalCategory (SheafOfModules.{u} ((sheafCompose J (forget₂ ..)).obj R)) :=
  inferInstance

example : SymmetricCategory (SheafOfModules.{u} ((sheafCompose J (forget₂ ..)).obj R)) :=
  inferInstance

end

end SheafOfModules
