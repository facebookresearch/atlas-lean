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
# Monoidal structure on sheaves of modules

Let `(C,J)` be a site and `R : Sheaf J CommRingCat.{u}`. Assume weak sheafification of
abelian-group-valued presheaves, the identification of its equivalences with locally bijective
maps, monoidality of the equivalence class `J.W`, and preservation of the sheaf condition by
`CommRingCat → RingCat`.

Localization of the monoidal category of module presheaves gives a monoidal structure on
module sheaves over the underlying ring sheaf of `R`. Tensor products are obtained by
sheafifying the presheaf tensor product. Additive extensionality on pure tensors and threefold
pure tensors supplies the equalities of tensor maps.
-/

universe u

open CategoryTheory MonoidalCategory TensorProduct

variable {C : Type*} [Category* C] {J : GrothendieckTopology C}

/-- Let `R` be a commutative semiring, `M,N` be `R`-semimodules with additive commutative monoids,
and `P₂` an additive commutative monoid. For any function-like type `F` of additive maps `M
⊗[R] N → P₂`, maps `g,h : F` satisfying `g(x ⊗ y)=h(x ⊗ y)` for every `x∈M`, `y∈N` are equal.
Scalar-linearity of the maps into `P₂` is not required. -/
private theorem TensorProduct.extAdd {R : Type*} [CommSemiring R] {M N P₂ : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P₂] [Module R M] [Module R N]
    {F : Type*} [FunLike F (M ⊗[R] N) P₂] [AddMonoidHomClass F (M ⊗[R] N) P₂]
    {g h : F} (H : ∀ (x : M) (y : N), g (x ⊗ₜ y) = h (x ⊗ₜ y)) : g = h := by
  apply DFunLike.ext _ _ fun t ↦ t.inductionOn H fun x y ha hb ↦ by
    simp only [map_add, ha, hb]

/-- Let `R,R₂` be commutative semirings, `M` an `R`- and `R₂`-semimodule with commuting scalar
actions, `N` an `R`-semimodule, and `M₂` an `R₂`-semimodule. All three underlying additive
monoids are commutative. For an additive commutative monoid `P₃` and a function-like type `F`
of additive maps `(M ⊗[R] N) ⊗[R₂] M₂ → P₃`, equality on every `(x ⊗ y) ⊗ z` implies equality
of `g,h : F`. The `R₂`-action on the first tensor product is induced through `M`. -/
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

/-- Let `C` be a category, `J` a Grothendieck topology, and `R : Sheaf J CommRingCat.{u}`. Assume
`J.W` on abelian presheaves is monoidal, `J.WEqualsLocallyBijective Ab.{u}`, `HasWeakSheafify
J Ab.{u}`, and `J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})`. Then
`SheafOfModules.{u}` over the underlying ring sheaf `(sheafCompose J (forget₂ ..)).obj R` is a
monoidal category, obtained by localizing tensor products of module presheaves. -/
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
