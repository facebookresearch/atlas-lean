/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from AxiomMath/Stacks (https://github.com/AxiomMath/Stacks),
revision c496df0d9beea9deaeabcea8492605f9a0a2313b, licensed under the Apache License,
Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0). The source files carry no
individual copyright or author notice.

* `StacksFrontier/Algebra/Category/ModuleCat/Presheaf/MonoidalClosed.lean`

Modifications: source-local imports replaced by MathlibExt and Mathlib, using the native
ring-sheaf forgetful functor; the tensor and internal-Hom operations are unchanged.
-/
module

public import MathlibExt.Algebra.Category.ModuleCat.PresheafTensorFormulae
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import Mathlib.CategoryTheory.Sites.SheafHom

/-!
# The internal hom of presheaves of modules, and monoidality of module sheafification

Let `R₀ : Cᵒᵖ ⥤ CommRingCat` be a presheaf of commutative rings. The category
`PresheafOfModules (R₀ ⋙ forget₂ CommRingCat RingCat)` carries a symmetric monoidal structure
whose tensor product is computed sectionwise, and `SheafOfModules` is the localization of
`PresheafOfModules` at the class `J.W.inverseImage (PresheafOfModules.toPresheaf _)` of
morphisms which are local isomorphisms of the underlying presheaves of abelian groups. To
transport the monoidal structure along that localization one needs that class to be *monoidal*,
i.e. stable under whiskering. That statement is not provable sectionwise, because tensoring is
not left exact; and the monoidality of `J.W` for presheaves of abelian groups does not transfer,
because `toPresheaf` is not a monoidal functor (its tensor product is over `ℤ`, while the module
tensor product is over `R₀`).

We prove the monoidality by constructing the internal hom of presheaves of modules, showing that
it is a sheaf whenever its target is, and running the argument through the tensor–hom
adjunction, as `Mathlib/CategoryTheory/Sites/Monoidal.lean` does for `Sheaf J A`.

## Main definitions

* `PresheafOfModules.coind M H`: for a presheaf of modules `M` and a presheaf of abelian groups
  `H`, the presheaf of modules `U ↦ Hom(M|_U, H|_U)` of additive maps; its underlying presheaf
  of types is `presheafHom`.
* `PresheafOfModules.ihom M N`: the internal hom, the sub-presheaf of modules of
  `coind M N.presheaf` consisting of the `R₀`-linear families.
* `PresheafOfModules.ihomHomEquiv`: the adjunction bijection `(M ⊗ L ⟶ N) ≃ (L ⟶ ihom M N)`.

## Main results

* `PresheafOfModules.isSheaf_coind`: the underlying presheaf of `coind M H` is a sheaf whenever
  `H` is.
* `PresheafOfModules.isSheaf_ihom`: the underlying presheaf of `ihom M N` is a sheaf whenever
  that of `N` is: linearity of a section is a local condition, and the ambient object is a sheaf.
* `PresheafOfModules.curry_naturality_left`: the adjunction bijection is natural in `L`.
* `PresheafOfModules.W_inverseImage_toPresheaf_eq_isLocal`: the localizing class of module
  sheafification is the class of morphisms left-orthogonal to the presheaves of modules whose
  underlying presheaf is a sheaf. This module-level reformulation makes the internal-hom
  argument available.
* `PresheafOfModules.isMonoidal_W_inverseImage_toPresheaf`: this class is monoidal.
-/

@[expose] public section

universe v u w
open CategoryTheory Opposite MonoidalCategory Limits

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{max u v w}}

section SmulPresheaf

variable (M : PresheafOfModules.{max u v w} R)

/-- Multiplication by `r : R.obj X`, as an endomorphism of the abelian group
`M.presheaf.obj X`. -/
noncomputable def smulPresheaf {X : Cᵒᵖ} (r : R.obj X) :
    M.presheaf.obj X ⟶ M.presheaf.obj X := ((M.obj X).smul r).asHom

/-- `M.smulPresheaf r` sends `m` to `r • m`. -/
@[simp] lemma smulPresheaf_apply {X : Cᵒᵖ} (r : R.obj X) (m : M.obj X) :
    M.smulPresheaf r m = r • m := rfl

/-- Multiplication by `0` is the zero morphism. -/
@[simp] lemma smulPresheaf_zero (X : Cᵒᵖ) : M.smulPresheaf (0 : R.obj X) = 0 :=
  congrArg End.asHom (map_zero (M.obj X).smul)

/-- Multiplication by `r + s` is the sum of the multiplications by `r` and by `s`. -/
lemma smulPresheaf_add {X : Cᵒᵖ} (r s : R.obj X) :
    M.smulPresheaf (r + s) = M.smulPresheaf r + M.smulPresheaf s :=
  congrArg End.asHom (map_add (M.obj X).smul r s)

/-- Multiplication by `r` followed by multiplication by `s` is multiplication by `s * r`. -/
lemma smulPresheaf_comm' {X : Cᵒᵖ} (r s : R.obj X) :
    M.smulPresheaf r ≫ M.smulPresheaf s = M.smulPresheaf (s * r) :=
  (congrArg End.asHom (map_mul (M.obj X).smul s r)).symm

end SmulPresheaf

section Coind

variable {R₀ : Cᵒᵖ ⥤ CommRingCat.{max u v w}}
  (M : PresheafOfModules.{max u v w} (R₀ ⋙ forget₂ CommRingCat RingCat))
  (H : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w})

/-- The sections of `coind M H` over `X`: the natural transformations from the restriction of
`M.presheaf` to `Over X.unop` to the restriction of `H`. -/
abbrev coindSections (X : Cᵒᵖ) : Type (max u v w) :=
  (Over.forget X.unop).op ⋙ M.presheaf ⟶ (Over.forget X.unop).op ⋙ H

/-- The action of `r : R₀.obj X` on a section `θ` of `coind M H` over `X`, precomposing each
component of `θ` with multiplication by the restriction of `r`. -/
noncomputable def coindSMul {X : Cᵒᵖ} (r : R₀.obj X) (θ : coindSections M H X) :
    coindSections M H X where
  app Y := M.smulPresheaf (R₀.map Y.unop.hom.op r) ≫ θ.app Y
  naturality {Y Z} φ := by
    have hw : (R₀.map Z.unop.hom.op) r
        = (R₀.map φ.unop.left.op) ((R₀.map Y.unop.hom.op) r) := by
      rw [← CategoryTheory.comp_apply, ← R₀.map_comp, ← op_comp, Over.w φ.unop]
    rw [Category.assoc, ← θ.naturality φ, hw]
    exact (M.smul_map_assoc (U := op Y.unop.left) (V := op Z.unop.left)
      φ.unop.left.op ((R₀.map Y.unop.hom.op) r) (θ.app Z)).symm

/-- The action of `R₀.obj X` on the sections of `coind M H` over `X`, given by `coindSMul`. -/
noncomputable instance (X : Cᵒᵖ) : SMul (R₀.obj X) (coindSections M H X) := ⟨coindSMul M H⟩

/-- The component of `r • θ` at `Y` is multiplication by the restriction of `r`, followed by
the component of `θ` at `Y`. -/
@[simp]
lemma coindSMul_app {X : Cᵒᵖ} (r : R₀.obj X) (θ : coindSections M H X)
    (Y : (Over X.unop)ᵒᵖ) :
    (r • θ).app Y = M.smulPresheaf (R₀.map Y.unop.hom.op r) ≫ θ.app Y := rfl

/-- The sections of `coind M H` over `X` form an `R₀.obj X`-module. -/
noncomputable instance (X : Cᵒᵖ) : Module (R₀.obj X) (coindSections M H X) where
  one_smul θ := by
    ext Y (m : M.obj (op Y.unop.left))
    change θ.app Y ((R₀.map Y.unop.hom.op (1 : R₀.obj X)) • m) = _
    rw [map_one, one_smul]
  mul_smul r s θ := by
    ext Y (m : M.obj (op Y.unop.left))
    change θ.app Y ((R₀.map Y.unop.hom.op (r * s)) • m)
      = θ.app Y ((R₀.map Y.unop.hom.op s) • (R₀.map Y.unop.hom.op r) • m)
    rw [map_mul, mul_comm, mul_smul]
  smul_zero r := by
    ext Y : 2
    rw [coindSMul_app, NatTrans.app_zero, comp_zero]
  smul_add r θ₁ θ₂ := by
    ext Y : 2
    rw [coindSMul_app, NatTrans.app_add, NatTrans.app_add, Preadditive.comp_add,
      coindSMul_app, coindSMul_app]
  add_smul r s θ := by
    ext Y : 2
    rw [coindSMul_app, NatTrans.app_add, map_add, M.smulPresheaf_add, Preadditive.add_comp,
      coindSMul_app, coindSMul_app]
  zero_smul θ := by
    ext Y : 2
    rw [coindSMul_app, map_zero, M.smulPresheaf_zero, zero_comp, NatTrans.app_zero]

/-- Restriction of a section of `coind` along `f`. -/
noncomputable def coindRestrict {X Y : Cᵒᵖ} (f : X ⟶ Y) (θ : coindSections M H X) :
    coindSections M H Y :=
  Functor.whiskerLeft (Over.map f.unop).op θ

/-- The component of `coindRestrict M H f θ` at `Z` is the component of `θ` at the image of
`Z` under `Over.map f.unop`. -/
@[simp]
lemma coindRestrict_app {X Y : Cᵒᵖ} (f : X ⟶ Y) (θ : coindSections M H X)
    (Z : (Over Y.unop)ᵒᵖ) :
    (coindRestrict M H f θ).app Z = θ.app (op ((Over.map f.unop).obj Z.unop)) := rfl

/-- The component of `coindRestrict M H f θ` at `Over.mk p` is the component of `θ` at
`Over.mk h`, for any `h` equal to `p ≫ f.unop`. -/
lemma coindRestrict_app_mk {X Y : Cᵒᵖ} (f : X ⟶ Y) {V : C} (p : V ⟶ Y.unop) (h : V ⟶ X.unop)
    (w : p ≫ f.unop = h) (θ : coindSections M H X) :
    (coindRestrict M H f θ).app (op (Over.mk p)) = θ.app (op (Over.mk h)) := by
  subst w
  rfl

/-- Restriction of sections of `coind M H` is additive. -/
lemma coindRestrict_add {X Y : Cᵒᵖ} (f : X ⟶ Y) (θ₁ θ₂ : coindSections M H X) :
    coindRestrict M H f (θ₁ + θ₂) = coindRestrict M H f θ₁ + coindRestrict M H f θ₂ := by
  ext Z : 2
  rw [coindRestrict_app, NatTrans.app_add, NatTrans.app_add, coindRestrict_app, coindRestrict_app]

/-- Restriction of sections of `coind M H` along `f` is semilinear with respect to
`R₀.map f`. -/
lemma coindRestrict_smul {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : R₀.obj X) (θ : coindSections M H X) :
    coindRestrict M H f (r • θ) = (R₀.map f r) • coindRestrict M H f θ := by
  ext Z : 2
  rw [coindRestrict_app, coindSMul_app, coindSMul_app, coindRestrict_app]
  congr 2
  change (R₀.map ((Over.map f.unop).obj Z.unop).hom.op) r = _
  rw [← CategoryTheory.comp_apply, ← R₀.map_comp]
  rfl

/-- The presheaf of abelian groups underlying `coind`. -/
noncomputable def coindPresheaf : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w} where
  obj X := AddCommGrpCat.of (coindSections M H X)
  map f := AddCommGrpCat.ofHom (AddMonoidHom.mk' (coindRestrict M H f) (coindRestrict_add M H f))
  map_id X := ConcreteCategory.hom_ext _ _ fun θ ↦
    ConcreteCategory.congr_hom ((presheafHom M.presheaf H).map_id X) θ
  map_comp f g := ConcreteCategory.hom_ext _ _ fun θ ↦
    ConcreteCategory.congr_hom ((presheafHom M.presheaf H).map_comp f g) θ

/-- The sections of `coindPresheaf M H` over `X` form an `R₀.obj X`-module. -/
noncomputable instance (X : Cᵒᵖ) : Module (R₀.obj X) ((coindPresheaf M H).obj X) :=
  inferInstanceAs (Module (R₀.obj X) (coindSections M H X))

/-- The sections of `coindPresheaf M H` over `X` form a module over
`(R₀ ⋙ forget₂ CommRingCat RingCat).obj X`. -/
noncomputable instance (X : Cᵒᵖ) :
    Module ((R₀ ⋙ forget₂ CommRingCat RingCat).obj X) ((coindPresheaf M H).obj X) :=
  inferInstanceAs (Module (R₀.obj X) (coindSections M H X))

/-- The presheaf of modules of additive maps from `M` to `H`, the right adjoint of `toPresheaf`. -/
noncomputable def coind : PresheafOfModules.{max u v w} (R₀ ⋙ forget₂ CommRingCat RingCat) :=
  ofPresheaf (coindPresheaf M H) (fun {_ _} f r θ ↦ coindRestrict_smul M H f r θ)

/-- The underlying presheaf of abelian groups of `coind M H` is `coindPresheaf M H`. -/
@[simp] lemma coind_presheaf : (coind M H).presheaf = coindPresheaf M H := rfl

/-- The sections of `coind M H` over `X` are `coindSections M H X`. -/
@[simp] lemma coind_obj_coe (X : Cᵒᵖ) : ((coind M H).obj X : Type _) = coindSections M H X := rfl

/-- The restriction maps of `coind M H` are given by `coindRestrict`. -/
@[simp] lemma coind_map_apply {X Y : Cᵒᵖ} (f : X ⟶ Y) (θ : coindSections M H X) :
    (coind M H).map f θ = coindRestrict M H f θ := rfl

/-- A presheaf of abelian groups whose underlying presheaf of types is a sheaf is a sheaf. -/
private lemma isSheaf_of_forget_eq {J : GrothendieckTopology C}
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}} {G : Cᵒᵖ ⥤ Type max u v w}
    (h : F ⋙ forget AddCommGrpCat = G) (hG : Presheaf.IsSheaf J G) :
    Presheaf.IsSheaf J F :=
  (Presheaf.isSheaf_iff_isSheaf_comp J F (forget AddCommGrpCat)).2 (h ▸ hG)

/-- The underlying presheaf of `coind M H` is a sheaf as soon as `H` is. -/
lemma isSheaf_coind {J : GrothendieckTopology C} (hH : Presheaf.IsSheaf J H) :
    Presheaf.IsSheaf J (coind M H).presheaf := by
  exact isSheaf_of_forget_eq (F := (coind M H).presheaf) rfl
    (Presheaf.IsSheaf.hom M.presheaf H hH)

end Coind

section Ihom

variable {R₀ : Cᵒᵖ ⥤ CommRingCat.{max u v w}}
  (M N : PresheafOfModules.{max u v w} (R₀ ⋙ forget₂ CommRingCat RingCat))

/-- Over a presheaf of commutative rings, multiplications by two sections commute. -/
lemma smulPresheaf_comm (M : PresheafOfModules.{max u v w} (R₀ ⋙ forget₂ CommRingCat RingCat))
    {X : Cᵒᵖ} (r s : (R₀ ⋙ forget₂ CommRingCat RingCat).obj X) :
    M.smulPresheaf r ≫ M.smulPresheaf s = M.smulPresheaf s ≫ M.smulPresheaf r := by
  rw [M.smulPresheaf_comm', M.smulPresheaf_comm', mul_comm]

/-- A section of `coind M N.presheaf` is *linear* when its components commute with the
multiplication by sections of the structure presheaf of rings. -/
def IsLinearSection {X : Cᵒᵖ} (θ : coindSections M N.presheaf X) : Prop :=
  ∀ (Y : (Over X.unop)ᵒᵖ) (r : (R₀ ⋙ forget₂ CommRingCat RingCat).obj (op Y.unop.left)),
    M.smulPresheaf r ≫ θ.app Y = θ.app Y ≫ N.smulPresheaf r

/-- The sum of two linear sections is linear. -/
lemma isLinearSection_add {X : Cᵒᵖ} {θ₁ θ₂ : coindSections M N.presheaf X}
    (h₁ : IsLinearSection M N θ₁) (h₂ : IsLinearSection M N θ₂) :
    IsLinearSection M N (θ₁ + θ₂) := fun Y r ↦ by
  rw [NatTrans.app_add, Preadditive.comp_add, Preadditive.add_comp, h₁ Y r, h₂ Y r]

/-- The zero section is linear. -/
lemma isLinearSection_zero (X : Cᵒᵖ) :
    IsLinearSection M N (0 : coindSections M N.presheaf X) := fun Y r ↦ by
  simp

/-- A scalar multiple of a linear section is linear. -/
lemma isLinearSection_smul {X : Cᵒᵖ} (s : R₀.obj X) {θ : coindSections M N.presheaf X}
    (h : IsLinearSection M N θ) : IsLinearSection M N (s • θ) := fun Y r ↦ by
  rw [coindSMul_app, ← Category.assoc, M.smulPresheaf_comm, Category.assoc, h Y r,
    Category.assoc]

/-- The restriction of a linear section is linear. -/
lemma isLinearSection_restrict {X Y : Cᵒᵖ} (f : X ⟶ Y) {θ : coindSections M N.presheaf X}
    (h : IsLinearSection M N θ) : IsLinearSection M N (coindRestrict M N.presheaf f θ) :=
  fun Z r ↦ h (op ((Over.map f.unop).obj Z.unop)) r

/-- The submodule of `coind M N.presheaf` given by the linear sections. -/
noncomputable def ihomSubmodule : (coind M N.presheaf).Submodule where
  obj X :=
    { carrier := {θ | IsLinearSection M N θ}
      add_mem' := fun h₁ h₂ ↦ isLinearSection_add M N h₁ h₂
      zero_mem' := isLinearSection_zero M N X
      smul_mem' := fun s _ h ↦ isLinearSection_smul M N s h }
  map f := fun _ h ↦ isLinearSection_restrict M N f h

/-- The internal hom of presheaves of modules. -/
noncomputable def ihom : PresheafOfModules.{max u v w} (R₀ ⋙ forget₂ CommRingCat RingCat) :=
  (ihomSubmodule M N).toPresheafOfModules

/-- The subfunctor of `presheafHom M.presheaf N.presheaf` given by the linear sections. -/
def ihomSubfunctor : Subfunctor (presheafHom M.presheaf N.presheaf) where
  obj _X := {θ | IsLinearSection M N θ}
  map f _ h := isLinearSection_restrict M N f h

variable {J : GrothendieckTopology C}

/-- Linearity of a section of `coind M N.presheaf` is a local property, as soon as the
underlying presheaf of `N` is a sheaf. -/
lemma isLinearSection_of_sieveOfSection_mem (hN : Presheaf.IsSheaf J N.presheaf) {X : Cᵒᵖ}
    (θ : coindSections M N.presheaf X)
    (hS : (ihomSubfunctor M N).sieveOfSection θ ∈ J X.unop) :
    IsLinearSection M N θ := by
  intro Y r
  refine hN.hom_ext ⟨Sieve.pullback Y.unop.hom ((ihomSubfunctor M N).sieveOfSection θ),
    J.pullback_stable _ hS⟩ _ _ (fun I ↦ ?_)
  have hlin : IsLinearSection M N (coindRestrict M N.presheaf (I.f ≫ Y.unop.hom).op θ) := I.hf
  have h1 := hlin (op (Over.mk (𝟙 I.Y)))
    (((R₀ ⋙ forget₂ CommRingCat RingCat).map I.f.op) r)
  rw [coindRestrict_app_mk M N.presheaf (I.f ≫ Y.unop.hom).op (𝟙 I.Y) (I.f ≫ Y.unop.hom)
    (Category.id_comp _)] at h1
  have hnat : M.presheaf.map I.f.op ≫ θ.app (op (Over.mk (I.f ≫ Y.unop.hom)))
      = θ.app Y ≫ N.presheaf.map I.f.op :=
    θ.naturality (Over.homMk I.f (by simp) : Over.mk (I.f ≫ Y.unop.hom) ⟶ Y.unop).op
  rw [Category.assoc, Category.assoc,
    show N.smulPresheaf _ ≫ _ = _ ≫ N.smulPresheaf _ from N.smul_map _ _,
    ← Category.assoc (θ.app Y), ← hnat, Category.assoc, ← h1]
  exact M.smul_map_assoc _ _ _

/-- The underlying presheaf of `ihom M N` is a sheaf as soon as that of `N` is. -/
lemma isSheaf_ihom (hN : Presheaf.IsSheaf J N.presheaf) :
    Presheaf.IsSheaf J (ihom M N).presheaf := by
  refine isSheaf_of_forget_eq (G := (ihomSubfunctor M N).toFunctor) rfl ?_
  rw [CategoryTheory.isSheaf_iff_isSheaf_of_type]
  refine (Subfunctor.isSheaf_iff _ ?_).2 (fun X θ hθ ↦
    isLinearSection_of_sieveOfSection_mem M N hN θ hθ)
  rw [← CategoryTheory.isSheaf_iff_isSheaf_of_type]
  exact Presheaf.IsSheaf.hom M.presheaf N.presheaf hN

end Ihom

section Adjunction

variable {R₀ : Cᵒᵖ ⥤ CommRingCat.{max u v w}}
  {M N L : PresheafOfModules.{max u v w} (R₀ ⋙ forget₂ CommRingCat RingCat)}

/-- The `AddCommGrpCat`-morphism underlying a morphism of modules. -/
noncomputable def ofModuleHom {X : Cᵒᵖ} (f : M.obj X ⟶ N.obj X) :
    M.presheaf.obj X ⟶ N.presheaf.obj X :=
  (forget₂ (ModuleCat ((R₀ ⋙ forget₂ CommRingCat RingCat).obj X)) AddCommGrpCat).map f

/-- `ofModuleHom f` acts on elements as `f`. -/
@[simp] lemma ofModuleHom_apply {X : Cᵒᵖ} (f : M.obj X ⟶ N.obj X) (m : M.obj X) :
    ofModuleHom f m = f m := rfl

/-- The morphism of modules `m ↦ m ⊗ₜ l`. -/
noncomputable def tmulRight
    (M L : PresheafOfModules.{max u v w} (R₀ ⋙ forget₂ CommRingCat RingCat)) {X : Cᵒᵖ}
    (l : L.obj X) : M.obj X ⟶ (M ⊗ L).obj X :=
  (ModuleCat.ofHom (R := R₀.obj X) ((TensorProduct.mk (R₀.obj X)
    (PresheafOfModulesOfCommRing.obj M X) (PresheafOfModulesOfCommRing.obj L X)).flip l) :
    PresheafOfModulesOfCommRing.obj M X ⟶ PresheafOfModulesOfCommRing.obj (M ⊗ L) X)

/-- `tmulRight M L l` sends `m` to `m ⊗ₜ l`. -/
@[simp] lemma tmulRight_apply
    (M L : PresheafOfModules.{max u v w} (R₀ ⋙ forget₂ CommRingCat RingCat)) {X : Cᵒᵖ}
    (l : L.obj X) (m : M.obj X) : tmulRight M L l m = m ⊗ₜ l := rfl

/-- The section of `coind M N.presheaf` over `X` attached to `α : M ⊗ L ⟶ N` and `l`. -/
noncomputable def curryApp (α : M ⊗ L ⟶ N) {X : Cᵒᵖ} (l : L.obj X) :
    coindSections M N.presheaf X where
  app Y := ofModuleHom (tmulRight M L (L.restrictₛₗ Y.unop.hom.op l) ≫ α.app (op Y.unop.left))
  naturality {Y Z} φ := by
    ext (m : M.obj (op Y.unop.left))
    have hz : Z.unop.hom.op = Y.unop.hom.op ≫ φ.unop.left.op := by
      rw [← op_comp, Over.w φ.unop]
    refine Eq.trans ?_ (naturality_apply α φ.unop.left.op
      (m ⊗ₜ (L.restrictₛₗ Y.unop.hom.op l)))
    have hl : (L.restrictₛₗ Z.unop.hom.op) l
        = (L.restrictₛₗ φ.unop.left.op) ((L.restrictₛₗ Y.unop.hom.op) l) := by
      rw [restrictₛₗ_apply, restrictₛₗ_apply, restrictₛₗ_apply, hz, L.map_comp_apply]
    change α.app (op Z.unop.left) ((M.restrictₛₗ φ.unop.left.op m) ⊗ₜ
        (L.restrictₛₗ Z.unop.hom.op l)) = _
    exact congrArg _ ((congrArg (fun x ↦ (M.restrictₛₗ φ.unop.left.op m) ⊗ₜ x) hl).trans
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul φ.unop.left.op m
        (L.restrictₛₗ Y.unop.hom.op l)).symm)

/-- The component of `curryApp α l` at `Y` sends `m` to `α` applied to `m` tensored with the
restriction of `l`. -/
@[simp] lemma curryApp_app_apply (α : M ⊗ L ⟶ N) {X : Cᵒᵖ} (l : L.obj X)
    (Y : (Over X.unop)ᵒᵖ) (m : M.obj (op Y.unop.left)) :
    (curryApp α l).app Y m
      = α.app (op Y.unop.left) (m ⊗ₜ (L.restrictₛₗ Y.unop.hom.op l)) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The section `curryApp α l` is linear. -/
lemma isLinearSection_curryApp (α : M ⊗ L ⟶ N) {X : Cᵒᵖ} (l : L.obj X) :
    IsLinearSection M N (curryApp α l) := fun Y r ↦ by
  ext (m : M.obj (op Y.unop.left))
  change α.app (op Y.unop.left) ((r • m) ⊗ₜ (L.restrictₛₗ Y.unop.hom.op l))
    = r • α.app (op Y.unop.left) (m ⊗ₜ (L.restrictₛₗ Y.unop.hom.op l))
  have h2 : α.app (op Y.unop.left)
        (r • (show (M ⊗ L).obj (op Y.unop.left) from m ⊗ₜ (L.restrictₛₗ Y.unop.hom.op l)))
      = r • α.app (op Y.unop.left) (m ⊗ₜ (L.restrictₛₗ Y.unop.hom.op l)) := map_smul _ _ _
  exact (congrArg _ (TensorProduct.smul_tmul' (R := R₀.obj (op Y.unop.left))
    (R' := R₀.obj (op Y.unop.left)) (M := PresheafOfModulesOfCommRing.obj M (op Y.unop.left))
    (N := PresheafOfModulesOfCommRing.obj L (op Y.unop.left))
    r m (L.restrictₛₗ Y.unop.hom.op l))).trans h2

/-- `curryApp α` is additive. -/
lemma curryApp_add (α : M ⊗ L ⟶ N) {X : Cᵒᵖ} (l₁ l₂ : L.obj X) :
    curryApp α (l₁ + l₂) = curryApp α l₁ + curryApp α l₂ := by
  ext Y (m : M.obj (op Y.unop.left))
  change α.app (op Y.unop.left) (m ⊗ₜ (L.restrictₛₗ Y.unop.hom.op (l₁ + l₂)))
    = α.app (op Y.unop.left) (m ⊗ₜ (L.restrictₛₗ Y.unop.hom.op l₁))
      + α.app (op Y.unop.left) (m ⊗ₜ (L.restrictₛₗ Y.unop.hom.op l₂))
  have h2 : α.app (op Y.unop.left) ((m ⊗ₜ (L.restrictₛₗ Y.unop.hom.op l₁))
        + (m ⊗ₜ (L.restrictₛₗ Y.unop.hom.op l₂)))
      = α.app (op Y.unop.left) (m ⊗ₜ (L.restrictₛₗ Y.unop.hom.op l₁))
        + α.app (op Y.unop.left) (m ⊗ₜ (L.restrictₛₗ Y.unop.hom.op l₂)) := map_add _ _ _
  exact (congrArg _
    ((congrArg (fun x ↦ m ⊗ₜ x) (map_add (L.restrictₛₗ Y.unop.hom.op) l₁ l₂)).trans
      (TensorProduct.tmul_add m _ _))).trans h2

set_option backward.isDefEq.respectTransparency false in
/-- `curryApp α` commutes with scalar multiplication. -/
lemma curryApp_smul (α : M ⊗ L ⟶ N) {X : Cᵒᵖ} (r : R₀.obj X) (l : L.obj X) :
    curryApp α (r • l) = r • curryApp α l := by
  ext Y (m : M.obj (op Y.unop.left))
  change α.app (op Y.unop.left) (m ⊗ₜ (L.restrictₛₗ Y.unop.hom.op (r • l)))
    = α.app (op Y.unop.left)
        (((R₀ ⋙ forget₂ CommRingCat RingCat).map Y.unop.hom.op r • m) ⊗ₜ
          (L.restrictₛₗ Y.unop.hom.op l))
  exact congrArg _
    ((congrArg (fun x ↦ m ⊗ₜ x) (map_smulₛₗ (L.restrictₛₗ Y.unop.hom.op) r l)).trans
      (TensorProduct.smul_tmul (R := R₀.obj (op Y.unop.left)) (R' := R₀.obj (op Y.unop.left))
        (M := PresheafOfModulesOfCommRing.obj M (op Y.unop.left))
        (N := PresheafOfModulesOfCommRing.obj L (op Y.unop.left))
        ((R₀ ⋙ forget₂ CommRingCat RingCat).map Y.unop.hom.op r) m
        (L.restrictₛₗ Y.unop.hom.op l)).symm)

/-- `curryApp α` commutes with restriction along `f`. -/
lemma curryApp_restrict (α : M ⊗ L ⟶ N) {X Y : Cᵒᵖ} (f : X ⟶ Y) (l : L.obj X) :
    curryApp α (L.restrictₛₗ f l) = coindRestrict M N.presheaf f (curryApp α l) := by
  ext Z (m : M.obj (op Z.unop.left))
  have hl : (L.restrictₛₗ Z.unop.hom.op) ((L.restrictₛₗ f) l)
      = (L.restrictₛₗ ((Over.map f.unop).obj Z.unop).hom.op) l := by
    rw [restrictₛₗ_apply, restrictₛₗ_apply, restrictₛₗ_apply, ← L.map_comp_apply]
    exact L.congr_map_apply (by simp) l
  change α.app (op Z.unop.left) (m ⊗ₜ (L.restrictₛₗ Z.unop.hom.op ((L.restrictₛₗ f) l))) = _
  exact congrArg _ (congrArg (fun x ↦ m ⊗ₜ x) hl)

/-- The bijection `(M ⊗ L ⟶ N) ≃ (L ⟶ ihom M N)`, forward direction. -/
noncomputable def curry (α : M ⊗ L ⟶ N) : L ⟶ ihom M N where
  app X := ModuleCat.ofHom (LinearMap.codRestrict ((ihomSubmodule M N).obj X)
    { toFun := curryApp α
      map_add' := curryApp_add α
      map_smul' := curryApp_smul α }
    (fun l ↦ isLinearSection_curryApp α l))
  naturality {X Y} f := by
    ext (l : L.obj X)
    exact Subtype.ext (curryApp_restrict α f l)

/-- The section of `coind M N.presheaf` underlying `(curry α).app X l` is `curryApp α l`. -/
@[simp] lemma curry_app_coe (α : M ⊗ L ⟶ N) (X : Cᵒᵖ) (l : L.obj X) :
    ((curry α).app X l).1 = curryApp α l := rfl

/-- The section of `coind M N.presheaf` underlying an element of `ihom M N`. -/
def ihomVal {X : Cᵒᵖ} (θ : (ihom M N).obj X) : coindSections M N.presheaf X := θ.1

/-- The section underlying the restriction of `θ` along `f` is the restriction of the section
underlying `θ`. -/
lemma ihomVal_map {X Y : Cᵒᵖ} (f : X ⟶ Y) (θ : (ihom M N).obj X) :
    ihomVal ((ihom M N).map f θ) = coindRestrict M N.presheaf f (ihomVal θ) := rfl

/-- Evaluation of a section `θ` of `ihom M N` over `X` at `m : M.obj X`, through the component
of `θ` at the identity of `X.unop`: this is the counit of the adjunction, read off on
sections. -/
noncomputable def ihomEval {X : Cᵒᵖ} (θ : (ihom M N).obj X) (m : M.obj X) : N.obj X :=
  (ihomVal θ).app (op (Over.mk (𝟙 X.unop))) m

/-- `ihomEval θ m` is the component of `ihomVal θ` at the identity, applied to `m`. -/
lemma ihomEval_def {X : Cᵒᵖ} (θ : (ihom M N).obj X) (m : M.obj X) :
    ihomEval θ m = (ihomVal θ).app (op (Over.mk (𝟙 X.unop))) m := rfl

/-- `ihomEval θ` is additive. -/
lemma ihomEval_add_left {X : Cᵒᵖ} (θ : (ihom M N).obj X) (m₁ m₂ : M.obj X) :
    ihomEval θ (m₁ + m₂) = ihomEval θ m₁ + ihomEval θ m₂ :=
  map_add _ _ _

/-- `ihomEval θ` commutes with scalar multiplication. -/
lemma ihomEval_smul_left {X : Cᵒᵖ} (θ : (ihom M N).obj X)
    (c : (R₀ ⋙ forget₂ CommRingCat RingCat).obj X) (m : M.obj X) :
    ihomEval θ (c • m) = c • ihomEval θ m :=
  ConcreteCategory.congr_hom (θ.2 (op (Over.mk (𝟙 X.unop))) c) m

/-- `ihomEval` is additive in the section. -/
lemma ihomEval_add_right {X : Cᵒᵖ} (θ₁ θ₂ : (ihom M N).obj X) (m : M.obj X) :
    ihomEval (θ₁ + θ₂) m = ihomEval θ₁ m + ihomEval θ₂ m := rfl

/-- `ihomEval` commutes with scalar multiplication of the section. -/
lemma ihomEval_smul_right {X : Cᵒᵖ} (c : (R₀ ⋙ forget₂ CommRingCat RingCat).obj X)
    (θ : (ihom M N).obj X) (m : M.obj X) :
    ihomEval (c • θ) m = c • ihomEval θ m := by
  change θ.1.app (op (Over.mk (𝟙 X.unop)))
      (((R₀ ⋙ forget₂ CommRingCat RingCat).map (𝟙 X.unop).op c) • m) = _
  have hc : (R₀ ⋙ forget₂ CommRingCat RingCat).map (𝟙 X.unop).op c = c :=
    ConcreteCategory.congr_hom ((R₀ ⋙ forget₂ CommRingCat RingCat).map_id X) c
  exact (congrArg _ (congrArg (fun r ↦ r • m) hc)).trans (ihomEval_smul_left θ c m)

/-- The bijection `(M ⊗ L ⟶ N) ≃ (L ⟶ ihom M N)`, backward direction. -/
noncomputable def uncurry (β : L ⟶ ihom M N) : M ⊗ L ⟶ N where
  app X := ModuleCat.MonoidalCategory.tensorLift
    (fun (m : M.obj X) (l : L.obj X) ↦ ihomEval (β.app X l) m)
    (fun m₁ m₂ l ↦ ihomEval_add_left _ _ _)
    (fun c m l ↦ ihomEval_smul_left _ _ _)
    (fun m l₁ l₂ ↦ by rw [map_add]; exact ihomEval_add_right _ _ _)
    (fun c m l ↦ by rw [map_smul]; exact ihomEval_smul_right _ _ _)
  naturality {X Y} f := ModuleCat.MonoidalCategory.tensor_ext (fun m l ↦ by
    have hβ : ihomVal (β.app Y (L.restrictₛₗ f l))
        = coindRestrict M N.presheaf f (ihomVal (β.app X l)) :=
      (congrArg _ (naturality_apply β f l)).trans (ihomVal_map f (β.app X l))
    have hnat : M.presheaf.map f ≫ (ihomVal (β.app X l)).app (op (Over.mk f.unop))
        = (ihomVal (β.app X l)).app (op (Over.mk (𝟙 X.unop))) ≫ N.presheaf.map f :=
      (ihomVal (β.app X l)).naturality
        (Over.homMk f.unop (by simp) : Over.mk f.unop ⟶ Over.mk (𝟙 X.unop)).op
    change ihomEval (β.app Y (L.restrictₛₗ f l)) (M.restrictₛₗ f m)
      = N.restrictₛₗ f (ihomEval (β.app X l) m)
    rw [ihomEval_def, hβ]
    exact (ConcreteCategory.congr_hom (coindRestrict_app_mk M N.presheaf f (𝟙 Y.unop) f.unop
      (Category.id_comp _) (ihomVal (β.app X l))) (M.restrictₛₗ f m)).trans
      (ConcreteCategory.congr_hom hnat m))

/-- `uncurry β` sends `m ⊗ₜ l` to the evaluation of `β.app X l` at `m`. -/
@[simp] lemma uncurry_app_tmul (β : L ⟶ ihom M N) (X : Cᵒᵖ) (m : M.obj X) (l : L.obj X) :
    (uncurry β).app X (m ⊗ₜ l) = ihomEval (β.app X l) m := rfl

/-- `uncurry` is a left inverse of `curry`. -/
lemma uncurry_curry (α : M ⊗ L ⟶ N) : uncurry (curry α) = α := by
  ext X : 1
  refine ModuleCat.MonoidalCategory.tensor_ext (fun m l ↦ ?_)
  change α.app X (m ⊗ₜ (L.restrictₛₗ (𝟙 X.unop).op l)) = α.app X (m ⊗ₜ l)
  exact congrArg _ (congrArg (fun x ↦ m ⊗ₜ x)
    ((restrictₛₗ_apply L (𝟙 X) l).trans (ConcreteCategory.congr_hom (L.map_id X) l)))

/-- `uncurry` is a right inverse of `curry`. -/
lemma curry_uncurry (β : L ⟶ ihom M N) : curry (uncurry β) = β := by
  ext X (l : L.obj X)
  refine Subtype.ext ?_
  change (_ : coindSections M N.presheaf X) = _
  ext Y (m : M.obj (op Y.unop.left))
  have hβ : ihomVal (β.app (op Y.unop.left) (L.restrictₛₗ Y.unop.hom.op l))
      = coindRestrict M N.presheaf Y.unop.hom.op (ihomVal (β.app X l)) :=
    (congrArg _ (naturality_apply β Y.unop.hom.op l)).trans
      (ihomVal_map Y.unop.hom.op (β.app X l))
  change ihomEval (β.app (op Y.unop.left) (L.restrictₛₗ Y.unop.hom.op l)) m
    = (ihomVal (β.app X l)).app Y m
  rw [ihomEval_def, hβ]
  exact ConcreteCategory.congr_hom (coindRestrict_app_mk M N.presheaf Y.unop.hom.op
    (𝟙 Y.unop.left) Y.unop.hom (Category.id_comp _) (ihomVal (β.app X l))) m

/-- `M ◁ g` sends `m ⊗ₜ y` to `m ⊗ₜ g.app X y`. -/
lemma whiskerLeft_app_tmul {L' : PresheafOfModules.{max u v w} (R₀ ⋙ forget₂ CommRingCat RingCat)}
    (g : L' ⟶ L) (X : Cᵒᵖ) (m : M.obj X) (y : L'.obj X) :
    (M ◁ g).app X (m ⊗ₜ y) = m ⊗ₜ g.app X y := rfl

/-- `curry` is natural in `L`: `curry ((M ◁ g) ≫ α) = g ≫ curry α`. -/
lemma curry_naturality_left
    {L' : PresheafOfModules.{max u v w} (R₀ ⋙ forget₂ CommRingCat RingCat)}
    (g : L' ⟶ L) (α : M ⊗ L ⟶ N) : curry ((M ◁ g) ≫ α) = g ≫ curry α := by
  ext X (l : L'.obj X)
  refine Subtype.ext ?_
  change (_ : coindSections M N.presheaf X) = _
  ext Y (m : M.obj (op Y.unop.left))
  change α.app (op Y.unop.left) ((M ◁ g).app (op Y.unop.left)
      (m ⊗ₜ (L'.restrictₛₗ Y.unop.hom.op l)))
    = α.app (op Y.unop.left) (m ⊗ₜ (L.restrictₛₗ Y.unop.hom.op (g.app X l)))
  exact congrArg _ ((whiskerLeft_app_tmul g (op Y.unop.left) m
    (L'.restrictₛₗ Y.unop.hom.op l)).trans
      (congrArg (fun x ↦ m ⊗ₜ x) (naturality_apply g Y.unop.hom.op l)))

/-- The internal-hom adjunction bijection `(M ⊗ L ⟶ N) ≃ (L ⟶ ihom M N)`. -/
noncomputable def ihomHomEquiv : (M ⊗ L ⟶ N) ≃ (L ⟶ ihom M N) where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

end Adjunction

section Crux

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{max u v w})
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]

/-- The class of morphisms of presheaves of modules whose underlying morphism of presheaves of
abelian groups is in `J.W` is exactly the class of morphisms which are left-orthogonal to the
presheaves of modules whose underlying presheaf is a sheaf. -/
lemma W_inverseImage_toPresheaf_eq_isLocal :
    J.W.inverseImage (toPresheaf.{max u v w} R.obj) =
      ObjectProperty.isLocal (fun N : PresheafOfModules.{max u v w} R.obj =>
        Presheaf.IsSheaf J N.presheaf) := by
  rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms (𝟙 R.obj),
    ← ObjectProperty.isLocal_eq_inverseImage_isomorphisms (sheafificationAdjunction (𝟙 R.obj))]
  congr 1
  ext N
  exact ⟨fun ⟨F, hF⟩ ↦ hF ▸ F.isSheaf, fun h ↦ ⟨⟨N, h⟩, rfl⟩⟩

/-- A morphism `f : M₁ ⟶ M₂` of presheaves of modules has underlying morphism in `J.W` if and
only if precomposition with `f` is bijective on morphisms into every presheaf of modules whose
underlying presheaf is a sheaf. -/
lemma W_inverseImage_toPresheaf_iff {M₁ M₂ : PresheafOfModules.{max u v w} R.obj} (f : M₁ ⟶ M₂) :
    J.W.inverseImage (toPresheaf.{max u v w} R.obj) f ↔
      ∀ (N : PresheafOfModules.{max u v w} R.obj), Presheaf.IsSheaf J N.presheaf →
        Function.Bijective (fun (g : M₂ ⟶ N) ↦ f ≫ g) := by
  rw [W_inverseImage_toPresheaf_eq_isLocal R]
  exact Iff.rfl

variable (S : Sheaf J CommRingCat.{max u v w})

/-- The characterization `W_inverseImage_toPresheaf_iff` for presheaves of modules over a sheaf
of commutative rings. -/
lemma W_inverseImage_toPresheaf_iff'
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v w})]
    {M₁ M₂ : PresheafOfModules.{max u v w} (S.obj ⋙ forget₂ CommRingCat RingCat)} (f : M₁ ⟶ M₂) :
    J.W.inverseImage (toPresheaf.{max u v w} (S.obj ⋙ forget₂ CommRingCat RingCat)) f ↔
      ∀ (N : PresheafOfModules.{max u v w} (S.obj ⋙ forget₂ CommRingCat RingCat)),
        Presheaf.IsSheaf J N.presheaf → Function.Bijective (fun (g : M₂ ⟶ N) ↦ f ≫ g) :=
  W_inverseImage_toPresheaf_iff (((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)) f

/-- Left whiskering by a presheaf of modules preserves the class of morphisms whose underlying
morphism of presheaves of abelian groups is in `J.W`. A sectionwise proof fails, since
tensoring is not left exact; the proof goes through the internal-hom adjunction instead. -/
lemma W_inverseImage_toPresheaf_whiskerLeft
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v w})]
    (M : PresheafOfModules.{max u v w} (S.obj ⋙ forget₂ CommRingCat RingCat))
    {L₁ L₂ : PresheafOfModules.{max u v w} (S.obj ⋙ forget₂ CommRingCat RingCat)} {g : L₁ ⟶ L₂}
    (hg : J.W.inverseImage (toPresheaf.{max u v w} (S.obj ⋙ forget₂ CommRingCat RingCat)) g) :
    J.W.inverseImage (toPresheaf.{max u v w} (S.obj ⋙ forget₂ CommRingCat RingCat)) (M ◁ g) := by
  refine (W_inverseImage_toPresheaf_iff' S (M ◁ g)).2 (fun N hN ↦ ?_)
  have key : (fun (h : M ⊗ L₂ ⟶ N) ↦ (M ◁ g) ≫ h)
      = (ihomHomEquiv (M := M) (N := N) (L := L₁)).symm ∘
        ((fun (k : L₂ ⟶ ihom M N) ↦ g ≫ k) ∘ ihomHomEquiv (M := M) (N := N) (L := L₂)) :=
    funext fun h ↦ Equiv.eq_symm_apply _ |>.2 (curry_naturality_left g h)
  rw [key]
  exact ihomHomEquiv.symm.bijective.comp
    (((W_inverseImage_toPresheaf_iff' S g).1 hg (ihom M N) (isSheaf_ihom M N hN)).comp
      ihomHomEquiv.bijective)

/-- The class of morphisms of presheaves of modules over a sheaf of commutative rings which are
local isomorphisms of the underlying presheaves of abelian groups is monoidal. This is the input
needed to transport the symmetric monoidal structure on `PresheafOfModules` along module
sheafification. -/
instance isMonoidal_W_inverseImage_toPresheaf
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v w})] :
    (J.W.inverseImage
      (toPresheaf.{max u v w} (S.obj ⋙ forget₂ CommRingCat RingCat))).IsMonoidal where
  whiskerLeft M _ _ _ hg := W_inverseImage_toPresheaf_whiskerLeft S M hg
  whiskerRight {L₁ L₂} f hf M :=
    ((J.W.inverseImage
      (toPresheaf.{max u v w} (S.obj ⋙ forget₂ CommRingCat RingCat))).arrow_mk_iso_iff
        (Arrow.isoMk (β_ L₁ M) (β_ L₂ M))).2 (W_inverseImage_toPresheaf_whiskerLeft S M hf)

end Crux

end PresheafOfModules

end
