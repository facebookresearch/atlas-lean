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

* `StacksFrontier/Algebra/Category/ModuleCat/Presheaf/Tensor.lean`

Modifications: source-local imports replaced by MathlibExt and Mathlib, using the native
ring-sheaf forgetful functor; the tensor and internal-Hom operations are unchanged.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Tensor products of presheaves of modules in independent universes

For a presheaf of commutative rings `O`, the objectwise tensor product of two presheaves of
`O`-modules whose factors live in independent universes, and the curried bifunctor it defines,
which is additive in each variable.

## Main definitions

* `PresheafOfModules.tensorObj`: The objectwise tensor product `F ⊗ G`.
* `PresheafOfModules.tensorHom`: The objectwise tensor product of two morphisms.
* `PresheafOfModules.tensorBifunctor`: The curried bifunctor `F, G ↦ F ⊗ G`.

## Main results

* `PresheafOfModules.tensorBifunctor_additive`: `tensorBifunctor` is additive in the first
  variable.
* `PresheafOfModules.tensorBifunctor_obj_additive`: `tensorBifunctor` is additive in the second
  variable.
-/

@[expose] public section

open CategoryTheory Opposite

open scoped TensorProduct

universe v u w z z₁ z₂

namespace ModuleCat

variable {R S : Type w} [CommRing R] [CommRing S] (φ : R →+* S)
  {M : Type z} [AddCommGroup M] [Module R M]
  {N : Type z₁} [AddCommGroup N] [Module R N]
  {M' : Type z} [AddCommGroup M'] [Module S M']
  {N' : Type z₁} [AddCommGroup N'] [Module S N']

/-- A pair of semilinear maps along a ring homomorphism `φ : R →+* S` induces a map
`M ⊗[R] N ⟶ M' ⊗[S] N'` which is `R`-linear for the `R`-module structure on the target
obtained by restriction of scalars along `φ`. -/
noncomputable def tensorRestrictMap (u : M →ₛₗ[φ] M') (v : N →ₛₗ[φ] N') :
    ModuleCat.of R (M ⊗[R] N) ⟶
      (ModuleCat.restrictScalars φ).obj (ModuleCat.of S (M' ⊗[S] N')) :=
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars φ).obj (ModuleCat.of S (M' ⊗[S] N')))
    (TensorProduct.lift
      (LinearMap.mk₂ R (M := M) (Nₗ := N)
        (Pₗ := ((ModuleCat.restrictScalars φ).obj (ModuleCat.of S (M' ⊗[S] N')) : Type (max z z₁)))
        (fun m n ↦ u m ⊗ₜ[S] v n)
        (fun m m₂ n ↦ by rw [map_add]; exact TensorProduct.add_tmul _ _ _)
        (fun r m n ↦ by rw [map_smulₛₗ]; exact (TensorProduct.smul_tmul' _ _ _).symm)
        (fun m n n₂ ↦ by rw [map_add]; exact TensorProduct.tmul_add _ _ _)
        (fun r m n ↦ by
          rw [map_smulₛₗ]
          exact TensorProduct.tmul_smul (R := S) (R' := S) (φ r) (u m) (v n))))

section Lift

variable {P : Type (max z z₁)} [AddCommGroup P] [Module R P]
  (f : M → N → P)
  (h₁ : ∀ x x' y, f (x + x') y = f x y + f x' y)
  (h₂ : ∀ (r : R) x y, f (r • x) y = r • f x y)
  (h₃ : ∀ x y y', f x (y + y') = f x y + f x y')
  (h₄ : ∀ (r : R) x y, f x (r • y) = r • f x y)

/-- A bilinear map on sections lifts to a morphism out of a tensor product. -/
noncomputable def tensorLift : ModuleCat.of R (M ⊗[R] N) ⟶ ModuleCat.of R P :=
  ModuleCat.ofHom (TensorProduct.lift (LinearMap.mk₂ R f h₁ h₂ h₃ h₄))

/-- The morphism `tensorLift f …` sends `m ⊗ₜ n` to `f m n`. -/
@[simp]
lemma tensorLift_tmul (m : M) (n : N) :
    tensorLift f h₁ h₂ h₃ h₄ (m ⊗ₜ[R] n) = f m n :=
  TensorProduct.lift.tmul _ _

end Lift

/-- Two morphisms out of a tensor product which agree on pure tensors are equal. -/
lemma tensor_ext {Q : ModuleCat.{max z z₁} R}
    {f g : ModuleCat.of R (M ⊗[R] N) ⟶ Q} (h : ∀ (m : M) (n : N), f (m ⊗ₜ[R] n) = g (m ⊗ₜ[R] n)) :
    f = g :=
  ModuleCat.hom_ext (TensorProduct.ext (LinearMap.ext fun m ↦ LinearMap.ext fun n ↦ h m n))

/-- The morphism `tensorRestrictMap φ u v` sends `m ⊗ₜ n` to `u m ⊗ₜ v n`. -/
@[simp]
lemma tensorRestrictMap_tmul (u : M →ₛₗ[φ] M') (v : N →ₛₗ[φ] N') (m : M) (n : N) :
    tensorRestrictMap φ u v (m ⊗ₜ[R] n) = u m ⊗ₜ[S] v n :=
  TensorProduct.lift.tmul _ _

section Restrict

variable {M : Type z} [AddCommGroup M] [Module S M] {N : Type z₁} [AddCommGroup N] [Module S N]

/-- Moving a scalar acting through restriction of scalars out of the first factor of a
pure tensor. -/
lemma smul_tmul_restrictScalars (r : R) (m : M) (n : N) :
    (φ r • m) ⊗ₜ[S] n = φ r • (m ⊗ₜ[S] n) :=
  (TensorProduct.smul_tmul' _ _ _).symm

/-- Moving a scalar acting through restriction of scalars out of the second factor of a
pure tensor. -/
lemma tmul_smul_restrictScalars (r : R) (m : M) (n : N) :
    m ⊗ₜ[S] (φ r • n) = φ r • (m ⊗ₜ[S] n) :=
  TensorProduct.tmul_smul (R := S) (R' := S) (φ r) m n

end Restrict

end ModuleCat

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C]

section MapApply

variable {R : Cᵒᵖ ⥤ RingCat.{w}} (M : PresheafOfModules.{z} R)

/-- The restriction map of `M` along an identity morphism fixes every section. -/
lemma map_id_apply (X : Cᵒᵖ) (x : M.obj X) : M.map (𝟙 X) x = x := by
  rw [M.map_id]; rfl

/-- Restricting a section along an identity morphism leaves it unchanged. -/
@[simp]
lemma restrictₛₗ_id_apply (X : Cᵒᵖ) (x : M.obj X) : M.restrictₛₗ (𝟙 X) x = x :=
  M.map_id_apply X x

/-- Restricting a section along `f ≫ g` is restricting it along `f` and then along `g`. -/
@[simp]
lemma restrictₛₗ_comp_apply {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (x : M.obj X) :
    M.restrictₛₗ (f ≫ g) x = M.restrictₛₗ g (M.restrictₛₗ f x) :=
  M.map_comp_apply f g x

variable {M} {N : PresheafOfModules.{z} R}

/-- Naturality of a family of maps of sections, in the pointwise form provided by
`PresheafOfModules.restrictₛₗ`. -/
lemma naturality_of_restrictₛₗ (app : ∀ X, M.obj X ⟶ N.obj X)
    (h : ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y) (x : M.obj X),
      app Y (M.restrictₛₗ f x) = N.restrictₛₗ f (app X x))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    M.map f ≫ (ModuleCat.restrictScalars (R.map f).hom).map (app Y) = app X ≫ N.map f :=
  ModuleCat.hom_ext (LinearMap.ext fun x ↦ h f x)

/-- A morphism of presheaves of modules commutes with restriction of sections. -/
lemma restrictₛₗ_naturality_apply (φ : M ⟶ N) {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : M.obj X) :
    Hom.app φ Y (M.restrictₛₗ f x) = N.restrictₛₗ f (Hom.app φ X x) :=
  naturality_apply φ f x

end MapApply

section Tensor

variable {O : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- The ring of sections of `O ⋙ forget₂ CommRingCat RingCat` over `X` is commutative. -/
noncomputable instance commRingObjForget₂ (X : Cᵒᵖ) :
    CommRing ((O ⋙ forget₂ CommRingCat RingCat).obj X) :=
  inferInstanceAs (CommRing (O.obj X))

/-- The objectwise tensor product of two presheaves of modules over a presheaf of commutative
rings, the two factors living in module universes independent of each other and of the universe of
the ring. -/
noncomputable def tensorObj (F : PresheafOfModules.{z} (O ⋙ forget₂ _ RingCat))
    (G : PresheafOfModules.{z₁} (O ⋙ forget₂ _ RingCat)) :
    PresheafOfModules.{max z z₁} (O ⋙ forget₂ CommRingCat RingCat) where
  obj X := ModuleCat.of ((O ⋙ forget₂ CommRingCat RingCat).obj X)
    (F.obj X ⊗[(O ⋙ forget₂ CommRingCat RingCat).obj X] G.obj X)
  map f := ModuleCat.tensorRestrictMap _ (F.restrictₛₗ f) (G.restrictₛₗ f)
  map_id X := by
    refine ModuleCat.hom_ext (TensorProduct.ext (LinearMap.ext fun x ↦ LinearMap.ext fun y ↦ ?_))
    change ModuleCat.tensorRestrictMap _ _ _ (x ⊗ₜ y) = _
    rw [ModuleCat.tensorRestrictMap_tmul, restrictₛₗ_id_apply, restrictₛₗ_id_apply]
    rfl
  map_comp f g := by
    refine ModuleCat.hom_ext (TensorProduct.ext (LinearMap.ext fun x ↦ LinearMap.ext fun y ↦ ?_))
    change ModuleCat.tensorRestrictMap _ _ _ (x ⊗ₜ y) = _
    rw [ModuleCat.tensorRestrictMap_tmul, restrictₛₗ_comp_apply, restrictₛₗ_comp_apply]
    rfl

variable {F : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat)}
  {G : PresheafOfModules.{z₁} (O ⋙ forget₂ CommRingCat RingCat)}

/-- Restriction in `tensorObj F G` sends `x ⊗ₜ y` to the tensor product of the restrictions of
`x` and `y`. -/
@[simp]
lemma tensorObj_restrictₛₗ_tmul {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : F.obj X) (y : G.obj X) :
    (tensorObj F G).restrictₛₗ f (x ⊗ₜ y) = F.restrictₛₗ f x ⊗ₜ G.restrictₛₗ f y :=
  ModuleCat.tensorRestrictMap_tmul _ _ _ _ _

end Tensor

section TensorHom

variable {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {F : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat)}
  {G : PresheafOfModules.{z₁} (O ⋙ forget₂ CommRingCat RingCat)}
  {P : PresheafOfModules.{max z z₁} (O ⋙ forget₂ CommRingCat RingCat)}

/-- A morphism out of the objectwise tensor product of two presheaves of modules, built
from a family of bilinear maps on sections which is compatible with restriction. -/
noncomputable def tensorMk
    (app : ∀ (X : Cᵒᵖ), F.obj X → G.obj X → P.obj X)
    (add_left : ∀ (X : Cᵒᵖ) (x x' : F.obj X) (y : G.obj X),
      app X (x + x') y = app X x y + app X x' y)
    (smul_left : ∀ (X : Cᵒᵖ) (r : (O ⋙ forget₂ CommRingCat RingCat).obj X)
      (x : F.obj X) (y : G.obj X), app X (r • x) y = r • app X x y)
    (add_right : ∀ (X : Cᵒᵖ) (x : F.obj X) (y y' : G.obj X),
      app X x (y + y') = app X x y + app X x y')
    (smul_right : ∀ (X : Cᵒᵖ) (r : (O ⋙ forget₂ CommRingCat RingCat).obj X)
      (x : F.obj X) (y : G.obj X), app X x (r • y) = r • app X x y)
    (naturality : ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y) (x : F.obj X) (y : G.obj X),
      P.restrictₛₗ f (app X x y) = app Y (F.restrictₛₗ f x) (G.restrictₛₗ f y)) :
    tensorObj F G ⟶ P where
  app X := ModuleCat.tensorLift (app X) (add_left X) (smul_left X) (add_right X) (smul_right X)
  naturality {X Y} f := by
    refine ModuleCat.tensor_ext fun x y ↦ ?_
    change ModuleCat.tensorLift (app Y) (add_left Y) (smul_left Y) (add_right Y) (smul_right Y)
        ((tensorObj F G).restrictₛₗ f (x ⊗ₜ y)) =
      P.restrictₛₗ f (ModuleCat.tensorLift (app X) (add_left X) (smul_left X) (add_right X)
        (smul_right X) (x ⊗ₜ y))
    rw [tensorObj_restrictₛₗ_tmul, ModuleCat.tensorLift_tmul, ModuleCat.tensorLift_tmul]
    exact (naturality f x y).symm

/-- On sections over `X`, the morphism `tensorMk app …` sends `x ⊗ₜ y` to `app X x y`. -/
@[simp]
lemma tensorMk_tmul
    (app : ∀ (X : Cᵒᵖ), F.obj X → G.obj X → P.obj X) (add_left) (smul_left) (add_right)
    (smul_right) (naturality) (X : Cᵒᵖ) (x : F.obj X) (y : G.obj X) :
    Hom.app (tensorMk app add_left smul_left add_right smul_right naturality) X (x ⊗ₜ y) =
      app X x y :=
  ModuleCat.tensorLift_tmul _ _ _ _ _ _ _

/-- Two morphisms out of an objectwise tensor product which agree on pure tensors of
sections are equal. -/
lemma tensorObj_hom_ext {φ ψ : tensorObj F G ⟶ P}
    (h : ∀ (X : Cᵒᵖ) (x : F.obj X) (y : G.obj X),
      Hom.app φ X (x ⊗ₜ y) = Hom.app ψ X (x ⊗ₜ y)) : φ = ψ :=
  hom_ext fun X ↦ ModuleCat.tensor_ext (h X)

end TensorHom

section TensorFunctor

variable {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {F F' : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat)}
  {G G' : PresheafOfModules.{z₁} (O ⋙ forget₂ CommRingCat RingCat)}

/-- The objectwise tensor product of two morphisms of presheaves of modules. -/
noncomputable def tensorHom (u : F ⟶ F') (v : G ⟶ G') : tensorObj F G ⟶ tensorObj F' G' :=
  tensorMk (fun X x y ↦ Hom.app u X x ⊗ₜ Hom.app v X y)
    (fun X x x' y ↦ by rw [map_add]; exact TensorProduct.add_tmul _ _ _)
    (fun X r x y ↦ by rw [map_smul]; exact TensorProduct.smul_tmul' _ _ _)
    (fun X x y y' ↦ by rw [map_add]; exact TensorProduct.tmul_add _ _ _)
    (fun X r x y ↦ by rw [map_smul]; exact TensorProduct.tmul_smul _ _ _)
    (fun {X Y} f x y ↦ by
      rw [tensorObj_restrictₛₗ_tmul, restrictₛₗ_naturality_apply u f x,
        restrictₛₗ_naturality_apply v f y])

/-- On sections over `X`, the morphism `tensorHom u v` sends `x ⊗ₜ y` to `u x ⊗ₜ v y`. -/
@[simp]
lemma tensorHom_tmul (u : F ⟶ F') (v : G ⟶ G') (X : Cᵒᵖ) (x : F.obj X) (y : G.obj X) :
    Hom.app (tensorHom u v) X (x ⊗ₜ y) = Hom.app u X x ⊗ₜ Hom.app v X y :=
  tensorMk_tmul _ _ _ _ _ _ _ _ _

/-- The tensor product of two identity morphisms is the identity. -/
@[simp]
lemma tensorHom_id (left : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat))
    (right : PresheafOfModules.{z₁} (O ⋙ forget₂ CommRingCat RingCat)) :
    tensorHom (𝟙 left) (𝟙 right) = 𝟙 (tensorObj left right) := by
  refine tensorObj_hom_ext fun sectionObj leftSection rightSection ↦ ?_
  rw [tensorHom_tmul]
  rfl

/-- The tensor product of morphisms is compatible with composition. -/
@[simp]
lemma tensorHom_comp
    {leftTarget : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat)}
    {rightTarget : PresheafOfModules.{z₁} (O ⋙ forget₂ CommRingCat RingCat)}
    (leftHom : F ⟶ F') (rightHom : G ⟶ G')
    (leftHom' : F' ⟶ leftTarget) (rightHom' : G' ⟶ rightTarget) :
    tensorHom leftHom rightHom ≫ tensorHom leftHom' rightHom' =
      tensorHom (leftHom ≫ leftHom') (rightHom ≫ rightHom') := by
  refine tensorObj_hom_ext fun sectionObj leftSection rightSection ↦ ?_
  change Hom.app (tensorHom leftHom' rightHom') sectionObj
      (Hom.app (tensorHom leftHom rightHom) sectionObj (leftSection ⊗ₜ rightSection)) =
    Hom.app (tensorHom (leftHom ≫ leftHom') (rightHom ≫ rightHom')) sectionObj
      (leftSection ⊗ₜ rightSection)
  rw [tensorHom_tmul, tensorHom_tmul, tensorHom_tmul]
  rfl

/-- Sections of a sum of morphisms of presheaves of modules are sums of sections. -/
private lemma app_add_apply {R : Cᵒᵖ ⥤ RingCat.{w}} {M N : PresheafOfModules.{z} R}
    (u u' : M ⟶ N) (X : Cᵒᵖ) (x : M.obj X) :
    Hom.app (u + u') X x = Hom.app u X x + Hom.app u' X x := by
  rw [add_app]
  rfl

/-- The zero morphism of presheaves of modules sends every section to zero. -/
private lemma app_zero_apply {R : Cᵒᵖ ⥤ RingCat.{w}} {M N : PresheafOfModules.{z} R}
    (X : Cᵒᵖ) (x : M.obj X) : Hom.app (0 : M ⟶ N) X x = 0 := by
  rw [zero_app]
  rfl

/-- The objectwise tensor product of morphisms is additive in the first factor. -/
theorem tensorHom_add_left (u u' : F ⟶ F') (v : G ⟶ G') :
    tensorHom (u + u') v = tensorHom u v + tensorHom u' v := by
  refine tensorObj_hom_ext fun X x y ↦ ?_
  rw [app_add_apply (tensorHom u v) (tensorHom u' v) X (x ⊗ₜ y), tensorHom_tmul, tensorHom_tmul,
    tensorHom_tmul, app_add_apply]
  exact TensorProduct.add_tmul _ _ _

/-- The objectwise tensor product of a zero morphism with any morphism is zero. -/
theorem tensorHom_zero_left (v : G ⟶ G') : tensorHom (0 : F ⟶ F') v = 0 := by
  refine tensorObj_hom_ext fun X x y ↦ ?_
  rw [tensorHom_tmul, app_zero_apply, TensorProduct.zero_tmul]
  exact (app_zero_apply (M := tensorObj F G) (N := tensorObj F' G') X _).symm

/-- The objectwise tensor product of morphisms is additive in the second factor. -/
theorem tensorHom_add_right (leftHom : F ⟶ F') (rightHom rightHom' : G ⟶ G') :
    tensorHom leftHom (rightHom + rightHom') =
      tensorHom leftHom rightHom + tensorHom leftHom rightHom' := by
  refine tensorObj_hom_ext fun X x y ↦ ?_
  rw [app_add_apply (tensorHom leftHom rightHom) (tensorHom leftHom rightHom') X (x ⊗ₜ y),
    tensorHom_tmul, tensorHom_tmul, tensorHom_tmul, app_add_apply]
  exact TensorProduct.tmul_add _ _ _

/-- The objectwise tensor product of any morphism with a zero morphism is zero. -/
theorem tensorHom_zero_right (leftHom : F ⟶ F') : tensorHom leftHom (0 : G ⟶ G') = 0 := by
  refine tensorObj_hom_ext fun X x y ↦ ?_
  rw [tensorHom_tmul, app_zero_apply, TensorProduct.tmul_zero]
  exact (app_zero_apply (M := tensorObj F G) (N := tensorObj F' G') X _).symm

variable (O) in
/-- The objectwise tensor product of presheaves of modules, as a curried bifunctor whose two
factors live in independent universes. -/
noncomputable def tensorBifunctor :
    PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat) ⥤
      PresheafOfModules.{z₁} (O ⋙ forget₂ CommRingCat RingCat) ⥤
        PresheafOfModules.{max z z₁} (O ⋙ forget₂ CommRingCat RingCat) where
  obj left :=
    { obj := fun right ↦ tensorObj left right
      map := fun rightHom ↦ tensorHom (𝟙 left) rightHom
      map_id := fun right ↦ tensorHom_id left right
      map_comp := fun rightHom rightHom' ↦ by
        rw [tensorHom_comp, Category.id_comp] }
  map leftHom :=
    { app := fun right ↦ tensorHom leftHom (𝟙 right)
      naturality := fun right right' rightHom ↦ by
        simp only [tensorHom_comp, Category.id_comp, Category.comp_id] }
  map_id left := NatTrans.ext (funext fun right ↦ tensorHom_id left right)
  map_comp leftHom leftHom' := NatTrans.ext (funext fun right ↦ by
    dsimp
    rw [tensorHom_comp, Category.id_comp])

/-- The bifunctor `tensorBifunctor O` sends `left` and `right` to `tensorObj left right`. -/
@[simp]
lemma tensorBifunctor_obj_obj
    (left : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat))
    (right : PresheafOfModules.{z₁} (O ⋙ forget₂ CommRingCat RingCat)) :
    ((tensorBifunctor O).obj left).obj right = tensorObj left right := rfl

/-- The functor `(tensorBifunctor O).obj left` acts on a morphism `rightHom` as
`tensorHom (𝟙 left) rightHom`. -/
@[simp]
lemma tensorBifunctor_obj_map
    (left : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat)) (rightHom : G ⟶ G') :
    ((tensorBifunctor O).obj left).map rightHom = tensorHom (𝟙 left) rightHom := rfl

/-- The component at `right` of `(tensorBifunctor O).map leftHom` is
`tensorHom leftHom (𝟙 right)`. -/
@[simp]
lemma tensorBifunctor_map_app (leftHom : F ⟶ F')
    (right : PresheafOfModules.{z₁} (O ⋙ forget₂ CommRingCat RingCat)) :
    ((tensorBifunctor O).map leftHom).app right = tensorHom leftHom (𝟙 right) := rfl

/-- The uncurried bifunctor `tensorBifunctor O` sends a pair of morphisms `(leftHom, rightHom)`
to `tensorHom leftHom rightHom`. -/
@[simp]
lemma tensorBifunctor_uncurry_map (leftHom : F ⟶ F') (rightHom : G ⟶ G') :
    (Functor.uncurry.obj (tensorBifunctor O)).map
        ((leftHom, rightHom) : (F, G) ⟶ (F', G')) =
      tensorHom leftHom rightHom := by
  change tensorHom leftHom (𝟙 G) ≫ tensorHom (𝟙 F') rightHom = _
  rw [tensorHom_comp, Category.comp_id, Category.id_comp]

/-- For a fixed first factor, the tensor product is an additive functor of the second
factor. -/
instance tensorBifunctor_obj_additive
    (left : PresheafOfModules.{z} (O ⋙ forget₂ CommRingCat RingCat)) :
    ((tensorBifunctor.{v, u, w, z, z₁} O).obj left).Additive where
  map_add := tensorHom_add_right (𝟙 left) _ _

/-- The tensor product bifunctor is additive in its first factor. -/
instance tensorBifunctor_additive : (tensorBifunctor.{v, u, w, z, z₁} O).Additive where
  map_add := NatTrans.ext (funext fun right ↦ tensorHom_add_left _ _ (𝟙 right))

end TensorFunctor

end PresheafOfModules
