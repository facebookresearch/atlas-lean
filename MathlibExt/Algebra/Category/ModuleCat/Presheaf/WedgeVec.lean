/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_PresheafOfModules_ExteriorPower.lean` and
`Definitions/Def_AlgebraicGeometry_ModulesWedge.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.PresheafExteriorPowers
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-!
# Functoriality of sectionwise exterior powers and the wedge map

* `exteriorPower.mulVec R M n : ⋀ⁿ M →ₗ M →ₗ ⋀ⁿ⁺¹ M` is right multiplication by a vector in the
  exterior algebra.
* `PresheafOfModules.extPowFunctor O n` makes the sectionwise exterior power
  `PresheafOfModules.extPow n` a functor on presheaves of modules over a presheaf of commutative
  rings `O`.
* `PresheafOfModules.wedgeVec n P : extPow n P ⊗ P ⟶ extPow (n + 1) P` is the sectionwise map
  `x ⊗ m ↦ x ∧ m`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe v₁ u₁ u

open CategoryTheory MonoidalCategory

namespace exteriorPower

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

/-- Multiplication in the exterior algebra, as a bilinear map `⋀ᵃ M → ⋀ᵇ M → ⋀ᵃ⁺ᵇ M`. -/
noncomputable def mulₗ (a b : ℕ) : ⋀[R]^a M →ₗ[R] ⋀[R]^b M →ₗ[R] ⋀[R]^(a + b) M :=
  LinearMap.mk₂ R (fun x y => ⟨x.1 * y.1, ExteriorAlgebra.mul_mem_exteriorPower x.2 y.2⟩)
    (fun x x' y => Subtype.ext (add_mul x.1 x'.1 y.1))
    (fun r x y => Subtype.ext (smul_mul_assoc r x.1 y.1))
    (fun x y y' => Subtype.ext (mul_add x.1 y.1 y'.1))
    (fun r x y => Subtype.ext (mul_smul_comm r x.1 y.1))

@[simp] lemma mulₗ_apply_coe (a b : ℕ) (x : ⋀[R]^a M) (y : ⋀[R]^b M) :
    ((mulₗ R M a b x y : ⋀[R]^(a + b) M) : ExteriorAlgebra R M) = x.1 * y.1 := rfl

lemma mulₗ_ιMulti_ιMulti {a b : ℕ} (v : Fin a → M) (w : Fin b → M) :
    mulₗ R M a b (ιMulti R a v) (ιMulti R b w) = ιMulti R (a + b) (Fin.append v w) :=
  Subtype.ext (ExteriorAlgebra.ιMulti_mul_ιMulti v w)

/-- Right multiplication by a vector, `⋀ⁿ M → M → ⋀ⁿ⁺¹ M`, `(x, m) ↦ x ∧ m`. -/
noncomputable def mulVec (n : ℕ) : ⋀[R]^n M →ₗ[R] M →ₗ[R] ⋀[R]^(n + 1) M :=
  (mulₗ R M n 1).compl₂ (oneEquiv R M).symm.toLinearMap

lemma mulVec_apply (n : ℕ) (x : ⋀[R]^n M) (m : M) :
    mulVec R M n x m = mulₗ R M n 1 x ((oneEquiv R M).symm m) := rfl

lemma mulVec_ιMulti (n : ℕ) (v : Fin n → M) (m : M) :
    mulVec R M n (ιMulti R n v) m = ιMulti R (n + 1) (Fin.append v (fun _ : Fin 1 => m)) := by
  rw [mulVec_apply, oneEquiv_symm_apply, mulₗ_ιMulti_ιMulti]

end exteriorPower

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {O : Cᵒᵖ ⥤ CommRingCat.{u}}

-- The commutative ring structure on sections used by `extPow`.
attribute [local instance]
  instCommRingCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrier_mathlibExt

private lemma extPow_induction {n : ℕ} {F : PresheafOfModules.{u} (O ⋙ forget₂ _ RingCat)}
    {X : Cᵒᵖ} {p : ⋀[(O ⋙ forget₂ _ RingCat).obj X]^n (F.obj X) → Prop}
    (zero : p 0) (add : ∀ x y, p x → p y → p (x + y))
    (smul : ∀ (r : (O ⋙ forget₂ _ RingCat).obj X) x, p x → p (r • x))
    (ιMulti : ∀ v : Fin n → F.obj X, p (exteriorPower.ιMulti _ n v)) (x) : p x := by
  have hx : x ∈ Submodule.span ((O ⋙ forget₂ _ RingCat).obj X)
      (Set.range (exteriorPower.ιMulti ((O ⋙ forget₂ _ RingCat).obj X) n (M := F.obj X))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨v, rfl⟩ := hx; exact ιMulti v
  | zero => exact zero
  | add x y _ _ hx hy => exact add x y hx hy
  | smul r x _ hx => exact smul r x hx

/-- The morphism of sectionwise exterior powers induced by a morphism of presheaves of
modules: on sections over `X` it is `⋀ⁿ` of the map on sections. -/
noncomputable def extPowMap (n : ℕ) {F G : PresheafOfModules.{u} (O ⋙ forget₂ _ RingCat)}
    (φ : F ⟶ G) : extPow n F ⟶ extPow n G where
  app X := ModuleCat.ofHom (exteriorPower.map n (φ.app X).hom)
  naturality {X Y} f := by
    ext x
    change exteriorPower.map n (φ.app Y).hom ((extPow n F).map f x) =
      (extPow n G).map f (exteriorPower.map n (φ.app X).hom x)
    induction x using extPow_induction with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | smul r x hx =>
      erw [PresheafOfModules.map_smul, map_smul, map_smul, PresheafOfModules.map_smul, hx]
    | ιMulti v =>
      erw [extPow_map_ιMulti, exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti,
        extPow_map_ιMulti]
      congr 1
      funext i
      exact naturality_apply φ f (v i)

lemma extPowMap_app_apply (n : ℕ) {F G : PresheafOfModules.{u} (O ⋙ forget₂ _ RingCat)}
    (φ : F ⟶ G) (X : Cᵒᵖ) (x : ⋀[(O ⋙ forget₂ _ RingCat).obj X]^n (F.obj X)) :
    (extPowMap n φ).app X x = exteriorPower.map n (φ.app X).hom x := rfl

variable (O) in
/-- The sectionwise `n`-th exterior power, as an endofunctor of presheaves of modules. -/
noncomputable def extPowFunctor (n : ℕ) :
    PresheafOfModules.{u} (O ⋙ forget₂ _ RingCat) ⥤ PresheafOfModules.{u} (O ⋙ forget₂ _ RingCat)
    where
  obj F := extPow n F
  map φ := extPowMap n φ
  map_id F := by
    ext X x
    change exteriorPower.map n LinearMap.id x = x
    rw [exteriorPower.map_id]
    rfl
  map_comp φ ψ := by
    ext X x
    change exteriorPower.map n ((ψ.app X).hom ∘ₗ (φ.app X).hom) x =
      exteriorPower.map n (ψ.app X).hom (exteriorPower.map n (φ.app X).hom x)
    rw [exteriorPower.map_comp]
    rfl

@[simp] lemma extPowFunctor_obj (n : ℕ) (F : PresheafOfModules.{u} (O ⋙ forget₂ _ RingCat)) :
    (extPowFunctor O n).obj F = extPow n F := rfl

@[simp] lemma extPowFunctor_map (n : ℕ) {F G : PresheafOfModules.{u} (O ⋙ forget₂ _ RingCat)}
    (φ : F ⟶ G) : (extPowFunctor O n).map φ = extPowMap n φ := rfl

/-- Right multiplication by a section, on the sections of `extPow n P` over `X`. -/
noncomputable abbrev wedgeVecApp (n : ℕ) (P : PresheafOfModulesOfCommRing.{u} O) (X : Cᵒᵖ) :
    ⋀[(O ⋙ forget₂ _ RingCat).obj X]^n (P.obj X) →ₗ[(O ⋙ forget₂ _ RingCat).obj X]
      P.obj X →ₗ[(O ⋙ forget₂ _ RingCat).obj X]
        ⋀[(O ⋙ forget₂ _ RingCat).obj X]^(n + 1) (P.obj X) :=
  exteriorPower.mulVec _ _ n

private lemma extPow_map_mulVec (n : ℕ) (P : PresheafOfModulesOfCommRing.{u} O) {X Y : Cᵒᵖ}
    (f : X ⟶ Y) (x : ⋀[(O ⋙ forget₂ _ RingCat).obj X]^n (P.obj X)) (m : P.obj X) :
    (extPow (n + 1) P).map f (wedgeVecApp n P X x m) =
      wedgeVecApp n P Y ((extPow n P).map f x) (P.map f m) := by
  induction x using extPow_induction with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | smul r x hx =>
    erw [LinearMap.map_smul₂, PresheafOfModules.map_smul, PresheafOfModules.map_smul,
      LinearMap.map_smul₂, hx]
  | ιMulti v =>
    erw [exteriorPower.mulVec_ιMulti, extPow_map_ιMulti, extPow_map_ιMulti,
      exteriorPower.mulVec_ιMulti]
    congr 1
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [Fin.append_left]
    · simp [Fin.append_right]

/-- The wedge map `extPow n P ⊗ P ⟶ extPow (n + 1) P`, given on sections by
`x ⊗ m ↦ x ∧ m`. -/
noncomputable def wedgeVec (n : ℕ) (P : PresheafOfModulesOfCommRing.{u} O) :
    extPow n P ⊗ P ⟶ extPow (n + 1) P where
  app X := ModuleCat.MonoidalCategory.tensorLift (fun x m => wedgeVecApp n P X x m)
    (fun x x' m => by simp only [map_add, LinearMap.add_apply])
    (fun r x m => by erw [LinearMap.map_smul₂])
    (fun x m m' => by simp only [map_add])
    (fun r x m => by erw [map_smul])
  naturality {X Y} f := by
    refine ModuleCat.hom_ext (TensorProduct.ext' fun x m => ?_)
    exact (extPow_map_mulVec n P f x m).symm

lemma wedgeVec_app_tmul (n : ℕ) (P : PresheafOfModulesOfCommRing.{u} O) (X : Cᵒᵖ)
    (x : ⋀[(O ⋙ forget₂ _ RingCat).obj X]^n (P.obj X)) (m : P.obj X) :
    (wedgeVec n P).app X (x ⊗ₜ[O.obj X] m) = wedgeVecApp n P X x m :=
  rfl

end PresheafOfModules
