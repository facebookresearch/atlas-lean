/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Adapted from AxiomMath/Stacks, revision
c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SectionwiseAlgebras.lean
(Apache 2.0, as described in that repository's LICENSE).
Modification: retain only the actual sectionwise exterior-power presheaf
and its section identification, using the complete semilinear core.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import MathlibExt.LinearAlgebra.ExteriorPowerSemilinear

/-! # Actual sectionwise exterior-power presheaves

The restriction maps are the exterior powers of the actual semilinear
module restrictions. This completes the source construction; no exterior
power is supplied as a formal law-bearing field.
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u w a

namespace PresheafOfModules

private theorem map_id_apply_ungraded
    {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}}
    (F : PresheafOfModules.{a} R) (U : Cᵒᵖ) (m : F.obj U) :
    F.map (𝟙 U) m = m := by
  rw [F.map_id]
  rfl

section ExtPow

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}

local instance (X : Cᵒᵖ) :
    CommRing ((O ⋙ forget₂ CommRingCat RingCat).obj X) :=
  inferInstanceAs (CommRing (O.obj X))

/-- The restriction map of the presheaf of sectionwise exterior powers, as an
additive map whose
target type is written as an exterior power rather than as a restriction of
scalars. -/
noncomputable def extPowRestrict (n : ℕ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) {X Y : Cᵒᵖ} (f :
      X ⟶ Y) :
    (⋀[(O ⋙ forget₂ _ RingCat).obj X]^n (F.obj X)) →+
      ⋀[(O ⋙ forget₂ _ RingCat).obj Y]^n (F.obj Y) :=
  (ExteriorAlgebra.powMapₛₗ n ((O ⋙ forget₂ _ RingCat).map f).hom
    (F.restrictₛₗ f)).toAddMonoidHom

/-- As an element of the exterior algebra, the restriction of a section of an
exterior power is
its image under `ExteriorAlgebra.mapₛₗ` of the restriction map of `F`. -/
@[simp]
theorem extPowRestrict_coe (n : ℕ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) {X Y : Cᵒᵖ} (f :
      X ⟶ Y)
    (x : ⋀[(O ⋙ forget₂ _ RingCat).obj X]^n (F.obj X)) :
    (extPowRestrict n F f x : ExteriorAlgebra ((O ⋙ forget₂ _ RingCat).obj Y)
      (F.obj Y)) =
      ExteriorAlgebra.mapₛₗ ((O ⋙ forget₂ _ RingCat).map f).hom (F.restrictₛₗ
        f) x := rfl

/-- The presheaf of abelian groups underlying the presheaf of sectionwise
exterior powers. -/
noncomputable def extPowAb (n : ℕ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) : Cᵒᵖ ⥤
      AddCommGrpCat.{max w a} where
  obj X := AddCommGrpCat.of (⋀[(O ⋙ forget₂ _ RingCat).obj X]^n (F.obj X))
  map f := AddCommGrpCat.ofHom (extPowRestrict n F f)
  map_id X := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => Subtype.ext ?_)
    exact ExteriorAlgebra.mapₛₗ_eq_self (F.restrictₛₗ (𝟙 X))
      (fun r => congrArg (fun φ : (O ⋙ forget₂ _ RingCat).obj X ⟶
        (O ⋙ forget₂ _ RingCat).obj X => (ConcreteCategory.hom φ) r)
        ((O ⋙ forget₂ _ RingCat).map_id X))
      (fun m => F.map_id_apply_ungraded X m) x
  map_comp {X _ Z} f g := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => Subtype.ext ?_)
    exact ExteriorAlgebra.mapₛₗ_eq_comp (F.restrictₛₗ f) (F.restrictₛₗ g)
      (F.restrictₛₗ (f ≫ g))
      (fun r => congrArg (fun φ : (O ⋙ forget₂ _ RingCat).obj X ⟶
        (O ⋙ forget₂ _ RingCat).obj Z => (ConcreteCategory.hom φ) r)
        ((O ⋙ forget₂ _ RingCat).map_comp f g))
      (fun m => F.map_comp_apply f g m) x

/-- The `O(X)`-module structure on `⋀ⁿ_{O(X)}(F(X))`. -/
noncomputable instance extPowAbModule (n : ℕ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) (X : Cᵒᵖ) :
    Module ((O ⋙ forget₂ _ RingCat).obj X) ((extPowAb n F).obj X) :=
  inferInstanceAs
    (Module ((O ⋙ forget₂ _ RingCat).obj X)
      (⋀[(O ⋙ forget₂ _ RingCat).obj X]^n (F.obj X)))

/-- The presheaf of sectionwise exterior powers: its sections over `X` are
`⋀ⁿ_{O(X)}(F(X))`, and its restriction maps are the exterior powers of the
restriction maps of
`F`, in the semilinear sense of `ExteriorAlgebra.powMapₛₗ`. -/
noncomputable def extPow (n : ℕ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) :
    PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat) :=
  PresheafOfModules.ofPresheaf (extPowAb n F) fun {_ _} _ r _ => Subtype.ext
    (ExteriorAlgebra.mapₛₗ_smul _ _ r _)

/-- Restricting a wedge of sections gives the wedge of their restrictions. -/
@[simp]
theorem extPow_map_ιMulti (n : ℕ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (v : Fin n → F.obj X) :
    (extPow n F).map f (exteriorPower.ιMulti _ n v) =
      exteriorPower.ιMulti _ n fun i => F.map f (v i) :=
  ExteriorAlgebra.powMapₛₗ_ιMulti n _ (F.restrictₛₗ f) v

/-- The sections of `extPow n F` over `X` are the `n`-th
exterior power of the sections of `F` over `X`. -/
noncomputable def extPowSections (n : ℕ)
    (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) (X : Cᵒᵖ) :
    (extPow n F).obj X ≃ₗ[(O ⋙ forget₂ _ RingCat).obj X]
      ⋀[(O ⋙ forget₂ _ RingCat).obj X]^n (F.obj X) :=
  LinearEquiv.refl _ _


end ExtPow

end PresheafOfModules
