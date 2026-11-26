/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_PresheafOfModules_ExteriorPower.lean`
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

/-!
# Functoriality of exterior powers of presheaves of modules

A morphism `φ : M ⟶ N` of presheaves of modules induces a morphism `exteriorPowerMap n φ` of
sectionwise exterior powers `PresheafOfModules.extPow n M ⟶ PresheafOfModules.extPow n N`, given
on sections by `exteriorPower.map n`. These maps form the functor `exteriorPowerFunctor R n`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace PresheafOfModules

variable {C : Type*} [Category C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

local instance ExteriorPower.commRingObj (X : Cᵒᵖ) :
    CommRing ((R ⋙ forget₂ CommRingCat RingCat).obj X) :=
  inferInstanceAs (CommRing (R.obj X))

namespace ExteriorPower

variable (n : ℕ) {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}

/-- **Exterior powers of a morphism, on the underlying abelian presheaves.** For `φ : M ⟶ N`,
the morphism `extPowAb n M ⟶ extPowAb n N` that is `exteriorPower.map n` of `φ.app X` on the
sections over each `X`. -/
noncomputable def mapAb (φ : M ⟶ N) : extPowAb n M ⟶ extPowAb n N where
  app X := AddCommGrpCat.ofHom (exteriorPower.map n (φ.app X).hom).toAddMonoidHom
  naturality {X Y} f := by
    have h : (exteriorPower.map n (φ.app Y).hom).comp
          (ExteriorAlgebra.powMapₛₗ n ((R ⋙ forget₂ CommRingCat RingCat).map f).hom
            (M.restrictₛₗ f)) =
        (ExteriorAlgebra.powMapₛₗ n ((R ⋙ forget₂ CommRingCat RingCat).map f).hom
            (N.restrictₛₗ f)).comp (exteriorPower.map n (φ.app X).hom) :=
      ExteriorAlgebra.powMapₛₗ_ext fun v => by
        simp only [LinearMap.comp_apply, ExteriorAlgebra.powMapₛₗ_ιMulti,
          exteriorPower.map_apply_ιMulti]
        congr 1
        funext i
        exact naturality_apply φ f (v i)
    exact AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => LinearMap.congr_fun h x)

end ExteriorPower

/-- **Exterior powers of a morphism of presheaves of modules.** For `φ : M ⟶ N`, the morphism
`extPow n M ⟶ extPow n N` of sectionwise `n`-th exterior powers that is
`exteriorPower.map n (φ.app X)` on the sections over each `X`. -/
noncomputable def exteriorPowerMap (n : ℕ)
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (φ : M ⟶ N) : extPow n M ⟶ extPow n N :=
  homMk (ExteriorPower.mapAb n φ) (fun X r m =>
    (exteriorPower.map n (φ.app X).hom).map_smul r m)

lemma exteriorPowerMap_app_apply (n : ℕ)
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (φ : M ⟶ N) (X : Cᵒᵖ) (x : (extPow n M).obj X) :
    (exteriorPowerMap n φ).app X x = exteriorPower.map n (φ.app X).hom x := rfl

lemma exteriorPowerMap_app_ιMulti (n : ℕ)
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (φ : M ⟶ N) (X : Cᵒᵖ) (m : Fin n → M.obj X) :
    (exteriorPowerMap n φ).app X (exteriorPower.ιMulti _ n m) =
      exteriorPower.ιMulti _ n (fun i => φ.app X (m i)) :=
  exteriorPower.map_apply_ιMulti _ _

variable (R) in
/-- **The exterior-power functor on presheaves of modules.** The functor sending a presheaf of
modules `M` to its sectionwise `n`-th exterior power `extPow n M` and a morphism `φ` to
`exteriorPowerMap n φ`. Modules and rings share the universe `u`, as for sheaves of modules on a
scheme; `extPow` itself also allows a larger module universe. -/
noncomputable def exteriorPowerFunctor (n : ℕ) :
    PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) ⥤
      PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) where
  obj M := extPow n M
  map φ := exteriorPowerMap n φ
  map_id M := by
    ext X : 1
    ext1
    refine LinearMap.ext fun x => ?_
    change exteriorPower.map n (𝟙 (M.obj X) : M.obj X ⟶ M.obj X).hom x = x
    rw [ModuleCat.hom_id, exteriorPower.map_id]
    rfl
  map_comp φ ψ := by
    ext X : 1
    ext1
    refine LinearMap.ext fun x => ?_
    change exteriorPower.map n (φ.app X ≫ ψ.app X).hom x =
      exteriorPower.map n (ψ.app X).hom (exteriorPower.map n (φ.app X).hom x)
    rw [ModuleCat.hom_comp, exteriorPower.map_comp]
    rfl

end PresheafOfModules
