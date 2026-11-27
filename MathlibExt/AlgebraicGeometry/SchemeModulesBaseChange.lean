/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicGeometry_ModulesBaseChangeHom.lean`,
`Theorems/Thm_AlgebraicGeometry_Scheme_Modules_baseChangeHom_comp_horizontal.lean`,
`P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_baseChangeHom_comp_horizontal.lean`,
`Theorems/Thm_AlgebraicGeometry_Scheme_Modules_unit_app_comp_pullbackComp_inv.lean`
and
`P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_unit_app_comp_pullbackComp_inv.lean`
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

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Base-change morphisms for sheaves of modules over schemes

For a commutative square of schemes

```
X' --g'--> X
|π'        |π
v          v
T' --ψ---> T
```

the mate of the pullback square under the pullback–pushforward adjunctions
is the canonical base-change morphism
`ψ^* π_* F ⟶ π'_* g'^* F`. This file defines that morphism and proves the
horizontal pasting law: base change along a composite of two squares is the
composite of the two base-change morphisms, conjugated by the canonical
pullback-composition isomorphisms. It does not assert that base change is
an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X T X' T' : Scheme.{u}} {π : X ⟶ T} {ψ : T' ⟶ T} {π' : X' ⟶ T'}
  {g' : X' ⟶ X}

noncomputable section

/-- The pullback 2-square attached to a commutative square of schemes,
built from the pullback-composition isomorphisms. -/
public def pullbackTwoSquare (h : g' ≫ π = π' ≫ ψ) :
    TwoSquare (pullback ψ) (pullback π) (pullback π') (pullback g') :=
  (pullbackComp π' ψ).hom ≫ (pullbackCongr h.symm).hom ≫ (pullbackComp g' π).inv

/-- The base-change natural transformation, defined as the mate of
`pullbackTwoSquare` under the pullback–pushforward adjunctions. -/
public def baseChangeNatTrans (h : g' ≫ π = π' ≫ ψ) :
    TwoSquare (pushforward π) (pullback g') (pullback ψ) (pushforward π') :=
  mateEquiv (pullbackPushforwardAdjunction π) (pullbackPushforwardAdjunction π')
    (pullbackTwoSquare h)

/-- The canonical base-change morphism
`ψ^* π_* F ⟶ π'_* g'^* F` for a commutative square of schemes. -/
public def baseChangeHom (h : g' ≫ π = π' ≫ ψ) (F : X.Modules) :
    (pullback ψ).obj ((pushforward π).obj F) ⟶
      (pushforward π').obj ((pullback g').obj F) :=
  (baseChangeNatTrans h).app F

/-- The component of the base-change transformation is the base-change
morphism. -/
public theorem baseChangeNatTrans_app (h : g' ≫ π = π' ≫ ψ) (F : X.Modules) :
    (baseChangeNatTrans h).app F = baseChangeHom h F :=
  rfl

/-- Naturality of the base-change morphism in the sheaf `F`. -/
public theorem baseChangeHom_naturality (h : g' ≫ π = π' ≫ ψ) {F G : X.Modules}
    (φ : F ⟶ G) :
    (pullback ψ).map ((pushforward π).map φ) ≫ baseChangeHom h G =
      baseChangeHom h F ≫ (pushforward π').map ((pullback g').map φ) :=
  (baseChangeNatTrans h).naturality φ

/-- The base-change morphism is characterized by its interaction with the
counit of the pullback–pushforward adjunction for `π'`. -/
public theorem baseChangeHom_counit (h : g' ≫ π = π' ≫ ψ) (F : X.Modules) :
    (pullback π').map (baseChangeHom h F) ≫
        (pullbackPushforwardAdjunction π').counit.app ((pullback g').obj F) =
      (pullbackTwoSquare h).app ((pushforward π).obj F) ≫
        (pullback g').map ((pullbackPushforwardAdjunction π).counit.app F) :=
  mateEquiv_counit (pullbackPushforwardAdjunction π)
    (pullbackPushforwardAdjunction π') (pullbackTwoSquare h) F

/-- The base-change morphism is characterized by its interaction with the
unit of the pullback–pushforward adjunction for `π`. -/
public theorem unit_baseChangeHom (h : g' ≫ π = π' ≫ ψ) (M : T.Modules) :
    (pullback ψ).map ((pullbackPushforwardAdjunction π).unit.app M) ≫
        baseChangeHom h ((pullback π).obj M) =
      (pullbackPushforwardAdjunction π').unit.app ((pullback ψ).obj M) ≫
        (pushforward π').map ((pullbackTwoSquare h).app M) :=
  unit_mateEquiv (pullbackPushforwardAdjunction π)
    (pullbackPushforwardAdjunction π') (pullbackTwoSquare h) M

section Adjoint

variable (π ψ π' g')

private theorem conjugateEquiv_pullbackCongr_hom {Y Z : Scheme.{u}}
    {f g : Y ⟶ Z} (e : f = g) :
    conjugateEquiv (pullbackPushforwardAdjunction g)
        (pullbackPushforwardAdjunction f) (pullbackCongr e).hom =
      (pushforwardCongr e).inv := by
  subst e
  have h1 : (pullbackCongr (rfl : f = f)).hom = 𝟙 _ := by simp [pullbackCongr]
  rw [h1, conjugateEquiv_id]
  ext M U : 3
  simp [pushforwardCongr_inv_app_app]

private theorem pushforwardCongr_symm_inv {Y Z : Scheme.{u}} {f g : Y ⟶ Z}
    (e : f = g) :
    (pushforwardCongr e.symm).inv = (pushforwardCongr e).hom := by
  ext M U : 3
  simp [pushforwardCongr_inv_app_app, pushforwardCongr_hom_app_app]

private theorem conjugateEquiv_pullbackComp_hom {W Y Z : Scheme.{u}}
    (f : W ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv (pullbackPushforwardAdjunction (f ≫ g))
        ((pullbackPushforwardAdjunction g).comp
          (pullbackPushforwardAdjunction f)) (pullbackComp f g).hom =
      (pushforwardComp f g).inv := by
  rw [← Iso.hom_comp_eq_id]
  rw [← conjugateEquiv_pullbackComp_inv f g]
  exact conjugateEquiv_comm _ _ (pullbackComp f g).hom_inv_id

private theorem conjugateEquiv_pullbackTwoSquare (h : g' ≫ π = π' ≫ ψ) :
    conjugateEquiv
        ((pullbackPushforwardAdjunction π).comp
          (pullbackPushforwardAdjunction g'))
        ((pullbackPushforwardAdjunction ψ).comp
          (pullbackPushforwardAdjunction π'))
        (pullbackTwoSquare h) =
      (pushforwardComp g' π).hom ≫ (pushforwardCongr h).hom ≫
        (pushforwardComp π' ψ).inv := by
  change conjugateEquiv _ _
    ((pullbackComp π' ψ).hom ≫ (pullbackCongr h.symm).hom ≫
      (pullbackComp g' π).inv) = _
  rw [← conjugateEquiv_comp _ (pullbackPushforwardAdjunction (π' ≫ ψ)),
    ← conjugateEquiv_comp _ (pullbackPushforwardAdjunction (g' ≫ π)),
    conjugateEquiv_pullbackComp_inv, conjugateEquiv_pullbackCongr_hom,
    pushforwardCongr_symm_inv, conjugateEquiv_pullbackComp_hom, Category.assoc]

private theorem pullbackPushforwardAdjunction_homEquiv_baseChangeHom
    (h : g' ≫ π = π' ≫ ψ) (F : X.Modules) :
    (pullbackPushforwardAdjunction ψ).homEquiv _ _ (baseChangeHom h F) =
      (pushforward π).map ((pullbackPushforwardAdjunction g').unit.app F) ≫
        (pushforwardComp g' π).hom.app _ ≫ (pushforwardCongr h).hom.app _ ≫
          (pushforwardComp π' ψ).inv.app _ := by
  have key := unit_mateEquiv (pullbackPushforwardAdjunction g')
    (pullbackPushforwardAdjunction ψ) (baseChangeNatTrans h) F
  have it := iterated_mateEquiv_conjugateEquiv
    (pullbackPushforwardAdjunction π) (pullbackPushforwardAdjunction π')
    (pullbackPushforwardAdjunction ψ) (pullbackPushforwardAdjunction g')
    (pullbackTwoSquare h)
  rw [conjugateEquiv_pullbackTwoSquare] at it
  have it' := NatTrans.congr_app it ((pullback g').obj F)
  simp only [NatTrans.comp_app] at it'
  rw [Adjunction.homEquiv_unit]
  have key' : (pullbackPushforwardAdjunction ψ).unit.app
        ((pushforward π).obj F) ≫
      (pushforward ψ).map ((baseChangeNatTrans h).app F) =
      (pushforward π).map ((pullbackPushforwardAdjunction g').unit.app F) ≫
        (mateEquiv (pullbackPushforwardAdjunction g')
          (pullbackPushforwardAdjunction ψ)
          (baseChangeNatTrans h)).app ((pullback g').obj F) := key.symm
  change (pullbackPushforwardAdjunction ψ).unit.app ((pushforward π).obj F) ≫
      (pushforward ψ).map ((baseChangeNatTrans h).app F) = _
  rw [key']
  exact congrArg
    (fun t => (pushforward π).map
      ((pullbackPushforwardAdjunction g').unit.app F) ≫ t) it'

/-- On sections over an open `U`, precomposition with the unit for `ψ`
followed by the base-change morphism is the unit for `g'` followed by
restriction along the equality of preimages given by the square. -/
public theorem unit_app_app_comp_baseChangeHom_app (h : g' ≫ π = π' ≫ ψ)
    (F : X.Modules) (U : T.Opens) :
    ((pullbackPushforwardAdjunction ψ).unit.app
        ((pushforward π).obj F)).app U ≫
        (baseChangeHom h F).app (ψ ⁻¹ᵁ U) =
      ((pullbackPushforwardAdjunction g').unit.app F).app (π ⁻¹ᵁ U) ≫
        ((pullback g').obj F).presheaf.map
          (eqToHom (show (π' ≫ ψ) ⁻¹ᵁ U = (g' ≫ π) ⁻¹ᵁ U by rw [h])).op := by
  have e := congrArg (fun t => Hom.app t U)
    (pullbackPushforwardAdjunction_homEquiv_baseChangeHom π ψ π' g' h F)
  simp only [Adjunction.homEquiv_unit, Hom.comp_app] at e
  exact e

end Adjoint

/-- On sections, the unit for a composite pullback, followed by the inverse
of the pullback-composition isomorphism, is the composite of the two units. -/
private theorem unit_app_comp_pullbackComp_inv {X Y Z : Scheme.{u}}
    (g : Z ⟶ Y) (f : Y ⟶ X) (M : X.Modules) (U : X.Opens) :
    ((pullbackPushforwardAdjunction (g ≫ f)).unit.app M).app U ≫
        ((pullbackComp g f).inv.app M).app ((g ≫ f) ⁻¹ᵁ U) =
      ((pullbackPushforwardAdjunction f).unit.app M).app U ≫
        ((pullbackPushforwardAdjunction g).unit.app
          ((pullback f).obj M)).app (f ⁻¹ᵁ U) := by
  have h := unit_conjugateEquiv
    ((pullbackPushforwardAdjunction f).comp
      (pullbackPushforwardAdjunction g))
    (pullbackPushforwardAdjunction (g ≫ f)) (pullbackComp g f).inv M
  rw [conjugateEquiv_pullbackComp_inv] at h
  have h' := congrArg (fun t => Hom.app t U) h
  simp only [Hom.comp_app, Adjunction.comp_unit_app, pushforward_map_app,
    pushforwardComp_hom_app_app, Functor.comp_obj] at h'
  erw [Category.comp_id] at h'
  exact h'.symm

private theorem map_eqToHom_comp_app {Y : Scheme.{u}} {M N : Y.Modules}
    (φ : M ⟶ N) {U V : Y.Opens} (e : U = V) :
    M.presheaf.map (eqToHom e).op ≫ φ.app U =
      φ.app V ≫ N.presheaf.map (eqToHom e).op := by
  subst e; simp

private theorem map_eqToHom_comp_map_eqToHom {Y : Scheme.{u}} (M : Y.Modules)
    {A₁ A₂ B₁ : Y.Opens} (a : A₁ = A₂) (b : B₁ = A₁) :
    M.presheaf.map (eqToHom a).op ≫ M.presheaf.map (eqToHom b).op =
      M.presheaf.map (eqToHom (b.trans a)).op := by
  subst a; subst b; simp

private theorem ext_of_unit_app_comp {T T' : Scheme.{u}} (ψ : T' ⟶ T)
    {M : T.Modules} {N : T'.Modules} (f₁ f₂ : (pullback ψ).obj M ⟶ N)
    (h : ∀ U : T.Opens,
      ((pullbackPushforwardAdjunction ψ).unit.app M).app U ≫
          f₁.app (ψ ⁻¹ᵁ U) =
        ((pullbackPushforwardAdjunction ψ).unit.app M).app U ≫
          f₂.app (ψ ⁻¹ᵁ U)) :
    f₁ = f₂ := by
  apply ((pullbackPushforwardAdjunction ψ).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine hom_ext _ _ fun U => ?_
  exact h U

private theorem inv_app_map_eqToHom_hom_app {Y : Scheme.{u}}
    {P Q : Y.Modules} (c : P ≅ Q) {W₁ W₃ : Y.Opens} (e : W₃ = W₁) :
    c.inv.app W₁ ≫ P.presheaf.map (eqToHom e).op ≫ c.hom.app W₃ =
      Q.presheaf.map (eqToHom e).op := by
  subst e
  simp [← Hom.comp_app]

/-- The composite of two horizontally adjacent commutative squares of
schemes is commutative. -/
public theorem comp_eq_of_horizontal
    {X T X' T' X'' T'' : Scheme.{u}} {π : X ⟶ T} {ψ : T' ⟶ T}
    {π' : X' ⟶ T'} {g' : X' ⟶ X} {ψ' : T'' ⟶ T'} {π'' : X'' ⟶ T''}
    {g'' : X'' ⟶ X'}
    (h₁ : g' ≫ π = π' ≫ ψ) (h₂ : g'' ≫ π' = π'' ≫ ψ') :
    (g'' ≫ g') ≫ π = π'' ≫ (ψ' ≫ ψ) := by
  calc (g'' ≫ g') ≫ π = g'' ≫ g' ≫ π := Category.assoc _ _ _
    _ = g'' ≫ (π' ≫ ψ) := by rw [h₁]
    _ = (g'' ≫ π') ≫ ψ := (Category.assoc _ _ _).symm
    _ = (π'' ≫ ψ') ≫ ψ := by rw [h₂]
    _ = π'' ≫ ψ' ≫ ψ := Category.assoc _ _ _

set_option maxHeartbeats 1600000 in
/-- Horizontal pasting of base-change morphisms: for two horizontally
adjacent commutative squares of schemes, the base-change morphism for the
composite square is the composite of the base-change morphisms for the two
squares, conjugated by the pullback-composition isomorphisms. -/
public theorem baseChangeHom_comp_horizontal
    {X T X' T' X'' T'' : Scheme.{u}} {π : X ⟶ T} {ψ : T' ⟶ T}
    {π' : X' ⟶ T'} {g' : X' ⟶ X} {ψ' : T'' ⟶ T'} {π'' : X'' ⟶ T''}
    {g'' : X'' ⟶ X'}
    (h₁ : g' ≫ π = π' ≫ ψ) (h₂ : g'' ≫ π' = π'' ≫ ψ') (F : X.Modules) :
    baseChangeHom (comp_eq_of_horizontal h₁ h₂) F =
      (pullbackComp ψ' ψ).inv.app ((pushforward π).obj F) ≫
        (pullback ψ').map (baseChangeHom h₁ F) ≫
          baseChangeHom h₂ ((pullback g').obj F) ≫
            (pushforward π'').map ((pullbackComp g'' g').hom.app F) := by
  have h₁₂ : (g'' ≫ g') ≫ π = π'' ≫ (ψ' ≫ ψ) :=
    comp_eq_of_horizontal h₁ h₂
  apply ext_of_unit_app_comp (ψ' ≫ ψ)
  intro U
  have e₁ : (π' ≫ ψ) ⁻¹ᵁ U = (g' ≫ π) ⁻¹ᵁ U := by rw [h₁]
  have e₂ : (π'' ≫ ψ') ⁻¹ᵁ (ψ ⁻¹ᵁ U) = (g'' ≫ π') ⁻¹ᵁ (ψ ⁻¹ᵁ U) := by
    rw [h₂]
  have e₁g : g'' ⁻¹ᵁ ((π' ≫ ψ) ⁻¹ᵁ U) = g'' ⁻¹ᵁ ((g' ≫ π) ⁻¹ᵁ U) := by
    rw [h₁]
  rw [unit_app_app_comp_baseChangeHom_app π (ψ' ≫ ψ) π'' (g'' ≫ g') h₁₂ F U]
  have s0 : ((pullbackPushforwardAdjunction (ψ' ≫ ψ)).unit.app
        ((pushforward π).obj F)).app U ≫
      ((pullbackComp ψ' ψ).inv.app ((pushforward π).obj F)).app
        ((ψ' ≫ ψ) ⁻¹ᵁ U) =
      ((pullbackPushforwardAdjunction ψ).unit.app
          ((pushforward π).obj F)).app U ≫
        ((pullbackPushforwardAdjunction ψ').unit.app
          ((pullback ψ).obj ((pushforward π).obj F))).app (ψ ⁻¹ᵁ U) :=
    unit_app_comp_pullbackComp_inv ψ' ψ ((pushforward π).obj F) U
  show _ = (((pullbackPushforwardAdjunction (ψ' ≫ ψ)).unit.app
      ((pushforward π).obj F)).app U ≫
    ((pullbackComp ψ' ψ).inv.app ((pushforward π).obj F)).app
      ((ψ' ≫ ψ) ⁻¹ᵁ U)) ≫
    ((pullback ψ').map (baseChangeHom h₁ F)).app ((ψ' ≫ ψ) ⁻¹ᵁ U) ≫
    (baseChangeHom h₂ ((pullback g').obj F)).app ((ψ' ≫ ψ) ⁻¹ᵁ U) ≫
    ((pullbackComp g'' g').hom.app F).app (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U))
  erw [s0]
  have s1 : ((pullbackPushforwardAdjunction ψ').unit.app
        ((pullback ψ).obj ((pushforward π).obj F))).app (ψ ⁻¹ᵁ U) ≫
      ((pullback ψ').map (baseChangeHom h₁ F)).app ((ψ' ≫ ψ) ⁻¹ᵁ U) =
      (baseChangeHom h₁ F).app (ψ ⁻¹ᵁ U) ≫
        ((pullbackPushforwardAdjunction ψ').unit.app
          ((pushforward π').obj ((pullback g').obj F))).app (ψ ⁻¹ᵁ U) := by
    have n := congrArg (fun t => Hom.app t (ψ ⁻¹ᵁ U))
      ((pullbackPushforwardAdjunction ψ').unit.naturality
        (baseChangeHom h₁ F))
    simp only [Functor.id_map, Functor.comp_map, Hom.comp_app] at n
    exact n.symm
  show _ = ((pullbackPushforwardAdjunction ψ).unit.app
      ((pushforward π).obj F)).app U ≫
    (((pullbackPushforwardAdjunction ψ').unit.app
        ((pullback ψ).obj ((pushforward π).obj F))).app (ψ ⁻¹ᵁ U) ≫
      ((pullback ψ').map (baseChangeHom h₁ F)).app
        ((ψ' ≫ ψ) ⁻¹ᵁ U)) ≫
    (baseChangeHom h₂ ((pullback g').obj F)).app ((ψ' ≫ ψ) ⁻¹ᵁ U) ≫
    ((pullbackComp g'' g').hom.app F).app (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U))
  erw [s1]
  have t1 : ((pullbackPushforwardAdjunction ψ).unit.app
        ((pushforward π).obj F)).app U ≫
      (baseChangeHom h₁ F).app (ψ ⁻¹ᵁ U) =
      ((pullbackPushforwardAdjunction g').unit.app F).app (π ⁻¹ᵁ U) ≫
        ((pullback g').obj F).presheaf.map (eqToHom e₁).op :=
    unit_app_app_comp_baseChangeHom_app π ψ π' g' h₁ F U
  show _ = (((pullbackPushforwardAdjunction ψ).unit.app
      ((pushforward π).obj F)).app U ≫
    (baseChangeHom h₁ F).app (ψ ⁻¹ᵁ U)) ≫
    ((pullbackPushforwardAdjunction ψ').unit.app
      ((pushforward π').obj ((pullback g').obj F))).app (ψ ⁻¹ᵁ U) ≫
    (baseChangeHom h₂ ((pullback g').obj F)).app ((ψ' ≫ ψ) ⁻¹ᵁ U) ≫
    ((pullbackComp g'' g').hom.app F).app (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U))
  erw [t1]
  have t2 : ((pullbackPushforwardAdjunction ψ').unit.app
        ((pushforward π').obj ((pullback g').obj F))).app (ψ ⁻¹ᵁ U) ≫
      (baseChangeHom h₂ ((pullback g').obj F)).app ((ψ' ≫ ψ) ⁻¹ᵁ U) =
      ((pullbackPushforwardAdjunction g'').unit.app
          ((pullback g').obj F)).app (π' ⁻¹ᵁ (ψ ⁻¹ᵁ U)) ≫
        ((pullback g'').obj ((pullback g').obj F)).presheaf.map
          (eqToHom e₂).op :=
    unit_app_app_comp_baseChangeHom_app π' ψ' π'' g'' h₂
      ((pullback g').obj F) (ψ ⁻¹ᵁ U)
  show _ = ((pullbackPushforwardAdjunction g').unit.app F).app
      (π ⁻¹ᵁ U) ≫ ((pullback g').obj F).presheaf.map (eqToHom e₁).op ≫
    (((pullbackPushforwardAdjunction ψ').unit.app
        ((pushforward π').obj ((pullback g').obj F))).app (ψ ⁻¹ᵁ U) ≫
      (baseChangeHom h₂ ((pullback g').obj F)).app
        ((ψ' ≫ ψ) ⁻¹ᵁ U)) ≫
    ((pullbackComp g'' g').hom.app F).app (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U))
  erw [t2]
  have u4 : ((pullback g').obj F).presheaf.map (eqToHom e₁).op ≫
      ((pullbackPushforwardAdjunction g'').unit.app
          ((pullback g').obj F)).app (π' ⁻¹ᵁ (ψ ⁻¹ᵁ U)) =
      ((pullbackPushforwardAdjunction g'').unit.app
          ((pullback g').obj F)).app (g' ⁻¹ᵁ (π ⁻¹ᵁ U)) ≫
        ((pullback g'').obj ((pullback g').obj F)).presheaf.map
          (eqToHom e₁g).op :=
    map_eqToHom_comp_app
      ((pullbackPushforwardAdjunction g'').unit.app ((pullback g').obj F)) e₁
  show _ = ((pullbackPushforwardAdjunction g').unit.app F).app
      (π ⁻¹ᵁ U) ≫
    (((pullback g').obj F).presheaf.map (eqToHom e₁).op ≫
      ((pullbackPushforwardAdjunction g'').unit.app
          ((pullback g').obj F)).app (π' ⁻¹ᵁ (ψ ⁻¹ᵁ U))) ≫
    ((pullback g'').obj ((pullback g').obj F)).presheaf.map
      (eqToHom e₂).op ≫
    ((pullbackComp g'' g').hom.app F).app (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U))
  erw [u4]
  have s3 : ((pullbackPushforwardAdjunction (g'' ≫ g')).unit.app F).app
        (π ⁻¹ᵁ U) ≫
      ((pullbackComp g'' g').inv.app F).app ((g'' ≫ g') ⁻¹ᵁ (π ⁻¹ᵁ U)) =
      ((pullbackPushforwardAdjunction g').unit.app F).app (π ⁻¹ᵁ U) ≫
        ((pullbackPushforwardAdjunction g'').unit.app
          ((pullback g').obj F)).app (g' ⁻¹ᵁ (π ⁻¹ᵁ U)) :=
    unit_app_comp_pullbackComp_inv g'' g' F (π ⁻¹ᵁ U)
  show _ = (((pullbackPushforwardAdjunction g').unit.app F).app
      (π ⁻¹ᵁ U) ≫
    ((pullbackPushforwardAdjunction g'').unit.app
        ((pullback g').obj F)).app (g' ⁻¹ᵁ (π ⁻¹ᵁ U))) ≫
    ((pullback g'').obj ((pullback g').obj F)).presheaf.map
      (eqToHom e₁g).op ≫
    ((pullback g'').obj ((pullback g').obj F)).presheaf.map
      (eqToHom e₂).op ≫
    ((pullbackComp g'' g').hom.app F).app (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U))
  erw [← s3]
  have m : ((pullback g'').obj ((pullback g').obj F)).presheaf.map
        (eqToHom e₁g).op ≫
      ((pullback g'').obj ((pullback g').obj F)).presheaf.map
        (eqToHom e₂).op =
      ((pullback g'').obj ((pullback g').obj F)).presheaf.map
        (eqToHom (e₂.trans e₁g)).op :=
    map_eqToHom_comp_map_eqToHom
      ((pullback g'').obj ((pullback g').obj F)) e₁g e₂
  show _ = ((pullbackPushforwardAdjunction (g'' ≫ g')).unit.app F).app
      (π ⁻¹ᵁ U) ≫
    ((pullbackComp g'' g').inv.app F).app ((g'' ≫ g') ⁻¹ᵁ (π ⁻¹ᵁ U)) ≫
    (((pullback g'').obj ((pullback g').obj F)).presheaf.map
        (eqToHom e₁g).op ≫
      ((pullback g'').obj ((pullback g').obj F)).presheaf.map
        (eqToHom e₂).op) ≫
    ((pullbackComp g'' g').hom.app F).app (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U))
  erw [m]
  have fin : ((pullbackComp g'' g').inv.app F).app
        ((g'' ≫ g') ⁻¹ᵁ (π ⁻¹ᵁ U)) ≫
      ((pullback g'').obj ((pullback g').obj F)).presheaf.map
        (eqToHom (e₂.trans e₁g)).op ≫
      ((pullbackComp g'' g').hom.app F).app
        (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U)) =
      ((pullback (g'' ≫ g')).obj F).presheaf.map
        (eqToHom (e₂.trans e₁g)).op :=
    inv_app_map_eqToHom_hom_app ((pullbackComp g'' g').app F) (e₂.trans e₁g)
  show _ = ((pullbackPushforwardAdjunction (g'' ≫ g')).unit.app F).app
      (π ⁻¹ᵁ U) ≫
    (((pullbackComp g'' g').inv.app F).app
        ((g'' ≫ g') ⁻¹ᵁ (π ⁻¹ᵁ U)) ≫
      ((pullback g'').obj ((pullback g').obj F)).presheaf.map
        (eqToHom (e₂.trans e₁g)).op ≫
      ((pullbackComp g'' g').hom.app F).app
        (π'' ⁻¹ᵁ ((ψ' ≫ ψ) ⁻¹ᵁ U)))
  erw [fin]
  rfl

end

end AlgebraicGeometry.Scheme.Modules
