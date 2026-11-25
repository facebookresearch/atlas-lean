/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.SchemeModulesBaseChange

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

-- exactSource consumer: the original three-hypothesis form, deriving
-- the composite-square equality from the two square equalities
-- (`Scheme.{0}`).
example {X T X' T' X'' T'' : Scheme.{0}} {π : X ⟶ T} {ψ : T' ⟶ T}
    {π' : X' ⟶ T'} {g' : X' ⟶ X} {ψ' : T'' ⟶ T'} {π'' : X'' ⟶ T''}
    {g'' : X'' ⟶ X'}
    (h₁ : g' ≫ π = π' ≫ ψ) (h₂ : g'' ≫ π' = π'' ≫ ψ')
    (h₁₂ : (g'' ≫ g') ≫ π = π'' ≫ (ψ' ≫ ψ)) (F : X.Modules) :
    Scheme.Modules.baseChangeHom h₁₂ F =
      (Scheme.Modules.pullbackComp ψ' ψ).inv.app
          ((Scheme.Modules.pushforward π).obj F) ≫
        (Scheme.Modules.pullback ψ').map
          (Scheme.Modules.baseChangeHom h₁ F) ≫
          Scheme.Modules.baseChangeHom h₂
            ((Scheme.Modules.pullback g').obj F) ≫
            (Scheme.Modules.pushforward π'').map
              ((Scheme.Modules.pullbackComp g'' g').hom.app F) :=
  Scheme.Modules.baseChangeHom_comp_horizontal h₁ h₂ F

-- Higher-universe consumer (`Scheme.{1}`), in the same
-- three-hypothesis form.
example {X T X' T' X'' T'' : Scheme.{1}} {π : X ⟶ T} {ψ : T' ⟶ T}
    {π' : X' ⟶ T'} {g' : X' ⟶ X} {ψ' : T'' ⟶ T'} {π'' : X'' ⟶ T''}
    {g'' : X'' ⟶ X'}
    (h₁ : g' ≫ π = π' ≫ ψ) (h₂ : g'' ≫ π' = π'' ≫ ψ')
    (h₁₂ : (g'' ≫ g') ≫ π = π'' ≫ (ψ' ≫ ψ)) (F : X.Modules) :
    Scheme.Modules.baseChangeHom h₁₂ F =
      (Scheme.Modules.pullbackComp ψ' ψ).inv.app
          ((Scheme.Modules.pushforward π).obj F) ≫
        (Scheme.Modules.pullback ψ').map
          (Scheme.Modules.baseChangeHom h₁ F) ≫
          Scheme.Modules.baseChangeHom h₂
            ((Scheme.Modules.pullback g').obj F) ≫
            (Scheme.Modules.pushforward π'').map
              ((Scheme.Modules.pullbackComp g'' g').hom.app F) :=
  Scheme.Modules.baseChangeHom_comp_horizontal h₁ h₂ F

-- Boundary case: all schemes are equal and every map is the identity.
-- The pasting law then relates base-change morphisms for identity
-- squares. The composite-square equality is redundant: it follows
-- from the two square equalities by reassociation.
example {X : Scheme.{0}} (F : X.Modules) :
    Scheme.Modules.baseChangeHom
        (show (𝟙 X ≫ 𝟙 X) ≫ 𝟙 X = 𝟙 X ≫ (𝟙 X ≫ 𝟙 X) by simp) F =
      (Scheme.Modules.pullbackComp (𝟙 X) (𝟙 X)).inv.app
          ((Scheme.Modules.pushforward (𝟙 X)).obj F) ≫
        (Scheme.Modules.pullback (𝟙 X)).map
          (Scheme.Modules.baseChangeHom
            (show 𝟙 X ≫ 𝟙 X = 𝟙 X ≫ 𝟙 X by simp) F) ≫
          Scheme.Modules.baseChangeHom
            (show 𝟙 X ≫ 𝟙 X = 𝟙 X ≫ 𝟙 X by simp)
            ((Scheme.Modules.pullback (𝟙 X)).obj F) ≫
            (Scheme.Modules.pushforward (𝟙 X)).map
              ((Scheme.Modules.pullbackComp (𝟙 X) (𝟙 X)).hom.app F) :=
  Scheme.Modules.baseChangeHom_comp_horizontal
    (show 𝟙 X ≫ 𝟙 X = 𝟙 X ≫ 𝟙 X by simp)
    (show 𝟙 X ≫ 𝟙 X = 𝟙 X ≫ 𝟙 X by simp) F
