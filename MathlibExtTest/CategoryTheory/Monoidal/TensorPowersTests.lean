/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.Monoidal.TensorPowers

/-!
# Generic finite tensor-power public contract tests

Selective compile-time checks for the generic `tensorPowObj` / `tensorPowMap` /
`tensorPowObj_add` API in an arbitrary monoidal category: zero/successor
computation, non-identity functoriality, add-iso unit laws, add-iso naturality,
one concrete symbolic associativity-coherence instance, and one direct
right-whisker transport consumer.

Each check is a direct generic invocation over `C`, `X/Y/Z`, and non-identity
symbolic maps; no production argument is re-proved, no concrete instance is
constructed, and no DG/`ModuleCat` fixture is used.

Nonclaims: no infinite sums, no (co)free objects, no filtrations,
completeness, adjunction, or derived/Koszul results here. These tests pin
semantics, not definitional transports; the transport consumer pins the
reusable `tensorPowObj_eqToHom_whiskerRight` corollary rather than reproving it.
-/

open CategoryTheory MonoidalCategory

namespace MathlibExtTest.GenericTensorPowers

universe v u vD uD

noncomputable section

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {X Y Z : C}

section PowComputation

example (X : C) : TensorPower.tensorPowObj X 0 = 𝟙_ C :=
  TensorPower.tensorPowObj_zero X

example (X : C) (n : ℕ) :
    TensorPower.tensorPowObj X (n + 1) = TensorPower.tensorPowObj X n ⊗ X :=
  TensorPower.tensorPowObj_succ X n

example {X Y : C} (f : X ⟶ Y) :
    TensorPower.tensorPowMap f 0 = 𝟙 _ :=
  TensorPower.tensorPowMap_zero f

example {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    TensorPower.tensorPowMap f (n + 1) =
      TensorPower.tensorPowMap f n ⊗ₘ f :=
  TensorPower.tensorPowMap_succ f n

end PowComputation

section Functoriality

example (X : C) (n : ℕ) :
    TensorPower.tensorPowMap (𝟙 X) n = 𝟙 _ :=
  TensorPower.tensorPowMap_id X n

example {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    TensorPower.tensorPowMap (f ≫ g) n =
      TensorPower.tensorPowMap f n ≫ TensorPower.tensorPowMap g n :=
  TensorPower.tensorPowMap_comp f g n

end Functoriality

section AddUnit

example (X : C) (m : ℕ) :
    (TensorPower.tensorPowObj_add X m 0).hom =
      (rightUnitor _).symm.hom :=
  TensorPower.tensorPowObj_add_zero_right X m

example (X : C) (n : ℕ) :
    (TensorPower.tensorPowObj_add X 0 n).hom ≫
        (leftUnitor (TensorPower.tensorPowObj X n)).hom =
      (eqToIso (congrArg (TensorPower.tensorPowObj X) (Nat.zero_add n))).hom :=
  TensorPower.tensorPowObj_add_zero_left X n

end AddUnit

section AddNaturality

example {X Y : C} (f : X ⟶ Y) (m n : ℕ) :
    TensorPower.tensorPowMap f (m + n) ≫
        (TensorPower.tensorPowObj_add Y m n).hom =
      (TensorPower.tensorPowObj_add X m n).hom ≫
        (TensorPower.tensorPowMap f m ⊗ₘ TensorPower.tensorPowMap f n) :=
  TensorPower.tensorPowObj_add_naturality f m n

end AddNaturality

section AddAssoc

example (X : C) :
    (eqToIso (congrArg (TensorPower.tensorPowObj X)
      (Nat.add_assoc 1 1 1))).hom ≫
        (TensorPower.tensorPowObj_add X 1 (1 + 1)).hom ≫
        (𝟙 _ ⊗ₘ (TensorPower.tensorPowObj_add X 1 1).hom) =
      (TensorPower.tensorPowObj_add X (1 + 1) 1).hom ≫
        ((TensorPower.tensorPowObj_add X 1 1).hom ⊗ₘ 𝟙 _) ≫
        (associator _ _ _).hom :=
  TensorPower.tensorPowObj_add_assoc X 1 1 1

end AddAssoc

section Transport

example (X : C) {a b : ℕ} (h : a = b) :
    ((eqToIso (congrArg (TensorPower.tensorPowObj X) h)).hom ⊗ₘ 𝟙 X) =
      (eqToIso (congrArg (fun k => TensorPower.tensorPowObj X k ⊗ X) h)).hom :=
  TensorPower.tensorPowObj_eqToHom_whiskerRight X h

end Transport

section LaxMonoidalImage

variable {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
variable (G : C ⥤ D) [G.LaxMonoidal]

example (X : C) (p q : ℕ) :
    G.obj (TensorPower.tensorPowObj X p) ⊗
        G.obj (TensorPower.tensorPowObj X q) ⟶
      G.obj (TensorPower.tensorPowObj X (p + q)) :=
  TensorPower.laxTensorPowerPairing G X p q

example (X : C) :
    𝟙_ D ⟶ G.obj (TensorPower.tensorPowObj X 0) :=
  TensorPower.laxTensorPowerUnit G X

example {X Y : C} (f : X ⟶ Y) (p q : ℕ) :
    (G.map (TensorPower.tensorPowMap f p) ⊗ₘ
        G.map (TensorPower.tensorPowMap f q)) ≫
        TensorPower.laxTensorPowerPairing G Y p q =
      TensorPower.laxTensorPowerPairing G X p q ≫
        G.map (TensorPower.tensorPowMap f (p + q)) :=
  TensorPower.laxTensorPowerPairing_naturality G f p q

example (X : C) (p : ℕ) :
    (TensorPower.laxTensorPowerUnit G X ▷
        G.obj (TensorPower.tensorPowObj X p)) ≫
        TensorPower.laxTensorPowerPairing G X 0 p =
      (λ_ (G.obj (TensorPower.tensorPowObj X p))).hom ≫
        eqToHom (congrArg
          (fun n ↦ G.obj (TensorPower.tensorPowObj X n))
          (Nat.zero_add p).symm) :=
  TensorPower.laxTensorPowerPairing_zero_left G X p

example (X : C) (p : ℕ) :
    (G.obj (TensorPower.tensorPowObj X p) ◁
        TensorPower.laxTensorPowerUnit G X) ≫
        TensorPower.laxTensorPowerPairing G X p 0 =
      (ρ_ (G.obj (TensorPower.tensorPowObj X p))).hom :=
  TensorPower.laxTensorPowerPairing_zero_right G X p

example (X : C) (p q r : ℕ) :
    (TensorPower.laxTensorPowerPairing G X p q ⊗ₘ
        𝟙 (G.obj (TensorPower.tensorPowObj X r))) ≫
        TensorPower.laxTensorPowerPairing G X (p + q) r ≫
        eqToHom (congrArg
          (fun n ↦ G.obj (TensorPower.tensorPowObj X n))
          (Nat.add_assoc p q r)) =
      (α_ (G.obj (TensorPower.tensorPowObj X p))
        (G.obj (TensorPower.tensorPowObj X q))
        (G.obj (TensorPower.tensorPowObj X r))).hom ≫
        (𝟙 (G.obj (TensorPower.tensorPowObj X p)) ⊗ₘ
          TensorPower.laxTensorPowerPairing G X q r) ≫
        TensorPower.laxTensorPowerPairing G X p (q + r) :=
  TensorPower.laxTensorPowerPairing_assoc G X p q r

end LaxMonoidalImage

section LaxMonoidalUniverses

variable {C₀ D₀ : Type 0}
  [Category.{0} C₀] [MonoidalCategory C₀]
  [Category.{0} D₀] [MonoidalCategory D₀]
  (G₀ : C₀ ⥤ D₀) [G₀.LaxMonoidal]

example (X : C₀) := TensorPower.laxTensorPowerPairing G₀ X 1 2

variable {C₁ D₁ : Type 1}
  [Category.{1} C₁] [MonoidalCategory C₁]
  [Category.{1} D₁] [MonoidalCategory D₁]
  (G₁ : C₁ ⥤ D₁) [G₁.LaxMonoidal]

example (X : C₁) := TensorPower.laxTensorPowerPairing G₁ X 2 1

end LaxMonoidalUniverses

section LaxMonoidalMixedUniverses

variable {C₀ : Type 0} [Category.{0} C₀] [MonoidalCategory C₀]
variable {D₁ : Type 1} [Category.{1} D₁] [MonoidalCategory D₁]
variable (G₀₁ : C₀ ⥤ D₁) [G₀₁.LaxMonoidal]

/-- The source and target object and morphism universes are genuinely
independent. -/
example (X : C₀) :
    G₀₁.obj (TensorPower.tensorPowObj X 1) ⊗
        G₀₁.obj (TensorPower.tensorPowObj X 2) ⟶
      G₀₁.obj (TensorPower.tensorPowObj X (1 + 2)) :=
  TensorPower.laxTensorPowerPairing G₀₁ X 1 2

end LaxMonoidalMixedUniverses

end

end MathlibExtTest.GenericTensorPowers
