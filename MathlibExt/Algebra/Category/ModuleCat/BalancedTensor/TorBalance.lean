/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensor.ProjectiveExact
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.BifunctorBalance

/-!
# Opposite-variable Tor balance

Projectivity of resolution terms supplies both exactness hypotheses of the
augmentation comparison. The modules are arbitrary; flatness, finite
generation and a choice of frame are not required.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ModuleCat.BalancedTensor

variable (R : Type u) [Ring R]
  [HasProjectiveResolutions (ModuleCat.{v} Rᵐᵒᵖ)]
  [HasProjectiveResolutions (ModuleCat.{v} R)]

/-- The actual two-variable Tor presentation obtained by deriving the left
module variable of the existing balanced tensor bifunctor. -/
abbrev torSecond (n : ℕ) : ModuleCat.{v} Rᵐᵒᵖ ⥤ ModuleCat.{v} R ⥤ AddCommGrpCat.{v} :=
  Functor.LeftDerivedBalance.deriveSecond (groupBifunctor R) n

/-- The actual two-variable Tor presentation obtained by deriving the right
module variable, retaining the same original variable order. -/
abbrev torFirst (n : ℕ) : ModuleCat.{v} Rᵐᵒᵖ ⥤ ModuleCat.{v} R ⥤ AddCommGrpCat.{v} :=
  Functor.LeftDerivedBalance.deriveFirst (groupBifunctor R) n

/-- Opposite-variable balance is earned from the two genuine projective
resolution augmentations and is natural in both original modules. -/
def torBalanceIso (n : ℕ) : torSecond R n ≅ torFirst R n :=
  Functor.LeftDerivedBalance.balanceIso (groupBifunctor R)
    (fun P hP => by
      let : Projective P := hP
      exact groupBifunctor_obj_preservesHomology_of_projective R P)
    (fun Q hQ => by
      let : Projective Q := hQ
      exact groupBifunctor_flip_obj_preservesHomology_of_projective R Q) n

/-- The canonical balance component retains both original homology objects. -/
def torBalanceObjIso (A : ModuleCat.{v} Rᵐᵒᵖ) (B : ModuleCat.{v} R) (n : ℕ) :
    ((torSecond R n).obj A).obj B ≅ ((torFirst R n).obj A).obj B :=
  ((torBalanceIso R n).app A).app B

/-- The comparison commutes with every genuine map of the original left coefficient. -/
theorem torBalance_hom_naturality_coefficient (A : ModuleCat.{v} Rᵐᵒᵖ)
    {B B' : ModuleCat.{v} R} (g : B ⟶ B') (n : ℕ) :
    ((torSecond R n).obj A).map g ≫ (torBalanceObjIso R A B' n).hom =
      (torBalanceObjIso R A B n).hom ≫ ((torFirst R n).obj A).map g :=
  ((torBalanceIso R n).app A).hom.naturality g

/-- The same canonical comparison commutes with every original right-module map. -/
theorem torBalance_hom_naturality_right
    {A A' : ModuleCat.{v} Rᵐᵒᵖ} (f : A ⟶ A') (B : ModuleCat.{v} R) (n : ℕ) :
    ((torSecond R n).map f).app B ≫ (torBalanceObjIso R A' B n).hom =
      (torBalanceObjIso R A B n).hom ≫ ((torFirst R n).map f).app B :=
  congrArg (fun t : (torSecond R n).obj A ⟶ (torFirst R n).obj A' => t.app B)
    ((torBalanceIso R n).hom.naturality f)

end ModuleCat.BalancedTensor
