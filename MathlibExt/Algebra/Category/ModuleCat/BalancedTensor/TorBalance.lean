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
# Balanced Tor in the two module variables

Let `R` be an associative ring, and assume the right and left module categories in carrier
universe `v` have projective resolutions. Deriving the balanced tensor bifunctor in the left
module gives `torSecond`, while deriving it in the right module gives `torFirst`; both retain
the variable order `(right module, left module)`.

Projective modules make tensoring exact in the opposite variable. This gives a natural
isomorphism between the two derived bifunctors in every natural degree, for arbitrary input
modules. The balance coordinate commutes with maps in each module variable, and the ring
universe remains independent of `v`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ModuleCat.BalancedTensor

variable (R : Type u) [Ring R]
  [HasProjectiveResolutions (ModuleCat.{v} Rᵐᵒᵖ)]
  [HasProjectiveResolutions (ModuleCat.{v} R)]

/-- Tor obtained by deriving the left-module variable.

In natural degree `n`, derive the second variable of the group-valued balanced tensor
bifunctor. The resulting bifunctor takes a right module `A` and a left module `B` to the Tor
group computed from a projective resolution of `B`. -/
abbrev torSecond (n : ℕ) : ModuleCat.{v} Rᵐᵒᵖ ⥤ ModuleCat.{v} R ⥤ AddCommGrpCat.{v} :=
  Functor.LeftDerivedBalance.deriveSecond (groupBifunctor R) n

/-- Tor obtained by deriving the right-module variable.

In natural degree `n`, derive the first variable of the group-valued balanced tensor bifunctor
and retain the right-then-left variable order. The computation uses a projective resolution of
the right module. -/
abbrev torFirst (n : ℕ) : ModuleCat.{v} Rᵐᵒᵖ ⥤ ModuleCat.{v} R ⥤ AddCommGrpCat.{v} :=
  Functor.LeftDerivedBalance.deriveFirst (groupBifunctor R) n

/-- Natural balance isomorphism between the two Tor derivations.

Assuming projective resolutions in both module categories, the second-variable and first-
variable derived tensor bifunctors are naturally isomorphic in every natural degree `n`.
Tensoring with projective resolution terms supplies the required exactness in the other
variable. -/
def torBalanceIso (n : ℕ) : torSecond R n ≅ torFirst R n :=
  Functor.LeftDerivedBalance.balanceIso (groupBifunctor R)
    (fun P hP => by
      let : Projective P := hP
      exact groupBifunctor_obj_preservesHomology_of_projective R P)
    (fun Q hQ => by
      let : Projective Q := hQ
      exact groupBifunctor_flip_obj_preservesHomology_of_projective R Q) n

/-- Tor balance isomorphism at a pair of modules.

For a right module `A`, left module `B`, and natural `n`, evaluate the balance natural
isomorphism to obtain `torSecond R n A B ≅ torFirst R n A B`. -/
def torBalanceObjIso (A : ModuleCat.{v} Rᵐᵒᵖ) (B : ModuleCat.{v} R) (n : ℕ) :
    ((torSecond R n).obj A).obj B ≅ ((torFirst R n).obj A).obj B :=
  ((torBalanceIso R n).app A).app B

/-- Tor balance coordinate is natural in the left module.

For `g : B ⟶ B'`, the second-variable Tor map followed by the balance coordinate at `(A, B')`
equals the coordinate at `(A, B)` followed by the first-variable Tor map. -/
theorem torBalance_hom_naturality_coefficient (A : ModuleCat.{v} Rᵐᵒᵖ)
    {B B' : ModuleCat.{v} R} (g : B ⟶ B') (n : ℕ) :
    ((torSecond R n).obj A).map g ≫ (torBalanceObjIso R A B' n).hom =
      (torBalanceObjIso R A B n).hom ≫ ((torFirst R n).obj A).map g :=
  ((torBalanceIso R n).app A).hom.naturality g

/-- Tor balance coordinate is natural in the right module.

For `f : A ⟶ A'`, the second-variable Tor map followed by the balance coordinate at `(A', B)`
equals the coordinate at `(A, B)` followed by the first-variable Tor map. -/
theorem torBalance_hom_naturality_right
    {A A' : ModuleCat.{v} Rᵐᵒᵖ} (f : A ⟶ A') (B : ModuleCat.{v} R) (n : ℕ) :
    ((torSecond R n).map f).app B ≫ (torBalanceObjIso R A' B n).hom =
      (torBalanceObjIso R A B n).hom ≫ ((torFirst R n).map f).app B :=
  congrArg (fun t : (torSecond R n).obj A ⟶ (torFirst R n).obj A' => t.app B)
    ((torBalanceIso R n).hom.naturality f)

end ModuleCat.BalancedTensor
