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

public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensorRight
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.ResolutionComparison
public import MathlibExt.CategoryTheory.Abelian.RightDerived.ResolutionComparison
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Right-module-valued Tor and Ext of a bimodule

Let `B` be an `R`-left, `S`-right bimodule with commuting actions. If the right `R`-module
category has projective resolutions, left deriving `A ↦ A ⊗_R B` gives right `S`-module-valued
Tor. If the right `S`-module category has injective resolutions, right deriving `C ↦
Hom_(Sᵐᵒᵖ)(B, C)` gives right `R`-module-valued Ext.

Forgetting the outer action commutes with these derivations because the forgetful module
functor is exact. Degree-zero Tor is naturally the tensor functor, and degree-zero Ext is
naturally the Hom functor. The ring universes are independent, while the underived categorical
adjunction and its derived functors use carrier universe `v`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe r s v

namespace ModuleCat.BalancedTensorRight

private theorem forgetting_preservesHomology (T : Type r) [Ring T] :
    (forget₂ (ModuleCat.{v} T) AddCommGrpCat.{v}).PreservesHomology := by
  let U : ModuleCat.{v} T ⥤ AddCommGrpCat.{v} := forget₂ _ _
  let : PreservesLimits U :=
    ModuleCat.forget₂AddCommGroup_preservesLimits (R := T)
  let : PreservesFiniteLimits U :=
    CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits U
  let : PreservesFiniteColimits U := ⟨by
    intro J hJ hFin
    exact @ModuleCat.forget₂PreservesColimitsOfShape T _ J hJ
      (inferInstance : HasColimitsOfShape J AddCommGrpCat.{v})⟩
  exact CategoryTheory.Functor.preservesHomologyOfExact U

variable (R : Type r) (S : Type s) [Ring R] [Ring S]
  (B : Type v) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
  [SMulCommClass R Sᵐᵒᵖ B]

section Tor

variable [HasProjectiveResolutions (ModuleCat.{v} Rᵐᵒᵖ)]

/-- Tor as the left-derived right-module tensor functor.

Assuming projective resolutions in `ModuleCat.{v} Rᵐᵒᵖ`, the degree-`n` left-derived functor
of `A ↦ A ⊗_R B` is `ModuleCat Rᵐᵒᵖ ⥤ ModuleCat Sᵐᵒᵖ`, retaining the right `S`-action. -/
def torFunctor (n : ℕ) : ModuleCat.{v} Rᵐᵒᵖ ⥤ ModuleCat.{v} Sᵐᵒᵖ :=
  (tensorFunctor R S B).leftDerived n

/-- Forgetting the right outer action commutes with Tor derivation.

The degree-`n` Tor functor followed by forgetting right `S`-scalars is naturally isomorphic to
the left-derived functor of the corresponding additive-group tensor functor. -/
def torForgetIso (n : ℕ) :
    torFunctor R S B n ⋙ forget₂ (ModuleCat.{v} Sᵐᵒᵖ) AddCommGrpCat.{v} ≅
      (tensorFunctor R S B ⋙
        forget₂ (ModuleCat.{v} Sᵐᵒᵖ) AddCommGrpCat.{v}).leftDerived n := by
  letI : (forget₂ (ModuleCat.{v} Sᵐᵒᵖ) AddCommGrpCat.{v}).PreservesHomology := by
    exact forgetting_preservesHomology (T := Sᵐᵒᵖ)
  exact (tensorFunctor R S B).leftDerivedCompIsoOfPreservesHomology
    (forget₂ (ModuleCat.{v} Sᵐᵒᵖ) AddCommGrpCat.{v}) n

/-- Degree-zero right-module Tor is the tensor functor.

The degree-zero left-derived tensor functor is naturally isomorphic to `tensorFunctor R S B`. -/
def torZeroIso : torFunctor R S B 0 ≅ tensorFunctor R S B :=
  (tensorFunctor R S B).leftDerivedZeroIsoSelf

/-- Degree-zero Tor comparison is the tensor augmentation.

The forward map of `torZeroIso R S B` is the canonical transformation `fromLeftDerivedZero` of
the tensor functor. -/
theorem torZeroIso_hom : (torZeroIso R S B).hom =
    (tensorFunctor R S B).fromLeftDerivedZero := rfl

end Tor

section Ext

variable [HasInjectiveResolutions (ModuleCat.{v} Sᵐᵒᵖ)]

/-- Ext as the right-derived right-module Hom functor.

Assuming injective resolutions in `ModuleCat.{v} Sᵐᵒᵖ`, right derive the coefficient Hom
functor in degree `n`. The result sends a right `S`-module `C` to `Ext^n_(Sᵐᵒᵖ)(B, C)` with
its right `R`-action. -/
def extFunctor (n : ℕ) : ModuleCat.{v} Sᵐᵒᵖ ⥤ ModuleCat.{v} Rᵐᵒᵖ :=
  (homFunctor R S B).rightDerived n

/-- Forgetting the right outer action commutes with Ext derivation.

The degree-`n` Ext functor followed by forgetting right `R`-scalars is naturally isomorphic to
the right-derived functor of the corresponding additive-group Hom functor. -/
def extForgetIso (n : ℕ) :
    extFunctor R S B n ⋙ forget₂ (ModuleCat.{v} Rᵐᵒᵖ) AddCommGrpCat.{v} ≅
      (homFunctor R S B ⋙
        forget₂ (ModuleCat.{v} Rᵐᵒᵖ) AddCommGrpCat.{v}).rightDerived n := by
  letI : (forget₂ (ModuleCat.{v} Rᵐᵒᵖ) AddCommGrpCat.{v}).PreservesHomology := by
    exact forgetting_preservesHomology (T := Rᵐᵒᵖ)
  exact (homFunctor R S B).rightDerivedCompIsoOfPreservesHomology
    (forget₂ (ModuleCat.{v} Rᵐᵒᵖ) AddCommGrpCat.{v}) n

/-- Degree-zero right-module Ext is the Hom functor.

The degree-zero right-derived coefficient Hom functor is naturally isomorphic to `homFunctor R
S B`. -/
def extZeroIso : extFunctor R S B 0 ≅ homFunctor R S B := by
  letI : (homFunctor R S B).IsRightAdjoint :=
    ⟨tensorFunctor R S B, ⟨tensorAdjunction R S B⟩⟩
  exact (homFunctor R S B).rightDerivedZeroIsoSelf

end Ext

end ModuleCat.BalancedTensorRight
