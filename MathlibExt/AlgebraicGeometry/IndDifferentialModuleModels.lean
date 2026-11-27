/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.BetaDifferentialRingModels
public import MathlibExt.CategoryTheory.NativeMonoidalBimoduleMapping
public import MathlibExt.CategoryTheory.NativeDerivedBimoduleOperators
public import MathlibExt.CategoryTheory.NativeOppositeBimoduleModels

/-!
# Native beta-ring modules in the original Ind coefficient category

The coefficient category is Ind of the original compact k-sheaves.
The rings are native beta images of the actual ordinary ring sheaves.
Ordinary modules enter through their full original coefficient sheaf and
every local ring action, followed by the prescribed monoidal beta mapping.
No Ind completion of ordinary A-modules is used for analytic I(beta A).

Source: DK arXiv:1311.2374v2, Section 4.10. Native Bimod, derived
localization and monoidal functor constructors: Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679, Apache 2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.IndDifferentialModuleModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.Opposite TopologicalSpace
open CompactSupportIndSheaves IndSheafCoefficientModels IndSheafAlphaBetaModels
open IndSheafMonoidalModels RingedComplexCoefficientModels BetaDifferentialRingModels
open MathlibExt.CategoryTheory.NativeMonoidalBimoduleMapping

variable (X : TopCat.{0})
  [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)]
  [CompactSheafSource ℂ X]
  (T : CompactTensorSource ℂ X) (I : IndTensorSource ℂ X T)
  (A : AlphaSource ℂ X) (B : BetaSource ℂ X A)
  [OrdinaryMonoidalSource ℂ X] [IndMonoidalSource ℂ X T I]
  [BetaMonoidalSource ℂ X T I A B]

local instance originalIndPreadditive : Preadditive (IndSheaf ℂ X) := Abelian.toPreadditive

/-- The coefficient ring is beta of the original ordinary coefficient unit. -/
abbrev betaCoefficientRing : Mon (IndSheaf ℂ X) :=
  mappedRing (beta ℂ X A B) (Mon.trivial (OrdinarySheaf ℂ X))

variable (R : TopCat.Sheaf RingCat.{0} X) [ComplexRingSheafSource X R]
  (S : RingCoefficientSheafSource X R) (M : OrdinaryRingMonoidSource X R S)

abbrev ordinaryRing : Mon (OrdinarySheaf ℂ X) :=
  letI := M.monoid
  Mon.mk (ringCoefficientSheaf X R S)

/-- The native beta image of this original normalized ring, including its multiplication. -/
abbrev nativeBetaRing : Mon (IndSheaf ℂ X) :=
  mappedRing (beta ℂ X A B) (ordinaryRing X R S M)

variable (F : ComplexModuleForgetSource X R)

/-- Ordinary representation is fixed on every original module section and action. -/
structure OrdinaryModuleRepresentationSource where
  functor : OrdinaryModule X R ⥤
    Bimod (ordinaryRing X R S M) (Mon.trivial (OrdinarySheaf ℂ X))
  underlying : functor ⋙ Bimod.forget (B := Mon.trivial (OrdinarySheaf ℂ X))
    (ordinaryRing X R S M) ≅ F.functor
  leftAction : ∀ (N : OrdinaryModule X R) (U : Opens X) (r : R.obj.obj (op U))
      (s : (functor.obj N).X.presheaf.obj (op U)),
    F.sections N U ((underlying.hom.app N).hom.app (op U)
      ((functor.obj N).actLeft.hom.app (op U)
        (sourceTensorSection ℂ X (ringCoefficientSheaf X R S)
          (functor.obj N).X U r s))) =
      r • F.sections N U ((underlying.hom.app N).hom.app (op U) s)

variable (O : OrdinaryModuleRepresentationSource X R S M F)
  (P : BimoduleMappingSource (beta ℂ X A B)
    (ordinaryRing X R S M) (Mon.trivial (OrdinarySheaf ℂ X)))

/-- Every object/map is the original ordinary module followed by the actual beta mapping. -/
def betaOrdinaryModule : OrdinaryModule X R ⥤
    Bimod (nativeBetaRing X T I A B R S M) (betaCoefficientRing X T I A B) :=
  O.functor ⋙ P.functor

/-- Structural native bimodule-category hypotheses for this original Ind tensor. The abelian
structure of each bimodule category is required to use the inherited hom-groups: a sum of
bimodule maps has the sum of the underlying Ind-sheaf maps. Bimodule maps are determined by
their underlying maps, so this fixes the additive structure; it is not free extra data. -/
class NativeModuleCalculus where
  [coequalizers : HasCoequalizers (IndSheaf ℂ X)]
  [leftColimits : ∀ K : IndSheaf ℂ X,
    PreservesColimitsOfSize.{0, 0} (tensorLeft K)]
  [rightColimits : ∀ K : IndSheaf ℂ X,
    PreservesColimitsOfSize.{0, 0} (tensorRight K)]
  [abelian : ∀ D E : Mon (IndSheaf ℂ X), Abelian (Bimod D E)]
  hom_add : ∀ (D E : Mon (IndSheaf ℂ X)) {P Q : Bimod D E} (f g : P ⟶ Q),
    (f + g).hom = f.hom + g.hom

attribute [instance] NativeModuleCalculus.coequalizers
  NativeModuleCalculus.leftColimits NativeModuleCalculus.rightColimits
attribute [instance_reducible, instance] NativeModuleCalculus.abelian

end MathlibExt.AlgebraicGeometry.IndDifferentialModuleModels
