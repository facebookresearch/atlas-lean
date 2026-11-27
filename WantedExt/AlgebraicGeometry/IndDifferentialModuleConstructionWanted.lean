/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.IndDifferentialModuleModels

/-!
# Construction requests for fully normalized native beta-ring modules

These requests construct the prescribed ordinary representation and
monoidal mapping with both original actions. They do not select an
enhanced realization or a final comparison. Source: DK1311.2374v2 Section4.10.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.IndDifferentialModuleConstructionWanted

open _root_.CategoryTheory TopologicalSpace
open MathlibExt.AlgebraicGeometry
open CompactSupportIndSheaves IndSheafCoefficientModels IndSheafAlphaBetaModels
open IndSheafMonoidalModels RingedComplexCoefficientModels BetaDifferentialRingModels
open IndDifferentialModuleModels
open MathlibExt.CategoryTheory.NativeMonoidalBimoduleMapping

variable (X : TopCat.{0})
  [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)]
  [CompactSheafSource ℂ X]
  (T : CompactTensorSource ℂ X) (I : IndTensorSource ℂ X T)
  (A : AlphaSource ℂ X) (B : BetaSource ℂ X A)
  [OrdinaryMonoidalSource ℂ X] [IndMonoidalSource ℂ X T I]
  [BetaMonoidalSource ℂ X T I A B]
  (R : TopCat.Sheaf RingCat.{0} X) [ComplexRingSheafSource X R]
  (S : RingCoefficientSheafSource X R) (M : OrdinaryRingMonoidSource X R S)
  (F : ComplexModuleForgetSource X R)

def_wanted actual_ordinary_module_representation : OrdinaryModuleRepresentationSource X R S M F

def_wanted actual_beta_module_mapping : BimoduleMappingSource (beta ℂ X A B)
  (ordinaryRing X R S M) (Mon.trivial (OrdinarySheaf ℂ X))

end WantedExt.AlgebraicGeometry.IndDifferentialModuleConstructionWanted
