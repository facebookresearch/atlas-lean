/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.SInverseSCoreTranslationAction

/-! # Tests for the skeleton action on core homology -/

@[expose] public section

#check CategoryTheory.SInverseS.coreLeftTranslationIsoOfIso
#check CategoryTheory.SInverseS.coreLeftTranslationZeroIso
#check CategoryTheory.SInverseS.coreLeftTranslationBiprodIso
#check CategoryTheory.SInverseS.coreLeftTranslationSkeletonZeroIso
#check CategoryTheory.SInverseS.coreLeftTranslationSkeletonAddIso
#check CategoryTheory.SInverseS.coreTranslationHomologyMap
#check CategoryTheory.SInverseS.coreTranslationHomologyMap_toSkeleton
#check CategoryTheory.SInverseS.coreTranslationHomologyMap_zero
#check CategoryTheory.SInverseS.coreTranslationHomologyMap_add
#check CategoryTheory.SInverseS.coreTranslationHomologyRepresentation
#check CategoryTheory.SInverseS.coreTranslationHomologyModule
#check CategoryTheory.SInverseS.coreTranslationHomologyModuleEquiv
#check CategoryTheory.SInverseS.coreTranslationHomologyModuleEquiv_monomial_smul

#print axioms CategoryTheory.SInverseS.coreLeftTranslationSkeletonAddIso
#print axioms CategoryTheory.SInverseS.coreTranslationHomologyMap_zero
#print axioms CategoryTheory.SInverseS.coreTranslationHomologyMap_add
#print axioms CategoryTheory.SInverseS.coreTranslationHomologyRepresentation
#print axioms
  CategoryTheory.SInverseS.coreTranslationHomologyModuleEquiv_monomial_smul

end
