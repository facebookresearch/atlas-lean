/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalKSpaceContinuousMap

/-!
# Tests for continuous exact-functor weak-diagonal K-space maps

These tests pin the weakly pointed map and its exact root path, the continuous
loop map, literal agreement with the landed raw function, pointwise identity
and composition homotopies, and all four supported object/morphism universe
combinations.

Negative checks retain the deliberate absence of strict functoriality,
additivity naturality, loop-map weak equivalences, spectra, and global
homotopical instances.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction

open _root_.CategoryTheory.Waldhausen.SConstruction

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D]
  [Limits.HasZeroObject C] [Limits.HasZeroObject D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  [ExactCategory C] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [Functor.IsExact F]

local instance stageWeakDiagonalKSpaceContinuousMapTestsWaldhausenC :
    WaldhausenCategory C :=
  ExactCategory.waldhausenCategory C

local instance stageWeakDiagonalKSpaceContinuousMapTestsWaldhausenD :
    WaldhausenCategory D :=
  ExactCategory.waldhausenCategory D

example : ContinuousMap.WeaklyPointed
    (stageWeakDiagonalReal.basepoint C)
    (stageWeakDiagonalReal.basepoint D) :=
  stageWeakDiagonalRealMapWeaklyPointed C D F

example : (stageWeakDiagonalRealMapWeaklyPointed C D F).hom =
    (stageWeakDiagonalReal.map C D F).hom :=
  stageWeakDiagonalRealMapWeaklyPointed_hom C D F

example : (stageWeakDiagonalRealMapWeaklyPointed C D F).rootPath =
    stageWeakDiagonalKSpace.zeroComparisonRootPath C D F :=
  stageWeakDiagonalRealMapWeaklyPointed_rootPath C D F

example : C(stageWeakDiagonalKSpace C, stageWeakDiagonalKSpace D) :=
  stageWeakDiagonalKSpaceContinuousMap C D F

example : Continuous (stageWeakDiagonalKSpaceContinuousMap C D F) :=
  (stageWeakDiagonalKSpaceContinuousMap C D F).continuous

example (gamma : stageWeakDiagonalKSpace C) :
    stageWeakDiagonalKSpaceContinuousMap C D F gamma =
      stageWeakDiagonalKSpaceMap C D F gamma :=
  stageWeakDiagonalKSpaceContinuousMap_apply C D F gamma

example (gamma : stageWeakDiagonalKSpace C) :
    (stageWeakDiagonalKSpaceContinuousMap C C (𝟭 C) gamma).Homotopic gamma :=
  stageWeakDiagonalKSpaceContinuousMap_id_homotopic C gamma

section Composition

variable {E : Type u} [Category.{v} E] [Preadditive E]
  [Limits.HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
variable (G : D ⥤ E) [G.Additive] [Functor.IsExact G]

local instance stageWeakDiagonalKSpaceContinuousMapTestsWaldhausenE :
    WaldhausenCategory E :=
  ExactCategory.waldhausenCategory E

example (gamma : stageWeakDiagonalKSpace C) :
    (stageWeakDiagonalKSpaceContinuousMap C E (F ⋙ G) gamma).Homotopic
      (stageWeakDiagonalKSpaceContinuousMap D E G
        (stageWeakDiagonalKSpaceContinuousMap C D F gamma)) :=
  stageWeakDiagonalKSpaceContinuousMap_comp_homotopic C D F E G gamma

end Composition

section Universes

variable {C00 D00 : Type} [Category C00] [Category D00]
  [Preadditive C00] [Preadditive D00]
  [Limits.HasZeroObject C00] [Limits.HasZeroObject D00]
  [HasBinaryBiproducts C00] [HasBinaryBiproducts D00]
  [ExactCategory C00] [ExactCategory D00]
variable {C11 D11 : Type 1} [Category.{1} C11] [Category.{1} D11]
  [Preadditive C11] [Preadditive D11]
  [Limits.HasZeroObject C11] [Limits.HasZeroObject D11]
  [HasBinaryBiproducts C11] [HasBinaryBiproducts D11]
  [ExactCategory C11] [ExactCategory D11]
variable {C01 D01 : Type} [Category.{1} C01] [Category.{1} D01]
  [Preadditive C01] [Preadditive D01]
  [Limits.HasZeroObject C01] [Limits.HasZeroObject D01]
  [HasBinaryBiproducts C01] [HasBinaryBiproducts D01]
  [ExactCategory C01] [ExactCategory D01]
variable {C10 D10 : Type 1} [Category.{0} C10] [Category.{0} D10]
  [Preadditive C10] [Preadditive D10]
  [Limits.HasZeroObject C10] [Limits.HasZeroObject D10]
  [HasBinaryBiproducts C10] [HasBinaryBiproducts D10]
  [ExactCategory C10] [ExactCategory D10]

example (H : C00 ⥤ D00) [H.Additive] [Functor.IsExact H] :
    (letI : WaldhausenCategory C00 := ExactCategory.waldhausenCategory C00;
      letI : WaldhausenCategory D00 := ExactCategory.waldhausenCategory D00;
      C(stageWeakDiagonalKSpace C00, stageWeakDiagonalKSpace D00)) :=
  stageWeakDiagonalKSpaceContinuousMap C00 D00 H

example (H : C11 ⥤ D11) [H.Additive] [Functor.IsExact H] :
    (letI : WaldhausenCategory C11 := ExactCategory.waldhausenCategory C11;
      letI : WaldhausenCategory D11 := ExactCategory.waldhausenCategory D11;
      C(stageWeakDiagonalKSpace C11, stageWeakDiagonalKSpace D11)) :=
  stageWeakDiagonalKSpaceContinuousMap C11 D11 H

example (H : C01 ⥤ D01) [H.Additive] [Functor.IsExact H] :
    (letI : WaldhausenCategory C01 := ExactCategory.waldhausenCategory C01;
      letI : WaldhausenCategory D01 := ExactCategory.waldhausenCategory D01;
      C(stageWeakDiagonalKSpace C01, stageWeakDiagonalKSpace D01)) :=
  stageWeakDiagonalKSpaceContinuousMap C01 D01 H

example (H : C10 ⥤ D10) [H.Additive] [Functor.IsExact H] :
    (letI : WaldhausenCategory C10 := ExactCategory.waldhausenCategory C10;
      letI : WaldhausenCategory D10 := ExactCategory.waldhausenCategory D10;
      C(stageWeakDiagonalKSpace C10, stageWeakDiagonalKSpace D10)) :=
  stageWeakDiagonalKSpaceContinuousMap C10 D10 H

end Universes

section Nonclaims

#guard_msgs (error, substring := true) in
#check stageWeakDiagonalKSpaceContinuousMap_mem_weakHomotopyEquivalences

#guard_msgs (error, substring := true) in
#check stageWeakDiagonalKSpaceContinuousMap_naturality

#guard_msgs (error, substring := true) in
#check stageWeakDiagonalKSpaceFunctor

#guard_msgs (error, substring := true) in
#check extensionAdditivityKSpaceContinuousMap_naturality

#guard_msgs (error, substring := true) in
#check stageWeakDiagonalKSpaceSpectrumMap

example : True := by
  fail_if_success
    let _ : CategoryWithWeakEquivalences TopCat.{max u v} := inferInstance
  trivial

end Nonclaims

#print axioms stageWeakDiagonalRealMapWeaklyPointed
#print axioms stageWeakDiagonalRealMapWeaklyPointed_hom
#print axioms stageWeakDiagonalRealMapWeaklyPointed_rootPath
#print axioms stageWeakDiagonalKSpaceContinuousMap
#print axioms stageWeakDiagonalKSpaceContinuousMap_apply
#print axioms stageWeakDiagonalKSpaceContinuousMap_id_homotopic
#print axioms stageWeakDiagonalKSpaceContinuousMap_comp_homotopic

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction

end
