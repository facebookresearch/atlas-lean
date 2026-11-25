/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import MathlibExt.AlgebraicGeometry.CompactSupportIndSheaves
public import Mathlib.Basic.Complex.Basic

/-!
# Original complex scalar structure and module forgetful normalization

The coefficient algebra is the original ring sheaf, and restrictions
preserve its complex constants. The ordinary forgetful source retains
every original module section, restriction and morphism. Analytic Ind
modules use separate native beta-ring actions on Ind coefficient sheaves.

Source: DK arXiv:1311.2374v2, Sections 4.10 and 5.2.
Native ring/module/Ind APIs: Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679,
Apache 2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RingedComplexCoefficientModels

open _root_.CategoryTheory _root_.Opposite TopologicalSpace
open CompactSupportIndSheaves

variable (X : TopCat.{0}) (R : TopCat.Sheaf RingCat.{0} X)

abbrev OrdinaryModule := SheafOfModules.{0} R

/-- A `ℂ`-algebra structure on every section ring of the ring sheaf, natural under
restriction. For a sheaf of holomorphic functions or differential operators this is meant to be
the constant functions; the class records the structure as a hypothesis and does not identify
it with those constants for an arbitrary ring sheaf. -/
class ComplexRingSheafSource where
  [algebra : ∀ U : Opens X, Algebra ℂ (R.obj.obj (op U))]
  natural : ∀ {U V : Opens X} (h : V ≤ U) (c : ℂ),
    (R.obj.map (homOfLE h).op).hom (algebraMap ℂ (R.obj.obj (op U)) c) =
      algebraMap ℂ (R.obj.obj (op V)) c

attribute [instance_reducible, instance] ComplexRingSheafSource.algebra

variable [ComplexRingSheafSource X R]

/-- Restrict the actual native ring-module scalar action through its original complex constants. -/
local instance moduleComplexScalars (N : OrdinaryModule X R) (U : Opens X) :
    Module ℂ (N.val.obj (op U)) :=
  Module.compHom (N.val.obj (op U)) (algebraMap ℂ (R.obj.obj (op U)))

/-- A construction of the original underlying complex sheaf, with all maps fixed. -/
structure ComplexModuleForgetSource where
  functor : OrdinaryModule X R ⥤ OrdinarySheaf ℂ X
  sections : ∀ (N : OrdinaryModule X R) (U : Opens X),
    (functor.obj N).presheaf.obj (op U) ≃ₗ[ℂ] N.val.obj (op U)
  restriction : ∀ (N : OrdinaryModule X R) (U V : Opens X) (h : V ≤ U)
    (s : (functor.obj N).presheaf.obj (op U)),
    sections N V ((functor.obj N).presheaf.map (homOfLE h).op s) =
      (N.val.map (homOfLE h).op).hom (sections N U s)
  morphism : ∀ (N N' : OrdinaryModule X R) (f : N ⟶ N') (U : Opens X)
    (s : (functor.obj N).presheaf.obj (op U)),
    sections N' U ((functor.map f).hom.app (op U) s) =
      (f.val.app (op U)).hom (sections N U s)

end MathlibExt.AlgebraicGeometry.RingedComplexCoefficientModels
