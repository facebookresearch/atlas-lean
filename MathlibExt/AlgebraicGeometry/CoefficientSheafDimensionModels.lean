/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CompactSupportIndSheaves
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Native flabby resolutions and coefficient cohomological dimension

The vanishing condition is the actual derived Hom from the native
constant coefficient sheaf to every original sheaf in degree n.
It is imposed on every original open subspace with one finite bound.
The source's finite flabby dimension is separately defined by actual
bounded flabby cochain resolutions and their native quasi-isomorphism
augmentations. These two conditions are not identified here.

Source: D'Agnolo--Kashiwara1311.2374v2, Section2 conventions (good spaces),
and ordinary sheaf cohomology as derived Hom from the constant unit.
Native constant sheaves, single functors and derived categories are
Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CoefficientSheafDimensionModels

open _root_.CategoryTheory TopologicalSpace
open CompactSupportIndSheaves

attribute [local instance] HasDerivedCategory.standard

variable (k : Type) [Field k] (M : TopCat.{0})

local instance dimensionAbelianPreadditive (X : TopCat.{0}) : Preadditive (OrdinarySheaf k X) :=
  Abelian.toPreadditive

/-- The original constant coefficient sheaf, on each actual open subspace. -/
def openConstant (U : Opens M) : OrdinarySheaf k (TopCat.of U) :=
  (constantSheaf (Opens.grothendieckTopology (TopCat.of U)) (ModuleCat.{0} k)).obj
    (ModuleCat.of k k)

/-- Literal higher-cohomology vanishing through the original derived unit Hom. -/
def SheafCohomologicalDimensionLE (d : ℕ) : Prop :=
  ∀ (U : Opens M) (F : OrdinarySheaf k (TopCat.of U)) (n : ℤ), (d : ℤ) < n →
    Subsingleton
      (((DerivedCategory.singleFunctor (OrdinarySheaf k (TopCat.of U)) 0).obj (openConstant k M U)) ⟶
        ((DerivedCategory.singleFunctor (OrdinarySheaf k (TopCat.of U)) 0).obj F)⟦n⟧)

/-- Finite dimension refers to one common bound for these actual coefficient cohomology groups. -/
def FiniteSheafCohomologicalDimension : Prop := ∃ d : ℕ, SheafCohomologicalDimensionLE k M d

/-- A native coefficient sheaf is flabby when every original restriction of sections is surjective. -/
def IsFlabby (F : OrdinarySheaf k M) : Prop :=
  ∀ (U V : Opens M) (h : V ≤ U), Function.Surjective ((F.presheaf.map (homOfLE h).op).hom)

/-- An actual bounded flabby resolution, with its original cochain augmentation and quasi-isomorphism. -/
def FlabbyDimensionLE (d : ℕ) : Prop :=
  ∀ F : OrdinarySheaf k M,
    ∃ (K : CochainComplex (OrdinarySheaf k M) ℤ)
      (a : (HomologicalComplex.single (OrdinarySheaf k M) (.up ℤ) 0).obj F ⟶ K),
      QuasiIso a ∧
        (∀ n : ℤ, n < 0 ∨ (d : ℤ) < n → _root_.CategoryTheory.Limits.IsZero (K.X n)) ∧
        (∀ n : ℤ, IsFlabby k M (K.X n))

/-- The exact finite flabby-dimension background of the source's good-space convention. -/
def FiniteFlabbyDimension : Prop := ∃ d : ℕ, FlabbyDimensionLE k M d

end MathlibExt.AlgebraicGeometry.CoefficientSheafDimensionModels
