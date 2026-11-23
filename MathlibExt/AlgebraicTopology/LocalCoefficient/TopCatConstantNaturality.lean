/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatBaseHomology
public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.TopCatConstant

/-!
# Naturality of the TopCat constant local-coefficient comparison

Pullback of a selected constant local system is canonically isomorphic to the
selected constant system on the source.  The landed cast-aware generator
formula for the SSet pullback chain map proves that the TopCat constant-chain
comparison is natural under one map of spaces.  Applying homology gives the
corresponding constant local-coefficient homology square.

This file makes no converse, acyclicity, plus-recognition, or
plus-construction claim.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.CategoryHomology
open scoped Simplicial

universe uR uX

namespace TopCat
namespace LocalSystem

/-- Pullback of a literal constant topological local system is canonically
isomorphic to the literal constant system on the source. -/
noncomputable def constantPullbackIso
    {R : Type uR} [CommRing R]
    {X Y : TopCat.{uX}} (f : X ⟶ Y)
    (M : ModuleCat.{max uR uX} R) :
    (TopCat.constantLocalSystem (X := Y) M).pullback f ≅
      TopCat.constantLocalSystem (X := X) M :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro x y g
    change 𝟙 M ≫ 𝟙 M = 𝟙 M ≫ 𝟙 M
    simp)

@[simp]
theorem constantPullbackIso_hom_app
    {R : Type uR} [CommRing R]
    {X Y : TopCat.{uX}} (f : X ⟶ Y)
    (M : ModuleCat.{max uR uX} R)
    (x : _root_.FundamentalGroupoid X) :
    (constantPullbackIso f M).hom.app x = 𝟙 M :=
  rfl

@[simp]
theorem constantPullbackIso_inv_app
    {R : Type uR} [CommRing R]
    {X Y : TopCat.{uX}} (f : X ⟶ Y)
    (M : ModuleCat.{max uR uX} R)
    (x : _root_.FundamentalGroupoid X) :
    (constantPullbackIso f M).inv.app x = 𝟙 M :=
  rfl

/-- For a constant coefficient system, the inverse singular-pullback
comparison is the identity on every coefficient object. -/
@[simp]
theorem singularPullbackIso_constant_inv_app
    {R : Type uR} [CommRing R]
    {X Y : TopCat.{uX}} (f : X ⟶ Y)
    (M : ModuleCat.{max uR uX} R)
    (x : SSet.FundamentalGroupoid (TopCat.toSSet.obj X)) :
    (TopCat.LocalSystem.singularPullbackIso f
      (TopCat.constantLocalSystem (X := Y) M)).inv.app x = 𝟙 M :=
  rfl

end LocalSystem

namespace ConstantNaturality

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The local-coefficient pullback chain map commutes with the canonical
constant-chain comparison.  The source constant-system comparison is
explicit because constant pullback is not treated as strictly equal. -/
theorem chainMap
    {R : Type uR} [CommRing R]
    {X Y : TopCat.{uX}} (f : X ⟶ Y)
    (M : ModuleCat.{max uR uX} R) :
    TopCat.localCoefficientPullbackChainMap f
          (TopCat.constantLocalSystem (X := Y) M) ≫
        (TopCat.constantLocalCoefficientChainIso (X := Y) M).hom =
      SSet.localCoefficientChainMap
            (TopCat.LocalSystem.toSingularMap
              (TopCat.LocalSystem.constantPullbackIso f M).hom) ≫
        (TopCat.constantLocalCoefficientChainIso (X := X) M).hom ≫
        ((AlgebraicTopology.singularChainComplexFunctor
          (ModuleCat.{max uR uX} R)).obj M).map f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply nervePullbackCoefficient_hom_ext
    (SSet.fundamentalGroupoidNerveUnit (TopCat.toSSet.obj X))
    ((TopCat.constantLocalSystem (X := Y) M).pullback f).toSingular
  intro sigma
  change SSet.localCoefficientι
      ((TopCat.constantLocalSystem (X := Y) M).pullback f).toSingular sigma ≫ _ =
    SSet.localCoefficientι
      ((TopCat.constantLocalSystem (X := Y) M).pullback f).toSingular sigma ≫ _
  simp only [HomologicalComplex.comp_f]
  rw [TopCat.localCoefficientPullbackChainMap_f]
  simp only [Category.assoc]
  have hMap := SSet.localCoefficientι_map
    (X := TopCat.toSSet.obj X)
    (α := (TopCat.LocalSystem.singularPullbackIso f
      (TopCat.constantLocalSystem (X := Y) M)).inv)
    (n := n) sigma
  slice_lhs 1 2 => exact hMap
  rw [TopCat.LocalSystem.singularPullbackIso_constant_inv_app]
  slice_lhs 1 2 => exact Category.id_comp _
  have hPull := SSet.localCoefficientι_pullbackChainMap
    (f := TopCat.toSSet.map f)
    (L := (TopCat.constantLocalSystem (X := Y) M).toSingular)
    (n := n) sigma
  slice_lhs 1 2 => exact hPull
  have hConstCast : SSet.localCoefficientPullbackFamilyEq
      (TopCat.toSSet.map f)
      (TopCat.constantLocalSystem (X := Y) M).toSingular sigma = rfl :=
    Subsingleton.elim _ _
  rw [hConstCast, eqToHom_refl, Category.id_comp]
  have hConstY := TopCat.constantLocalCoefficientι_comp_chainIso_hom
    (X := Y) M ((TopCat.toSSet.map f).app _ sigma)
  slice_lhs 1 2 => exact hConstY
  rw [SSet.localCoefficientChainMap_f]
  have hBeta := SSet.localCoefficientι_map
    (X := TopCat.toSSet.obj X)
    (α := TopCat.LocalSystem.toSingularMap
      (TopCat.LocalSystem.constantPullbackIso f M).hom)
    (n := n) sigma
  slice_rhs 1 2 => exact hBeta
  rw [TopCat.LocalSystem.toSingularMap_app,
    TopCat.LocalSystem.constantPullbackIso_hom_app]
  slice_rhs 1 2 => exact Category.id_comp _
  have hConstX := TopCat.constantLocalCoefficientι_comp_chainIso_hom
    (X := X) M sigma
  slice_rhs 1 2 => exact hConstX
  have hOrd := SSet.ι_chainComplexMap_f
    (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)
    (TopCat.toSSet.map f) M sigma
  exact hOrd.symm

/-- Homology-level naturality of the constant local-coefficient comparison. -/
theorem homologyMap
    {R : Type uR} [CommRing R]
    {X Y : TopCat.{uX}} (f : X ⟶ Y)
    (M : ModuleCat.{max uR uX} R) (n : ℕ) :
    TopCat.localCoefficientPullbackHomologyMap f
          (TopCat.constantLocalSystem (X := Y) M) n ≫
        (TopCat.constantLocalCoefficientHomologyIso (X := Y) M n).hom =
      TopCat.localCoefficientHomologyMap
            (TopCat.LocalSystem.constantPullbackIso f M).hom n ≫
        (TopCat.constantLocalCoefficientHomologyIso (X := X) M n).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor
          (ModuleCat.{max uR uX} R) n).obj M).map f := by
  change HomologicalComplex.homologyMap
        (TopCat.localCoefficientPullbackChainMap f
          (TopCat.constantLocalSystem (X := Y) M)) n ≫
      HomologicalComplex.homologyMap
        (TopCat.constantLocalCoefficientChainIso (X := Y) M).hom n =
    HomologicalComplex.homologyMap
        (SSet.localCoefficientChainMap
          (TopCat.LocalSystem.toSingularMap
            (TopCat.LocalSystem.constantPullbackIso f M).hom)) n ≫
      HomologicalComplex.homologyMap
          (TopCat.constantLocalCoefficientChainIso (X := X) M).hom n ≫
        HomologicalComplex.homologyMap
          (((AlgebraicTopology.singularChainComplexFunctor
            (ModuleCat.{max uR uX} R)).obj M).map f) n
  rw [← HomologicalComplex.homologyMap_comp]
  rw [← HomologicalComplex.homologyMap_comp]
  rw [← HomologicalComplex.homologyMap_comp]
  exact congrArg (fun k => HomologicalComplex.homologyMap k n)
    (chainMap f M)

end ConstantNaturality
end TopCat
