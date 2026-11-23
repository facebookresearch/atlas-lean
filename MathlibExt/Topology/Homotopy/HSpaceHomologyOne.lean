/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.TopCat.HurewiczOne
public import MathlibExt.Topology.Homotopy.HSpaceFundamentalGroup
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import MathlibExt.GroupTheory.Abelianization.MapBijective

/-!
# The original H₁ comparison determines the original π₁ map of H-spaces

The calibrated Hurewicz isomorphisms and their actual naturality square are
reused. H-space commutativity is transported to arbitrary original points.
The comparison is any continuous map; multiplication preservation is not
assumed. No acyclicity or desired fundamental-group isomorphism is a premise.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

universe u

public section

namespace TopCat.HSpaceHomologyOne

/-- The exact original integral H₁ map makes its actual abelianization map bijective. -/
theorem abelianizationMap_bijective_of_integralHomologyOne_isIso
    {X Y : TopCat.{u}} [PathConnectedSpace X] [PathConnectedSpace Y]
    (f : X ⟶ Y) (x : X)
    (hf : IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor 1).map f)) :
    Function.Bijective
      (Abelianization.map (FundamentalGroup.mapOfEq f.hom (rfl : f.hom x = f x))) := by
  let U := ((singularHomologyFunctor AddCommGrpCat.{u} 1).obj
    (singularIntegralCoefficients : AddCommGrpCat.{u}))
  let eX := TopCat.fundamentalGroupAbelianizationHomologyOneIso X x
  let eY := TopCat.fundamentalGroupAbelianizationHomologyOneIso Y (f x)
  let g := FundamentalGroup.mapOfEq f.hom (rfl : f.hom x = f x)
  let m := AddCommGrpCat.ofHom ((Abelianization.map g).toAdditive)
  let : IsIso (U.map f) := hf
  have hNat : m ≫ eY.hom = eX.hom ≫ U.map f :=
    TopCat.fundamentalGroupAbelianizationHomologyOneIso_hom_naturality f x
  have hComp : IsIso (m ≫ eY.hom) :=
    hNat.symm ▸ (inferInstance : IsIso (eX.hom ≫ U.map f))
  let : IsIso m := (isIso_comp_right_iff m eY.hom).mp hComp
  have hm : Function.Bijective m := ConcreteCategory.bijective_of_isIso m
  constructor
  · intro a b h
    have h' : m (Additive.ofMul a) = m (Additive.ofMul b) := congrArg Additive.ofMul h
    exact congrArg Additive.toMul (hm.1 h')
  · intro b
    obtain ⟨a, ha⟩ := hm.2 (Additive.ofMul b)
    exact ⟨Additive.toMul a, congrArg Additive.toMul ha⟩

/-- Arbitrary maps between path-connected H-spaces get their original π₁ bijection from integral
H₁. -/
theorem fundamentalGroupMap_bijective_of_integralHomologyOne_isIso
    {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
    [PathConnectedSpace X] [PathConnectedSpace Y]
    (f : X ⟶ Y)
    (hf : IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor 1).map f))
    (x : X) :
    Function.Bijective (FundamentalGroup.mapOfEq f.hom (rfl : f.hom x = f x)) := by
  let : IsMulCommutative (FundamentalGroup X x) :=
    IsMulCommutative.of_comm (HSpace.fundamentalGroup_mul_comm_at_point (X := X) x)
  let : IsMulCommutative (FundamentalGroup Y (f x)) :=
    IsMulCommutative.of_comm (HSpace.fundamentalGroup_mul_comm_at_point (X := Y) (f x))
  exact MonoidHom.bijective_of_abelianization_map
    (FundamentalGroup.mapOfEq f.hom (rfl : f.hom x = f x))
    (abelianizationMap_bijective_of_integralHomologyOne_isIso f x hf)

end TopCat.HSpaceHomologyOne
