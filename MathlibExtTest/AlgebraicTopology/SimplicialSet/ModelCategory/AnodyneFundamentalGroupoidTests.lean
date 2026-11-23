/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.AnodyneFundamentalGroupoid
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.GroupTheory.Perm.Basic
import MathlibExt.AlgebraicTopology.SimplicialSet.GroupoidNerveKan
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetAnodyneLifting

/-!
# Tests for fundamental groupoids of anodyne extensions

The public theorem is exercised at symbolic and concrete universes, on
isomorphisms, a genuine horn inclusion, composites, and the empty simplicial
set.  Private test clients separately reconstruct the strict retraction and
check the opposite triangle as a natural isomorphism.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Nerve Opposite Simplicial
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory
namespace AnodyneFundamentalGroupoidTests

section SymbolicUniverse

variable {X Y : SSet.{u}} {i : X ⟶ Y}
  (hi : SSet.anodyneExtensions i)

example : (SSet.mapFundamentalGroupoid i).IsEquivalence :=
  hi.isEquivalence_mapFundamentalGroupoid

example : (SSet.mapFundamentalGroupoid i).FullyFaithful := by
  let _ : (SSet.mapFundamentalGroupoid i).IsEquivalence :=
    hi.isEquivalence_mapFundamentalGroupoid
  exact Functor.FullyFaithful.ofFullyFaithful _

end SymbolicUniverse

section ExplicitUniverses

example {X Y : SSet.{1}} {i : X ⟶ Y}
    (hi : SSet.anodyneExtensions i) :
    (SSet.mapFundamentalGroupoid i).IsEquivalence :=
  hi.isEquivalence_mapFundamentalGroupoid

example {X Y : SSet.{0}} {i : X ⟶ Y}
    (hi : SSet.anodyneExtensions i) :
    (SSet.mapFundamentalGroupoid i).IsEquivalence :=
  hi.isEquivalence_mapFundamentalGroupoid

end ExplicitUniverses

section Isomorphisms

example (X : SSet.{u}) :
    (SSet.mapFundamentalGroupoid (𝟙 X)).IsEquivalence :=
  SSet.anodyneExtensions.isEquivalence_mapFundamentalGroupoid
    (SSet.anodyneExtensions.of_isIso (𝟙 X))

example {X Y : SSet.{u}} (e : X ≅ Y) :
    (SSet.mapFundamentalGroupoid e.hom).IsEquivalence :=
  SSet.anodyneExtensions.isEquivalence_mapFundamentalGroupoid
    (SSet.anodyneExtensions.of_isIso e.hom)

end Isomorphisms

section HornAndComposition

example :
    (SSet.mapFundamentalGroupoid
      (SSet.horn (n := 1) (0 : Fin 2)).ι).IsEquivalence :=
  SSet.anodyneExtensions.isEquivalence_mapFundamentalGroupoid
    (SSet.anodyneExtensions.horn_ι (0 : Fin 2))

example {X Y Z : SSet.{u}} {i : X ⟶ Y} {j : Y ⟶ Z}
    (hi : SSet.anodyneExtensions i) (hj : SSet.anodyneExtensions j) :
    (SSet.mapFundamentalGroupoid (i ≫ j)).IsEquivalence :=
  SSet.anodyneExtensions.isEquivalence_mapFundamentalGroupoid
    (SSet.anodyneExtensions.comp_mem i j hi hj)

example :
    (SSet.mapFundamentalGroupoid
      ((SSet.horn (n := 1) (0 : Fin 2)).ι ≫
        𝟙 (Δ[1] : SSet.{u}))).IsEquivalence :=
  SSet.anodyneExtensions.isEquivalence_mapFundamentalGroupoid
    (SSet.anodyneExtensions.comp_mem _ _
      (SSet.anodyneExtensions.horn_ι (0 : Fin 2))
      (SSet.anodyneExtensions.of_isIso (𝟙 (Δ[1] : SSet.{u}))))

end HornAndComposition

section EmptyBoundary

private abbrev emptySSet : SSet.{u} :=
  (⊥ : (Δ[0] : SSet.{u}).Subcomplex)

example :
    (SSet.mapFundamentalGroupoid (𝟙 emptySSet)).IsEquivalence :=
  SSet.anodyneExtensions.isEquivalence_mapFundamentalGroupoid
    (SSet.anodyneExtensions.of_isIso (𝟙 emptySSet))

end EmptyBoundary

private noncomputable def unitMap (X : SSet.{u}) :
    X ⟶ CategoryTheory.nerve (SSet.FundamentalGroupoid X) :=
  SSet.fundamentalGroupoidNerveEquiv X
    (SSet.FundamentalGroupoid X) (𝟭 _)

private theorem strictFirstTriangleClient
    {X Y : SSet.{u}} {i : X ⟶ Y}
    (hi : SSet.anodyneExtensions i) :
    ∃ R : SSet.FundamentalGroupoid Y ⥤ SSet.FundamentalGroupoid X,
      SSet.mapFundamentalGroupoid i ⋙ R = 𝟭 _ := by
  let _ : SSet.KanComplex
      (CategoryTheory.nerve (SSet.FundamentalGroupoid X)) :=
    SSet.kanComplex_nerve_of_groupoid (SSet.FundamentalGroupoid X)
  obtain ⟨rbar, hrbar⟩ :=
    SSet.anodyneExtensions.exists_lift_of_isFibrant (unitMap X) hi
  let R : SSet.FundamentalGroupoid Y ⥤ SSet.FundamentalGroupoid X :=
    (SSet.fundamentalGroupoidNerveEquiv Y
      (SSet.FundamentalGroupoid X)).symm rbar
  refine ⟨R, ?_⟩
  apply (SSet.fundamentalGroupoidNerveEquiv X
    (SSet.FundamentalGroupoid X)).injective
  rw [SSet.fundamentalGroupoidNerveEquiv_precomp]
  change i ≫ SSet.fundamentalGroupoidNerveEquiv Y
      (SSet.FundamentalGroupoid X) R = unitMap X
  rw [show SSet.fundamentalGroupoidNerveEquiv Y
      (SSet.FundamentalGroupoid X) R = rbar by
    exact (SSet.fundamentalGroupoidNerveEquiv Y
      (SSet.FundamentalGroupoid X)).apply_symm_apply rbar]
  exact hrbar

private theorem naturalIsoSecondTriangleClient
    {X Y : SSet.{u}} {i : X ⟶ Y}
    (hi : SSet.anodyneExtensions i) :
    ∃ R : SSet.FundamentalGroupoid Y ⥤ SSet.FundamentalGroupoid X,
      Nonempty (R ⋙ SSet.mapFundamentalGroupoid i ≅ 𝟭 _) := by
  let _ : (SSet.mapFundamentalGroupoid i).IsEquivalence :=
    hi.isEquivalence_mapFundamentalGroupoid
  exact ⟨(SSet.mapFundamentalGroupoid i).inv,
    ⟨(SSet.mapFundamentalGroupoid i).asEquivalence.counitIso⟩⟩

section TriangleClients

variable {X Y : SSet.{u}} {i : X ⟶ Y}
  (hi : SSet.anodyneExtensions i)

example :
    ∃ R : SSet.FundamentalGroupoid Y ⥤ SSet.FundamentalGroupoid X,
      SSet.mapFundamentalGroupoid i ⋙ R = 𝟭 _ :=
  strictFirstTriangleClient hi

example :
    ∃ R : SSet.FundamentalGroupoid Y ⥤ SSet.FundamentalGroupoid X,
      Nonempty (R ⋙ SSet.mapFundamentalGroupoid i ≅ 𝟭 _) :=
  naturalIsoSecondTriangleClient hi

end TriangleClients

section NonThinGroupoid

private def swap₂ : Equiv.Perm (Fin 2) := Equiv.swap 0 1

private def swapEnd :
    End (SingleObj.star (Equiv.Perm (Fin 2))) :=
  SingleObj.toEnd (Equiv.Perm (Fin 2)) swap₂

example : swap₂ ≠ 1 := by decide

set_option backward.isDefEq.respectTransparency false in
example :
    (SSet.mapFundamentalGroupoid
      (𝟙 (CategoryTheory.nerve
        (SingleObj (Equiv.Perm (Fin 2)))))).map
        (SSet.FundamentalGroupoid.homMk
          (CategoryTheory.nerve.edgeMk swapEnd.asHom)) =
      SSet.FundamentalGroupoid.homMk
        (CategoryTheory.nerve.edgeMk swapEnd.asHom) := by
  let _ : (SSet.mapFundamentalGroupoid
      (𝟙 (CategoryTheory.nerve
        (SingleObj (Equiv.Perm (Fin 2)))))).IsEquivalence :=
    SSet.anodyneExtensions.isEquivalence_mapFundamentalGroupoid
      (SSet.anodyneExtensions.of_isIso
        (𝟙 (CategoryTheory.nerve
          (SingleObj (Equiv.Perm (Fin 2))))))
  rw [SSet.mapFundamentalGroupoid_map_homMk]
  congr 1

end NonThinGroupoid

section PrivateBoundary

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.fundamentalGroupoidNerveUnit

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.fundamentalGroupoidNerveCounit

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.fundamentalGroupoidNerveHomotopyIso

end PrivateBoundary

section NoGlobalInstance

example {X Y : SSet.{u}} (_i : X ⟶ Y) : True := by
  fail_if_success
    let _ := inferInstanceAs ((SSet.mapFundamentalGroupoid _i).IsEquivalence)
  trivial

end NoGlobalInstance

#print axioms SSet.anodyneExtensions.isEquivalence_mapFundamentalGroupoid

end AnodyneFundamentalGroupoidTests
end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory

end
