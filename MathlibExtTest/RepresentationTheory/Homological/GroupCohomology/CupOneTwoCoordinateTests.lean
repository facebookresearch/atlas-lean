/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupProductLowDegree
import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupOneTwoFunctoriality
import Mathlib.Algebra.Group.TypeTags.Basic
meta import Mathlib.Tactic.Ring

/-!
# Positive cup coordinates and a nonidentity group pullback

The first character on `C₂ × C₂` and the square of the second character give a degree-(1,2)
cup cocycle with trivial `ZMod 2` coefficients. Its ordered basis value is one tensor one;
changing the first basis input makes the coordinate zero. The canonical degree-three class
is the product of the degree-one and degree-two classes through both cup APIs. A coordinate
swap is a genuine nonidentity group map and changes the detected cocycle value to zero.
The basis coordinate proves that the cup cocycle is nonzero.
-/

open CategoryTheory MonoidalCategory groupCohomology
open scoped TensorProduct

noncomputable section
set_option autoImplicit false

namespace CupOneTwoCoordinateTests

private abbrev R := ZMod 2
private abbrev G := Multiplicative (R × R)
private abbrev A : Rep R G := Rep.trivial R G R
private abbrev T : Rep R G := A ⊗ A

private def first : cocycles₁ A :=
  ⟨fun g => g.toAdd.1, (mem_cocycles₁_iff _).2 (fun g h => by
    change g.toAdd.1 + h.toAdd.1 = h.toAdd.1 + g.toAdd.1
    exact add_comm _ _)⟩

private def secondSquare : cocycles₂ A :=
  ⟨fun p => p.1.toAdd.2 * p.2.toAdd.2, (mem_cocycles₂_iff _).2 (fun g h j => by
    change (g.toAdd.2 + h.toAdd.2) * j.toAdd.2 + g.toAdd.2 * h.toAdd.2 =
      h.toAdd.2 * j.toAdd.2 + g.toAdd.2 * (h.toAdd.2 + j.toAdd.2)
    ring)⟩

private def e₁ : G := Multiplicative.ofAdd (1, 0)
private def e₂ : G := Multiplicative.ofAdd (0, 1)
private def product : cocycles₃ T := cupCocycleOneTwo A A first secondSquare
private def coordinate : T →ₗ[R] R := (TensorProduct.lid R R).toLinearMap

private lemma product_basis : coordinate (product (e₁, e₂, e₂)) = 1 := by
  change (TensorProduct.lid R R) ((1 : R) ⊗ₜ[R] (1 : R)) = 1
  simp [smul_eq_mul]

example : coordinate (product (e₁, e₂, e₂)) = 1 := product_basis

example : coordinate (product (e₂, e₂, e₂)) = 0 := by
  change (TensorProduct.lid R R) ((0 : R) ⊗ₜ[R] (1 : R)) = 0
  simp

example : product ≠ 0 := by
  intro h
  have hz := congrArg (fun z : cocycles₃ T => coordinate (z (e₁, e₂, e₂))) h
  rw [product_basis] at hz
  have hzero : coordinate ((0 : cocycles₃ T) (e₁, e₂, e₂)) = 0 := by
    change coordinate 0 = 0
    exact map_zero _
  exact one_ne_zero (hz.trans hzero)

example : cupOneTwo A A (H1π A first) (H2π A secondSquare) = H3π T product :=
  cupOneTwo_H1π_H2π A A first secondSquare

example : (cup G R A A 1 2).hom (H1π A first ⊗ₜ[R] H2π A secondSquare) =
    H3π T product :=
  (cup_one_two_apply G R A A (H1π A first) (H2π A secondSquare)).trans
    (cupOneTwo_H1π_H2π A A first secondSquare)

private abbrev swap : G →* G where
  toFun g := Multiplicative.ofAdd (g.toAdd.2, g.toAdd.1)
  map_one' := rfl
  map_mul' _ _ := rfl

private abbrev coefficientIdentity : Rep.res swap A ⟶ A :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

private abbrev tensorIdentity : Rep.res swap T ⟶ T :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

example : map (A := T) (B := T) swap (coefficientIdentity ⊗ₘ coefficientIdentity) 3
    (cupOneTwo A A (H1π A first) (H2π A secondSquare)) =
      cupOneTwo A A (map swap coefficientIdentity 1 (H1π A first))
        (map swap coefficientIdentity 2 (H2π A secondSquare)) :=
  map_cupOneTwo_of_hom (k := R) (G := G) (H := G) (A := A) (B := A) (A' := A) (B' := A)
    swap coefficientIdentity coefficientIdentity (H1π A first) (H2π A secondSquare)

example : coordinate (mapCocycles₃ swap tensorIdentity product (e₁, e₂, e₂)) = 0 := by
  have h := congrFun (coe_mapCocycles₃ swap tensorIdentity product) (e₁, e₂, e₂)
  change mapCocycles₃ swap tensorIdentity product (e₁, e₂, e₂) =
    tensorIdentity.hom (product (swap e₁, swap e₂, swap e₂)) at h
  have hc := congrArg coordinate h
  exact hc.trans (by
    change (TensorProduct.lid R R) ((0 : R) ⊗ₜ[R] (0 : R)) = 0
    simp)

end CupOneTwoCoordinateTests
