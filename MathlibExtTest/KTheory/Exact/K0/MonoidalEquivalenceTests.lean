/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

import MathlibExt.KTheory.Exact.K0.Equivalence
import MathlibExt.KTheory.Exact.K0.SplitRing

/-!
# Public clients for the ring equivalence on exact-category K₀

The categories have independent object and morphism universes. Only the
forward equivalence functor is supplied with a strong monoidal structure.
The split-exact clients compose the genuine Grothendieck-ring comparison
with the same equivalence and retain the original inverse generators.
-/

open CategoryTheory Limits MonoidalCategory
open AlgebraicKTheory

universe v₁ u₁ v₂ u₂

section Exact

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C]
  [ExactCategory.IsTensorBiexact C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
  [MonoidalCategory D] [BraidedCategory D] [MonoidalPreadditive D]
  [ExactCategory.IsTensorBiexact D]
variable (e : C ≌ D) [e.functor.Additive] [e.inverse.Additive]
  [e.functor.IsExact] [e.inverse.IsExact] [e.functor.Monoidal]

example : (K0.ringEquivOfEquivalence e).toAddEquiv = K0.equivOfEquivalence e :=
  K0.ringEquivOfEquivalence_toAddEquiv e

example : (K0.ringEquivOfEquivalence e).toRingHom = K0.mapRing e.functor :=
  K0.ringEquivOfEquivalence_toRingHom e

example (x : K0 C) : K0.ringEquivOfEquivalence e x = K0.map e.functor x :=
  rfl

example (y : K0 D) : (K0.ringEquivOfEquivalence e).symm y = K0.map e.inverse y :=
  rfl

example (X : C) :
    K0.ringEquivOfEquivalence e (K0.mk X) = K0.mk (e.functor.obj X) :=
  K0.ringEquivOfEquivalence_mk e X

example (Y : D) :
    (K0.ringEquivOfEquivalence e).symm (K0.mk Y) = K0.mk (e.inverse.obj Y) :=
  K0.ringEquivOfEquivalence_symm_mk e Y

example (X Y : C) :
    K0.ringEquivOfEquivalence e (K0.mk (X ⊗ Y)) =
      K0.mk (e.functor.obj X) * K0.mk (e.functor.obj Y) := by
  rw [← K0.mk_mul, map_mul, K0.ringEquivOfEquivalence_mk,
    K0.ringEquivOfEquivalence_mk]

example : K0.ringEquivOfEquivalence e (K0.mk (𝟙_ C)) = (1 : K0 D) := by
  rw [K0.one_eq, map_one]

end Exact

section Identity

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C]
  [ExactCategory.IsTensorBiexact C]

local instance : (CategoryTheory.Equivalence.refl : C ≌ C).functor.Additive :=
  inferInstanceAs ((𝟭 C).Additive)
local instance : (CategoryTheory.Equivalence.refl : C ≌ C).inverse.Additive :=
  inferInstanceAs ((𝟭 C).Additive)
local instance : (CategoryTheory.Equivalence.refl : C ≌ C).functor.IsExact :=
  inferInstanceAs ((𝟭 C).IsExact)
local instance : (CategoryTheory.Equivalence.refl : C ≌ C).inverse.IsExact :=
  inferInstanceAs ((𝟭 C).IsExact)
local instance : (CategoryTheory.Equivalence.refl : C ≌ C).functor.Monoidal :=
  inferInstanceAs ((𝟭 C).Monoidal)

example (x : K0 C) :
    K0.ringEquivOfEquivalence (CategoryTheory.Equivalence.refl : C ≌ C) x = x := by
  change K0.map (𝟭 C) x = x
  exact DFunLike.congr_fun K0.map_id x

end Identity

section Split

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D]
  [MonoidalCategory D] [BraidedCategory D] [MonoidalPreadditive D]

local instance : ExactCategory C := ExactCategory.splitExactCategory (C := C)
local instance : ExactCategory D := ExactCategory.splitExactCategory (C := D)
local instance : ExactCategory.IsTensorBiexact C := ExactCategory.splitIsTensorBiexact C
local instance : ExactCategory.IsTensorBiexact D := ExactCategory.splitIsTensorBiexact D

variable (e : C ≌ D) [e.functor.Additive] [e.inverse.Additive] [e.functor.Monoidal]

local instance : e.functor.IsExact := ExactCategory.isExact_splitSource _
local instance : e.inverse.IsExact := ExactCategory.isExact_splitSource _

example (X : C) :
    ((K0.splitRingIso C).commRingCatIsoToRingEquiv.trans (K0.ringEquivOfEquivalence e))
        (Algebra.GrothendieckAddGroup.of (toSkeleton X)) = K0.mk (e.functor.obj X) := by
  change K0.ringEquivOfEquivalence e
    ((K0.splitRingIso C).hom (Algebra.GrothendieckAddGroup.of (toSkeleton X))) = _
  rw [K0.splitRingIso_hom_of_toSkeleton, K0.ringEquivOfEquivalence_mk]

example (Y : D) :
    ((K0.splitRingIso C).commRingCatIsoToRingEquiv.trans (K0.ringEquivOfEquivalence e)).symm
        (K0.mk Y) = Algebra.GrothendieckAddGroup.of (toSkeleton (e.inverse.obj Y)) := by
  change (K0.splitRingIso C).inv ((K0.ringEquivOfEquivalence e).symm (K0.mk Y)) = _
  rw [K0.ringEquivOfEquivalence_symm_mk, K0.splitRingIso_inv_mk]

end Split

#print axioms AlgebraicKTheory.K0.ringEquivOfEquivalence
#print axioms AlgebraicKTheory.K0.ringEquivOfEquivalence_toAddEquiv
#print axioms AlgebraicKTheory.K0.ringEquivOfEquivalence_toRingHom
#print axioms AlgebraicKTheory.K0.ringEquivOfEquivalence_mk
#print axioms AlgebraicKTheory.K0.ringEquivOfEquivalence_symm_mk
