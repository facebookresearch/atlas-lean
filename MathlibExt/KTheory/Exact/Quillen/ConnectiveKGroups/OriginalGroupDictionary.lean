/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.ConnectiveKGroups
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Original current group operations and exact K-zero dictionary

The existing current positive group has the same complete stock cube
group structure. Its multiplication and unit are read out through those
public equality theorems.

The existing exact K-zero dictionary becomes a multiplicative equivalence
by the native additive/multiplicative type tags. Both whole functions and
the original exact-functor naturality square retain that same dictionary.
All category object and Hom universes remain independent.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits
open AlgebraicKTheory.ConnectiveKGroups
open scoped Topology

namespace AlgebraicKTheory.ConnectiveKGroups

universe uC vC uD vD

variable (C : Type uC) [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- The actual current positive group is the complete original stock cube group. -/
theorem groupStructure_succ_original (n : ℕ) :
    groupStructure C (n + 1) =
      HomotopyGroup.group (X := NQKSpace C) (x := zeroLoop C) (Fin (n + 1)) :=
  (groupStructure_succ_value C n).trans (NQKSpaceOriginalPositiveGroup_value C n (zeroLoop C))

/-- Every current positive unit is the unit of the same original stock cube group. -/
theorem groupStructure_succ_one_original (n : ℕ) :
    @One.one (groupCarrier C (n + 1))
      (groupStructure C (n + 1)).toMulOneClass.toMulOne.toOne =
    @One.one (groupCarrier C (n + 1))
      (HomotopyGroup.group (X := NQKSpace C)
        (x := zeroLoop C) (Fin (n + 1))).toMulOneClass.toMulOne.toOne :=
  congrArg (fun g : Group (groupCarrier C (n + 1)) =>
    g.toMulOneClass.toMulOne.toOne.one)
    (groupStructure_succ_original C n)

/-- Every current positive multiplication is the same original stock cube multiplication. -/
theorem groupStructure_succ_mul_original (n : ℕ)
    (a b : groupCarrier C (n + 1)) :
    @Mul.mul (groupCarrier C (n + 1))
      (groupStructure C (n + 1)).toMulOneClass.toMulOne.toMul a b =
    @Mul.mul (groupCarrier C (n + 1))
      (HomotopyGroup.group (X := NQKSpace C)
        (x := zeroLoop C) (Fin (n + 1))).toMulOneClass.toMulOne.toMul a b :=
  congrArg (fun g : Group (groupCarrier C (n + 1)) =>
    g.toMulOneClass.toMulOne.toMul.mul a b)
    (groupStructure_succ_original C n)

/-- The actual current degree-zero group uses its existing canonical exact K-zero dictionary. -/
def groupExactK0MulEquiv :
    @MulEquiv (groupCarrier C 0) (Multiplicative (K0 C))
      (groupStructure C 0).toMulOneClass.toMulOne.toMul inferInstance := by
  let : Mul (groupCarrier C 0) := (groupStructure C 0).toMulOneClass.toMulOne.toMul
  exact AddEquiv.toMultiplicativeRight (groupExactK0Equiv C)

/-- Every current-zero forward uses the same original exact K-zero evaluator. -/
theorem groupExactK0MulEquiv_apply (g : groupCarrier C 0) :
    groupExactK0MulEquiv C g =
      Multiplicative.ofAdd (groupExactK0Equiv C (Additive.ofMul g)) := rfl

/-- Every current-zero inverse uses the inverse of that same original exact dictionary. -/
theorem groupExactK0MulEquiv_symm_apply (g : Multiplicative (K0 C)) :
    letI : Mul (groupCarrier C 0) := (groupStructure C 0).toMulOneClass.toMulOne.toMul
    (groupExactK0MulEquiv C).symm g =
      Additive.toMul ((groupExactK0Equiv C).symm (Multiplicative.toAdd g)) := by
  let : Mul (groupCarrier C 0) := (groupStructure C 0).toMulOneClass.toMulOne.toMul
  rfl

variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]

/-- The whole original current degree-zero functor map retains canonical exact K-zero naturality. -/
theorem groupExactK0MulEquiv_naturality
    (F : C ⥤ D) [F.Additive] [F.IsExact] (g : groupCarrier C 0) :
    groupExactK0MulEquiv D (groupMap C F 0 g) =
      (K0.map F).toMultiplicative (groupExactK0MulEquiv C g) :=
  congrArg Multiplicative.ofAdd (groupExactK0Equiv_naturality C F g)

end AlgebraicKTheory.ConnectiveKGroups
