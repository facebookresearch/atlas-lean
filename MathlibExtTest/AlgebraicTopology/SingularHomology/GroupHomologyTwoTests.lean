/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SingularHomology.GroupHomologyTwo
import MathlibExt.KTheory.Ring.SteinbergPlusFiberPerfectness

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial

universe u

/-- Original acyclicity supplies native H2 of the same canonical singular carrier. -/
example (X : TopCat.{u}) (hX : TopCat.IsAcyclicSpace X) :
    IsZero ((TopCat.toSSet.obj X).homology
      (singularIntegralCoefficients : AddCommGrpCat.{u}) 2) :=
  TopCat.nativeSingularHomologyTwo_isZero_of_isAcyclicSpace X hX

/-- The actual ordinary based group is the target of the canonical H2 transport. -/
example (X : TopCat.{u}) (x : X) :
    groupHomology (Rep.trivial (ULift.{u} ℤ)
      (End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm x))) (ULift.{u} ℤ)) 2 ≅
        groupHomology (Rep.trivial (ULift.{u} ℤ) (FundamentalGroup X x) (ULift.{u} ℤ)) 2 :=
  TopCat.singularFundamentalGroupHomologyTwoIso X x

/-- The original point of an actual acyclic space gives the genuine ordinary-group H2 result. -/
example (X : TopCat.{u}) (x : X) (hX : TopCat.IsAcyclicSpace X) :
    IsZero (groupHomology (Rep.trivial (ULift.{u} ℤ)
      (FundamentalGroup X x) (ULift.{u} ℤ)) 2) :=
  TopCat.groupHomologyTwo_isZero_of_isAcyclicSpace X x hX

/-- The original independently constructed plus fiber consumes its existing
actual acyclicity theorem and original selected point. No group-H2 outcome is an input. -/
example (R : Type u) [Ring R] :
    IsZero (groupHomology (Rep.trivial (ULift.{u} ℤ)
      (FundamentalGroup (AlgebraicKTheory.StableGL.independentPlusFiber R)
        (AlgebraicKTheory.StableGL.independentPlusFiberPoint R)) (ULift.{u} ℤ)) 2) :=
  TopCat.groupHomologyTwo_isZero_of_isAcyclicSpace
    (AlgebraicKTheory.StableGL.independentPlusFiber R)
    (AlgebraicKTheory.StableGL.independentPlusFiberPoint R)
    (AlgebraicKTheory.StableGL.independentPlusFiber_isAcyclic R)

end
