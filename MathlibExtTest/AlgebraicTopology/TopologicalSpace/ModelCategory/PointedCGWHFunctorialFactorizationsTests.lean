/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHFunctorialFactorizations
import MathlibExt.AlgebraicTopology.ModelCategory.Replacement

/-!
# Tests for the selected pointed CGWH functorial factorizations
-/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.MorphismProperty HomotopicalAlgebra

namespace MathlibExtTest.PointedCGWHFunctorialFactorizationsTests

section ScopeOff

example : True := by
  fail_if_success
    let _ : ModelCategory PointedCGWH.{u, v} := inferInstance
  fail_if_success
    let _ : HasFunctorialFactorization (cofibrations PointedCGWH.{u, v})
        (trivialFibrations PointedCGWH.{u, v}) := inferInstance
  fail_if_success
    let _ : HasFunctorialFactorization
        (trivialCofibrations PointedCGWH.{u, v})
        (fibrations PointedCGWH.{u, v}) := inferInstance
  trivial

end ScopeOff

section Selected

open scoped CGWH.modelCategory

#check CGWH.modelCategory.instPointedCGWHHasFunctorialFactorizationCofibrationsTrivialFibrations
#check CGWH.modelCategory.instPointedCGWHHasFunctorialFactorizationTrivialCofibrationsFibrations

#synth ModelCategory CGWH.{u, v}
#synth ModelCategory PointedCGWH.{u, v}
#synth HasFunctorialFactorization (cofibrations PointedCGWH.{u, v})
  (trivialFibrations PointedCGWH.{u, v})
#synth HasFunctorialFactorization
  (trivialCofibrations PointedCGWH.{u, v})
  (fibrations PointedCGWH.{u, v})

#synth HasFunctorialFactorization (cofibrations PointedCGWH.{0, 0})
  (trivialFibrations PointedCGWH.{0, 0})
#synth HasFunctorialFactorization
  (trivialCofibrations PointedCGWH.{0, 0})
  (fibrations PointedCGWH.{0, 0})
#synth HasFunctorialFactorization (cofibrations PointedCGWH.{1, 1})
  (trivialFibrations PointedCGWH.{1, 1})
#synth HasFunctorialFactorization
  (trivialCofibrations PointedCGWH.{1, 1})
  (fibrations PointedCGWH.{1, 1})
#synth HasFunctorialFactorization (cofibrations PointedCGWH.{0, 1})
  (trivialFibrations PointedCGWH.{0, 1})
#synth HasFunctorialFactorization
  (trivialCofibrations PointedCGWH.{0, 1})
  (fibrations PointedCGWH.{0, 1})
#synth HasFunctorialFactorization (cofibrations PointedCGWH.{1, 0})
  (trivialFibrations PointedCGWH.{1, 0})
#synth HasFunctorialFactorization
  (trivialCofibrations PointedCGWH.{1, 0})
  (fibrations PointedCGWH.{1, 0})

example :
    (inferInstance : HasFunctorialFactorization
      (cofibrations PointedCGWH.{u, v})
      (trivialFibrations PointedCGWH.{u, v})) =
      CGWH.modelCategory.instPointedCGWHHasFunctorialFactorizationCofibrationsTrivialFibrations :=
  rfl

example :
    (inferInstance : HasFunctorialFactorization
      (trivialCofibrations PointedCGWH.{u, v})
      (fibrations PointedCGWH.{u, v})) =
      CGWH.modelCategory.instPointedCGWHHasFunctorialFactorizationTrivialCofibrationsFibrations :=
  rfl

variable {X Y : PointedCGWH.{u, v}}

example (f : X ⟶ Y) :
    cofibrations PointedCGWH.{u, v}
      ((functorialFactorizationData (cofibrations PointedCGWH.{u, v})
        (trivialFibrations PointedCGWH.{u, v})).factorizationData f).i :=
  ((functorialFactorizationData (cofibrations PointedCGWH.{u, v})
    (trivialFibrations PointedCGWH.{u, v})).factorizationData f).hi

example (f : X ⟶ Y) :
    trivialFibrations PointedCGWH.{u, v}
      ((functorialFactorizationData (cofibrations PointedCGWH.{u, v})
        (trivialFibrations PointedCGWH.{u, v})).factorizationData f).p :=
  ((functorialFactorizationData (cofibrations PointedCGWH.{u, v})
    (trivialFibrations PointedCGWH.{u, v})).factorizationData f).hp

example (f : X ⟶ Y) :
    ((functorialFactorizationData (cofibrations PointedCGWH.{u, v})
        (trivialFibrations PointedCGWH.{u, v})).factorizationData f).i ≫
      ((functorialFactorizationData (cofibrations PointedCGWH.{u, v})
        (trivialFibrations PointedCGWH.{u, v})).factorizationData f).p = f :=
  ((functorialFactorizationData (cofibrations PointedCGWH.{u, v})
    (trivialFibrations PointedCGWH.{u, v})).factorizationData f).fac

example (f : X ⟶ Y) :
    trivialCofibrations PointedCGWH.{u, v}
      ((functorialFactorizationData
        (trivialCofibrations PointedCGWH.{u, v})
        (fibrations PointedCGWH.{u, v})).factorizationData f).i :=
  ((functorialFactorizationData
    (trivialCofibrations PointedCGWH.{u, v})
    (fibrations PointedCGWH.{u, v})).factorizationData f).hi

example (f : X ⟶ Y) :
    fibrations PointedCGWH.{u, v}
      ((functorialFactorizationData
        (trivialCofibrations PointedCGWH.{u, v})
        (fibrations PointedCGWH.{u, v})).factorizationData f).p :=
  ((functorialFactorizationData
    (trivialCofibrations PointedCGWH.{u, v})
    (fibrations PointedCGWH.{u, v})).factorizationData f).hp

example (f : X ⟶ Y) :
    ((functorialFactorizationData
        (trivialCofibrations PointedCGWH.{u, v})
        (fibrations PointedCGWH.{u, v})).factorizationData f).i ≫
      ((functorialFactorizationData
        (trivialCofibrations PointedCGWH.{u, v})
        (fibrations PointedCGWH.{u, v})).factorizationData f).p = f :=
  ((functorialFactorizationData
    (trivialCofibrations PointedCGWH.{u, v})
    (fibrations PointedCGWH.{u, v})).factorizationData f).fac

#check cofibrantReplacement (C := PointedCGWH.{u, v})
#check cofibrantReplacementCounit (C := PointedCGWH.{u, v})
#check fibrantReplacement (C := PointedCGWH.{u, v})
#check fibrantReplacementUnit (C := PointedCGWH.{u, v})

example (X : PointedCGWH.{u, v}) :
    IsCofibrant
      ((cofibrantReplacement (C := PointedCGWH.{u, v})).obj X) :=
  inferInstance

example (X : PointedCGWH.{u, v}) :
    WeakEquivalence ((cofibrantReplacementCounit
      (C := PointedCGWH.{u, v})).app X) :=
  inferInstance

example (X : PointedCGWH.{u, v}) :
    IsFibrant
      ((fibrantReplacement (C := PointedCGWH.{u, v})).obj X) :=
  inferInstance

example (X : PointedCGWH.{u, v}) :
    WeakEquivalence ((fibrantReplacementUnit
      (C := PointedCGWH.{u, v})).app X) :=
  inferInstance

end Selected

section FirstInstanceDeletion

open scoped CGWH.modelCategory

attribute [-instance]
  CGWH.modelCategory.instPointedCGWHHasFunctorialFactorizationCofibrationsTrivialFibrations in
example : True := by
  fail_if_success
    let _ : HasFunctorialFactorization (cofibrations PointedCGWH.{u, v})
      (trivialFibrations PointedCGWH.{u, v}) := inferInstance
  trivial

end FirstInstanceDeletion

section SecondInstanceDeletion

open scoped CGWH.modelCategory

attribute [-instance]
  CGWH.modelCategory.instPointedCGWHHasFunctorialFactorizationTrivialCofibrationsFibrations in
example : True := by
  fail_if_success
    let _ : HasFunctorialFactorization
        (trivialCofibrations PointedCGWH.{u, v})
        (fibrations PointedCGWH.{u, v}) := inferInstance
  trivial

end SecondInstanceDeletion

section ScopeTeardown

example : True := by
  fail_if_success
    let _ : HasFunctorialFactorization (cofibrations PointedCGWH.{u, v})
        (trivialFibrations PointedCGWH.{u, v}) := inferInstance
  fail_if_success
    let _ : HasFunctorialFactorization
        (trivialCofibrations PointedCGWH.{u, v})
        (fibrations PointedCGWH.{u, v}) := inferInstance
  trivial

end ScopeTeardown

/-- error: Unknown constant `PointedCGWH.cofibrantReplacement` -/
#guard_msgs in
#check PointedCGWH.cofibrantReplacement

/-- error: Unknown constant `PointedCGWH.fibrantReplacement` -/
#guard_msgs in
#check PointedCGWH.fibrantReplacement

#print axioms
  CGWH.modelCategory.instPointedCGWHHasFunctorialFactorizationCofibrationsTrivialFibrations
#print axioms
  CGWH.modelCategory.instPointedCGWHHasFunctorialFactorizationTrivialCofibrationsFibrations

end MathlibExtTest.PointedCGWHFunctorialFactorizationsTests
