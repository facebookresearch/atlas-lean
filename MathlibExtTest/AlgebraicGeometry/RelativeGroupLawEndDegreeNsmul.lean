/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.RelativeGroupLawEndDegreeNsmul

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace RelativeGroupLawEndDegreeNsmulTest

/-- Source-shaped consumer with the original binders, at `n = 1`. -/
example {K : Type u} [Field K] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of K)) (L : RelativeGroupLaw K f)
    (g : ℕ) :
    L.endDegree (L.nsmul f 1 RelativeGroupLaw.idPoint) = 1 ^ (2 * g) :=
  L.endDegree_nsmul_one_idPoint_eq_pow g

/-- Higher-universe consumer. -/
example {K : Type v} [Field K] {A : Scheme.{v}}
    (f : A ⟶ Spec (CommRingCat.of K)) (L : RelativeGroupLaw K f)
    (g : ℕ) :
    L.endDegree (L.nsmul f 1 RelativeGroupLaw.idPoint) = 1 ^ (2 * g) :=
  L.endDegree_nsmul_one_idPoint_eq_pow g

/-- Boundary example: at `g = 0` the formula gives `1`. -/
example {K : Type u} [Field K] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of K)) (L : RelativeGroupLaw K f) :
    L.endDegree (L.nsmul f 1 RelativeGroupLaw.idPoint) = 1 := by
  rw [L.endDegree_nsmul_one_idPoint_eq_pow 0, pow_zero]

end RelativeGroupLawEndDegreeNsmulTest
