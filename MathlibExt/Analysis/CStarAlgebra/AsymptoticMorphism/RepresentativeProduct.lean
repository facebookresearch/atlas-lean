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

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.IteratedAlgebra

public import Mathlib.CategoryTheory.EqToHom

/-!
# Products of finite-stage representatives

The canonical finite-iteration transport is owned by `IteratedAlgebra`.
This module uses it to package the literal representative composite

```text
(map n psi).comp phi : A -> alpha^n(alpha^m C)
```

at summed stage `n + m`.

This is representative-level data only. There is no class product, path/alpha
comparison, direct-limit operation, flattening map, associativity theorem, or
E-theory product here.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory
open scoped CStarAlgebra

noncomputable section

attribute [local instance] AsymptoticAlgebra.cStarAlgebra

namespace IteratedAsymptoticAlgebra

universe uA uB uC

/-- Compose finite-stage representatives. The mathematical composite is
`(map n psi).comp phi`; `iteratedAddHom` only transports its canonical
stored carrier to the literal summed stage. -/
def productRepresentative (n m : ℕ)
    {A : Type uA} {B : Type uB} {C : Type uC}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C]
    (phi : HomN n A B) (psi : HomN m B C) : HomN (n + m) A C :=
  (iteratedAddHom n m C).comp ((map n psi).comp phi)

@[simp]
theorem productRepresentative_apply (n m : ℕ)
    {A : Type uA} {B : Type uB} {C : Type uC}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C]
    (phi : HomN n A B) (psi : HomN m B C) (a : A) :
    productRepresentative n m phi psi a =
      iteratedAddHom n m C (map n psi (phi a)) :=
  rfl

/-- At source stage zero, representative product is ordinary composition. -/
private theorem map_zero_stage_eq_eqToHom_comp
    (m : ℕ)
    {B : Type uB} {C : Type uC}
    [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
    (psi : HomN m B C) :
    map 0 psi =
      (eqToHom
        (NonUnitalCStarAlgCat.iteratedAsymptoticAlgebraObject_zero
          (NonUnitalCStarAlgCat.iteratedAsymptoticAlgebraObject m
            (NonUnitalCStarAlgCat.of C))).symm).comp psi := by
  rw [map_zero_stage]
  rfl

/-- At source stage zero, representative product is ordinary composition
followed by the explicit transport from stage `m` to literal stage `0+m`. -/
theorem productRepresentative_zero_left (m : ℕ)
    {A : Type uA} {B : Type uB} {C : Type uC}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C]
    (phi : HomN 0 A B) (psi : HomN m B C) :
    productRepresentative 0 m phi psi =
      (eqToHom
        (congrArg
          (fun k => NonUnitalCStarAlgCat.iteratedAsymptoticAlgebraObject k
            (NonUnitalCStarAlgCat.of C))
          (Nat.zero_add m)).symm).comp (psi.comp phi) := by
  unfold productRepresentative
  rw [map_zero_stage_eq_eqToHom_comp]
  calc
    (iteratedAddHom 0 m C).comp
        (((eqToHom
          (NonUnitalCStarAlgCat.iteratedAsymptoticAlgebraObject_zero
            (NonUnitalCStarAlgCat.iteratedAsymptoticAlgebraObject m
              (NonUnitalCStarAlgCat.of C))).symm).comp psi).comp phi) =
      ((iteratedAddHom 0 m C).comp
        (eqToHom
          (NonUnitalCStarAlgCat.iteratedAsymptoticAlgebraObject_zero
            (NonUnitalCStarAlgCat.iteratedAsymptoticAlgebraObject m
              (NonUnitalCStarAlgCat.of C))).symm)).comp
        (psi.comp phi) := by
          apply NonUnitalStarAlgHom.ext
          intro a
          rfl
    _ = (eqToHom
          (congrArg
            (fun k => NonUnitalCStarAlgCat.iteratedAsymptoticAlgebraObject k
              (NonUnitalCStarAlgCat.of C))
            (Nat.zero_add m)).symm).comp (psi.comp phi) := by
      exact congrArg (fun F => F.comp (psi.comp phi))
        (iteratedAddHom_zero_left m C)

/-- At coefficient stage zero, only the existing `map n` action remains. -/
theorem productRepresentative_zero_right (n : ℕ)
    {A : Type uA} {B : Type uB} {C : Type uC}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C]
    (phi : HomN n A B) (psi : HomN 0 B C) :
    productRepresentative n 0 phi psi = (map n psi).comp phi := by
  unfold productRepresentative
  rw [iteratedAddHom_zero_right]
  apply NonUnitalStarAlgHom.ext
  intro a
  rfl

#print axioms productRepresentative
#print axioms productRepresentative_apply
#print axioms productRepresentative_zero_left
#print axioms productRepresentative_zero_right

end IteratedAsymptoticAlgebra
