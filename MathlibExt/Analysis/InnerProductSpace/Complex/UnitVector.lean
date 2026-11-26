/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Star.Basic

/-!
# Finite normalized complex vectors

For a finite index type I, a UnitVector I has coordinates z_i∈ℂ satisfying ∑i conj(z_i)z_i=1.
This is unit norm in the standard Hermitian ℓ² product on ℂ^I.
-/

@[expose] public section

open scoped BigOperators
open Complex

namespace Complex

/-- **Complex unit vector by coordinates.**

For a finite index type I, UnitVector I consists of z:I→ℂ with ∑i conj(z_i)z_i=1, equivalently
∑i|z_i|²=1.
-/
structure UnitVector (d : Type*) [Fintype d] where
  /-- **Coordinates of a finite complex unit vector.**

For finite I and u:UnitVector I, the field coord:I→ℂ gives z_i with ∑i conj(z_i)z_i=1.
-/
  coord : d → ℂ
  normalized' : ∑ i, star (coord i) * coord i = 1

instance {d : Type*} [Fintype d] :
    CoeFun (UnitVector d) (fun _ => d → ℂ) where
  coe := UnitVector.coord

@[ext]
theorem UnitVector.ext {d : Type*} [Fintype d]
    {u v : UnitVector d} (h : ∀ i, u.coord i = v.coord i) : u = v := by
  have hfun : u.coord = v.coord := funext h
  cases u with
  | mk coord₁ norm₁ =>
    cases v with
    | mk coord₂ norm₂ =>
      simp_all

end Complex
