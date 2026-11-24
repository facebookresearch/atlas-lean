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
# Finite complex unit vectors

This module defines finite-dimensional normalized complex vectors in the
natural complex inner-product domain. A unit vector is indexed by a finite
type and satisfies the normalization condition `∑ i, star (coord i) * coord i = 1`,
corresponding to unit norm in the standard complex inner product on `d → ℂ`.

## Main definitions

* `Complex.UnitVector d` – unit vector on index type `d` with complex coordinates.

## Main results

* `UnitVector.ext` – extensionality by coordinates.
-/

@[expose] public section

open scoped BigOperators
open Complex

namespace Complex

/-- A finite-dimensional normalized complex vector in the natural complex
    inner-product space, indexed by a finite type `d`. Normalization is
    expressed as `∑ i, star (coord i) * coord i = 1`, i.e. unit norm for the
    standard Hermitian inner product on `d → ℂ`. -/
structure UnitVector (d : Type*) [Fintype d] where
  /-- The complex coordinates of the vector, indexed by `d`. -/
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
