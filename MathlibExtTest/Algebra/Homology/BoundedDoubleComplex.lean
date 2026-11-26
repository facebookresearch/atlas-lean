/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.BoundedDoubleComplex
import Mathlib.Tactic.Ring

/-!
# Tests for bounded double complexes

A square double complex over `ℤ`, with `ℤ` in bidegrees `(0, 0)`, `(1, 0)`, `(0, 1)` and
`(1, 1)` and `0` elsewhere, pins the sign convention of the total differential
`dTot = dH + (-1)^p dV`: no sign in degree `0`, and a sign on the vertical part from column `1`.
-/

@[expose] public section

noncomputable section

namespace DoubleComplexTest

open DoubleComplex

/-- The rank of the cell in bidegree `(p, q)`. -/
private abbrev dim : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 1, 0 => 1
  | 0, 1 => 1
  | 1, 1 => 1
  | _, _ => 0

/-- The cell in bidegree `(p, q)`. -/
private abbrev cell (p q : ℕ) : Type := Fin (dim p q) → ℤ

/-- Horizontal differentials: multiplication by `2` and by `4` out of column `0`. -/
private abbrev hor : ∀ p q, cell p q →ₗ[ℤ] cell (p + 1) q
  | 0, 0 => (2 : ℤ) • LinearMap.id
  | 0, 1 => (4 : ℤ) • LinearMap.id
  | _, _ => 0

/-- Vertical differentials: multiplication by `3` and by `6` out of row `0`. -/
private abbrev ver : ∀ p q, cell p q →ₗ[ℤ] cell p (q + 1)
  | 0, 0 => (3 : ℤ) • LinearMap.id
  | 1, 0 => (6 : ℤ) • LinearMap.id
  | _, _ => 0

/-- The square double complex; the differentials commute because `6 * 2 = 4 * 3`. -/
private abbrev square : Bounded ℤ where
  C := cell
  dH := hor
  dV := ver
  dH_sq _ _ := LinearMap.zero_comp _
  dV_sq
    | 0, _ => LinearMap.zero_comp _
    | 1, _ => LinearMap.zero_comp _
    | _ + 2, _ => LinearMap.zero_comp _
  dHV_comm
    | 0, 0 => LinearMap.ext fun x => funext fun i =>
        show (6 : ℤ) * (2 * x i) = 4 * (3 * x i) by ring
    | 0, _ + 1 => (LinearMap.zero_comp _).trans (LinearMap.zero_comp _).symm
    | _ + 1, _ => (LinearMap.zero_comp _).trans (LinearMap.zero_comp _).symm
  N := 2
  hBound
    | _ + 2, _, _ => inferInstanceAs (Subsingleton (Fin 0 → ℤ))
    | 0, _ + 2, _ => inferInstanceAs (Subsingleton (Fin 0 → ℤ))
    | 1, _ + 2, _ => inferInstanceAs (Subsingleton (Fin 0 → ℤ))
    | 0, 0, h | 0, 1, h | 1, 0, h | 1, 1, h => by omega

/-- In degree `0` the total differential has no sign: its components are `dH` and `dV`. -/
example (i : Fin 1) :
    dTot square 0 (fun _ _ => 1) ⟨(1, 0), rfl⟩ i = 2 ∧
      dTot square 0 (fun _ _ => 1) ⟨(0, 1), rfl⟩ i = 3 :=
  ⟨rfl, rfl⟩

/-- From column `1` the vertical part carries the sign `(-1)^p`:
`dTot` on `(1, 1)` is `dH - dV`, here `4 - 6`. -/
example (i : Fin 1) : dTot square 1 (fun _ _ => 1) ⟨(1, 1), rfl⟩ i = -2 :=
  rfl

/-- The total differential squares to zero on the square complex. -/
example : dTot square 1 ∘ₗ dTot square 0 = 0 :=
  dTot_comp_dTot square 0

end DoubleComplexTest
