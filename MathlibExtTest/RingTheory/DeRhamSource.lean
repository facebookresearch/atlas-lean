/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.DeRhamSource.Complex
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Tests for the de Rham complex of a ring map

For the polynomial ring `ℤ[x, y]` over `ℤ`, the de Rham differential sends `x · dy` to
`dx ∧ dy`, kills the exact form `dy`, and squares to zero; the degree-zero arrow of the de Rham
complex is the universal derivation.
-/

open MathlibExt.DeRhamSource MathlibExt.DeRhamSource.KaehlerDifferential
open _root_.KaehlerDifferential

noncomputable section

namespace MathlibExtTest.DeRhamSource

private abbrev P := MvPolynomial (Fin 2) ℤ

private abbrev x : P := MvPolynomial.X 0
private abbrev y : P := MvPolynomial.X 1

/-- `d (x · dy) = dx ∧ dy`. -/
example : deRhamDifferential (A := ℤ) (B := P) 1
    (x • exteriorPower.ιMulti P 1 fun _ ↦ D ℤ P y) =
      exteriorPower.ιMulti P 2 ![D ℤ P x, D ℤ P y] := by
  have h := deRhamDifferential_smul_ιMulti_D (A := ℤ) (B := P) 1 ![x, y]
  have e1 : (fun i : Fin 1 ↦ D ℤ P (![x, y] i.succ)) = fun _ ↦ D ℤ P y := by
    funext i
    fin_cases i
    rfl
  have e2 : (fun i : Fin 2 ↦ D ℤ P (![x, y] i)) = ![D ℤ P x, D ℤ P y] := by
    funext i
    fin_cases i <;> rfl
  rw [e1, e2] at h
  exact h

/-- The exact form `dy = d(1 · y)` is closed: `d(dy) = 0`. -/
example : deRhamDifferential (A := ℤ) (B := P) 1
    (exteriorPower.ιMulti P 1 fun _ ↦ D ℤ P y) = 0 := by
  have h := deRhamDifferential_smul_ιMulti_D (A := ℤ) (B := P) 1 ![1, y]
  have e1 : (fun i : Fin 1 ↦ D ℤ P (![1, y] i.succ)) = fun _ ↦ D ℤ P y := by
    funext i
    fin_cases i
    rfl
  rw [e1] at h
  have h1 : (![1, y] 0 : P) = 1 := rfl
  rw [h1, one_smul] at h
  rw [h]
  exact (exteriorPower.ιMulti P 2).map_coord_zero (i := 0) (by simp)

/-- The de Rham differential squares to zero. -/
example (ξ : ⋀[P]^1 (Ω[P⁄ℤ])) :
    deRhamDifferential (A := ℤ) 2 (deRhamDifferential 1 ξ) = 0 :=
  deRhamDifferential_comp_self 1 ξ

/-- In degree zero the arrow of the de Rham complex is the universal derivation. -/
example (b : P) :
    ((deRhamComplex ℤ P).d 0 1).hom (b • exteriorPower.ιMulti P 0 fun i ↦ D ℤ P (![b] i.succ)) =
      exteriorPower.ιMulti P 1 fun _ ↦ D ℤ P b := by
  have h := deRhamComplex_d_smul_ιMulti_D (A := ℤ) (B := P) 0 ![b]
  have e : (fun i : Fin 1 ↦ D ℤ P (![b] i)) = fun _ ↦ D ℤ P b := by
    funext i
    fin_cases i
    rfl
  rw [e] at h
  exact h

end MathlibExtTest.DeRhamSource
