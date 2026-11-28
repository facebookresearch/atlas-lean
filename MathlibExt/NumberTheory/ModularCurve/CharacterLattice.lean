/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from https://github.com/anthropics/fermats-last-theorem, compared with the
source file at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`:
`Definitions/Def_ModularCurve_ComponentGroup.lean` (the degree, the character
lattice and the width pairing).
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Pi

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# The character lattice and the width pairing

The degree of an integer-valued function on a finite type, the degree-zero character lattice
(the kernel of the degree), and the diagonal pairing weighted by a family of widths. The ribbon
kernel of degeneracy data and its Gram map
(`MathlibExt.NumberTheory.ModularCurve.RibbonKernel`) are stated in these coordinates.
-/

@[expose] public section

namespace ModularCurve

open Finset

section CharacterLattice

variable {ι : Type*} [Fintype ι]

/-- **Degree.** The degree of an integer-valued function on a finite type: the sum of its values. -/
def degreeOn (ι : Type*) [Fintype ι] : (ι → ℤ) →ₗ[ℤ] ℤ :=
  ∑ x : ι, LinearMap.proj x

@[simp] theorem degreeOn_apply (D : ι → ℤ) : degreeOn ι D = ∑ x : ι, D x := by
  simp [degreeOn]

/-- **Character lattice.** The degree-zero character lattice: the kernel of the degree map. -/
def characterLattice (ι : Type*) [Fintype ι] : Submodule ℤ (ι → ℤ) :=
  LinearMap.ker (degreeOn ι)

/-- **Membership in the character lattice.** A function lies in the character lattice exactly when
its values sum to zero. -/
theorem mem_characterLattice {D : ι → ℤ} :
    D ∈ characterLattice ι ↔ ∑ x : ι, D x = 0 := by
  simp [characterLattice, LinearMap.mem_ker]

end CharacterLattice

section Pairing

variable {ι : Type*} [Fintype ι]

/-- **Width pairing.** The pairing `(D, D') ↦ ∑ x, e x * (D x * D' x)` on integer-valued functions,
weighted by the widths `e`. -/
def widthPairing (e : ι → ℕ) : (ι → ℤ) →ₗ[ℤ] (ι → ℤ) →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ (fun D D' => ∑ x : ι, (e x : ℤ) * (D x * D' x))
    (fun D₁ D₂ D' => by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by simp only [Pi.add_apply]; ring)
    (fun c D D' => by
      rw [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by
        simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun D D'₁ D'₂ => by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by simp only [Pi.add_apply]; ring)
    (fun c D D' => by
      rw [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by
        simp only [Pi.smul_apply, smul_eq_mul]; ring)

@[simp] theorem widthPairing_apply (e : ι → ℕ) (D D' : ι → ℤ) :
    widthPairing e D D' = ∑ x : ι, (e x : ℤ) * (D x * D' x) := by
  simp only [widthPairing, LinearMap.mk₂_apply]

/-- **Symmetry of the width pairing.** The width pairing is symmetric. -/
theorem widthPairing_comm (e : ι → ℕ) (D D' : ι → ℤ) :
    widthPairing e D D' = widthPairing e D' D := by
  simp only [widthPairing_apply]
  exact Finset.sum_congr rfl fun x _ => by ring

end Pairing

end ModularCurve
