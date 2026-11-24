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

public import MathlibExt.KTheory.Ring.K2.SteinbergSymbol
import MathlibExt.KTheory.Ring.K2.StableSteinbergWeylRelations

/-! # Mixed-torus commutator bridge

The canonical torus cocycle as a mixed torus commutator.
-/

@[expose] public section

universe u

open scoped commutatorElement

namespace AlgebraicKTheory.StableSteinberg

/-- The canonical torus cocycle is a mixed torus commutator. -/
public theorem torusCocycle_eq_commutatorElement {F : Type u} [Field F]
    (u v : Fˣ) :
    torusCocycle u v =
      ⁅torus 0 1 (by omega) u, torus 0 2 (by omega) v⁆ := by
  let h01 : (0 : ℕ) ≠ 1 := by omega
  let h02 : (0 : ℕ) ≠ 2 := by omega
  let h21 : (2 : ℕ) ≠ 1 := by omega
  have hConj :
      torus 0 2 h02 v * torus 0 1 h01 u *
          (torus 0 2 h02 v)⁻¹ =
        torus 0 1 h01 (u * v) *
          (torus 0 1 h01 v)⁻¹ := by
    have h :=
      torus_conj_torus (R := F) 0 1 2 h01 h02 h21 v u
    rw [mul_comm v u] at h
    exact h
  change
    torus 0 1 h01 u * torus 0 1 h01 v *
        (torus 0 1 h01 (u * v))⁻¹ =
      ⁅torus 0 1 h01 u, torus 0 2 h02 v⁆
  rw [← commutatorElement_inv
    (torus 0 2 h02 v) (torus 0 1 h01 u)]
  simp only [commutatorElement_def]
  rw [hConj]
  simp only [mul_inv_rev, inv_inv, mul_assoc]

end AlgebraicKTheory.StableSteinberg

end
