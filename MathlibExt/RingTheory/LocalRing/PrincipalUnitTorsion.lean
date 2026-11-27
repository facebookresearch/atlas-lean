/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsLocalRing_eq_one_of_pow_eq_one_of_sub_one_mem_maximalIdeal.lean`
and
`P2M/Sol/S_IsLocalRing_eq_one_of_pow_eq_one_of_sub_one_mem_maximalIdeal.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

@[expose] public section

universe u

open IsLocalRing

namespace IsLocalRing

private theorem geomSum_sub_natCast_mem_maximalIdeal {A : Type u}
    [CommRing A] [IsLocalRing A] {u : A}
    (hu : u - 1 ∈ maximalIdeal A) (n : ℕ) :
    (∑ i ∈ Finset.range n, u ^ i) - (n : A) ∈ maximalIdeal A := by
  have hpow : ∀ i, u ^ i - 1 ∈ maximalIdeal A := fun i => by
    have h : u ^ i - 1 = (u - 1) * ∑ j ∈ Finset.range i, u ^ j := by
      rw [mul_comm, geom_sum_mul]
    exact h ▸ Ideal.mul_mem_right _ _ hu
  have heq : (∑ i ∈ Finset.range n, u ^ i) - (n : A) =
      ∑ i ∈ Finset.range n, (u ^ i - 1) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
  rw [heq]
  exact sum_mem fun i _ => hpow i

/-- Tame torsion vanishes in principal units: if `u ≡ 1` modulo the
maximal ideal of a local ring, `n` is a unit, and `u ^ n = 1`, then
`u = 1`. The cofactor `1 + u + … + u ^ (n-1)` is congruent to the unit
`n`, hence a unit, and it annihilates `u - 1`. -/
public theorem eq_one_of_pow_eq_one_of_sub_one_mem_maximalIdeal
    {A : Type u} [CommRing A] [IsLocalRing A] {u : A}
    (hu : u - 1 ∈ maximalIdeal A) {n : ℕ} (hn : IsUnit (n : A))
    (hun : u ^ n = 1) : u = 1 := by
  have hfact : (u - 1) * (∑ i ∈ Finset.range n, u ^ i) = 0 := by
    rw [mul_comm, geom_sum_mul, hun, sub_self]
  have hcof : IsUnit (∑ i ∈ Finset.range n, u ^ i) := by
    rw [← notMem_maximalIdeal]
    intro hmem
    have h := Ideal.sub_mem _ hmem
      (geomSum_sub_natCast_mem_maximalIdeal hu n)
    simp only [sub_sub_cancel] at h
    exact (notMem_maximalIdeal.mpr hn) h
  obtain ⟨v, hv⟩ := hcof
  have h0 : u - 1 = 0 := by
    have h := congrArg (· * (↑v⁻¹ : A)) hfact
    simp only [mul_assoc, ← hv, v.mul_inv, mul_one, zero_mul] at h
    exact h
  exact sub_eq_zero.mp h0

end IsLocalRing
