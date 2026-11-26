/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_LatticeTreeOrbital.lean`
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
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.AlgebraicGeometry.FormalOmega.LatticeNeighbour
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

open scoped Matrix
open LT.LatticeTree

universe u

/-- Consumer with the original binders: membership in the neighbour through `(c, d)`. -/
private theorem exactSource {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
    {ϖ c d : R} {v : Fin 2 → K} :
    v ∈ interLattice R K ϖ c d ↔
      (∀ i, IsLocalization.IsInteger R (v i)) ∧
        ∃ w : K, IsLocalization.IsInteger R w ∧
          algebraMap R K d * v 0 - algebraMap R K c * v 1 = algebraMap R K ϖ * w :=
  mem_interLattice

/-- `IsLocalization.isInteger_neg` and `IsLocalization.isInteger_sub` hold over any commutative
ring, not only over fields. -/
example {S : Type u} [CommRing S] [Algebra ℤ S] {a b : S} (ha : IsLocalization.IsInteger ℤ a)
    (hb : IsLocalization.IsInteger ℤ b) :
    IsLocalization.IsInteger ℤ (a - b) ∧ IsLocalization.IsInteger ℤ (-a) :=
  ⟨IsLocalization.isInteger_sub ha hb, IsLocalization.isInteger_neg ha⟩

/-- Higher-universe consumer: the neighbours are injectively parametrized. -/
example {R : Type (u + 1)} [CommRing R] {K : Type (u + 1)} [Field K] [Algebra R K]
    [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) :
    Function.Injective (neighborOfOption R K ϖ) :=
  neighborOfOption_injective hϖ

/-- Over `𝔽₂`, the plane `𝔽₂²` has `3` lines. -/
example : Nat.card {W : Submodule (ZMod 2) (Fin 2 → ZMod 2) // W ≠ ⊥ ∧ W ≠ ⊤} = 3 := by
  rw [Submodule.card_ne_bot_ne_top_of_finrank_two (by simp), Nat.card_zmod]

example : interLattice ℤ_[2] ℚ_[2] 2 1 0 ≠ interLattice ℤ_[2] ℚ_[2] 2 1 1 := by
  intro h
  have hd := dvd_of_interLattice_eq h
  rw [mul_one, one_mul, sub_zero] at hd
  exact (PadicInt.irreducible_p (p := 2)).not_isUnit (isUnit_of_dvd_one hd)

example : interLattice ℤ_[2] ℚ_[2] 2 0 1 ≠ interLattice ℤ_[2] ℚ_[2] 2 1 0 := by
  intro h
  have hd := dvd_of_interLattice_eq h
  rw [mul_zero, one_mul, zero_sub] at hd
  exact (PadicInt.irreducible_p (p := 2)).not_isUnit
    (isUnit_of_dvd_one (dvd_neg.mp hd))

example : interLattice ℤ_[2] ℚ_[2] 2 1 0 = interLattice ℤ_[2] ℚ_[2] 2 1 2 :=
  interLattice_one_eq_of_dvd_sub ⟨-1, by ring⟩

example (x : Option (ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2])})) :
    neighborOfOption ℤ_[2] ℚ_[2] 2 x < stdLattice ℤ_[2] ℚ_[2] :=
  (neighborOfOption_mem_interval PadicInt.irreducible_p x).2

/-- Boundary: for `(c, d)` divisible by `ϖ` the neighbour construction degenerates to `R²`. -/
example {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K] (ϖ : R) :
    interLattice R K ϖ 0 0 = stdLattice R K :=
  interLattice_zero_zero ϖ
