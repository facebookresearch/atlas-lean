/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.Padics.HodgeTate.FiniteExtension

/-! Tests for Hodge–Tate representations over a finite extension: for `K ≤ L` inside `ℚ̄_p` with
`L` finite over `ℚ_p`, a representation is Hodge–Tate over `K` if and only if it is Hodge–Tate
over `L`, with the same Hodge–Tate numbers; in particular over `K = ℚ_p`, and for the
cyclotomic representation `ℚ_p(1)`. -/

open Representation MathlibExt.AlgebraicGeometry.HodgeTateComparison

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

-- Hodge–Tate over `K` if and only if over `L`, with the same Hodge–Tate numbers.
example {K L : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ L) [FiniteDimensional ℚ_[p] L]
    (ρ : Representation ℚ_[p] (Galois p) V) (i : ℤ) :
    (ρ.IsHodgeTate K ↔ ρ.IsHodgeTate L) ∧ ρ.hodgeTateNumber K i = ρ.hodgeTateNumber L i :=
  ⟨isHodgeTate_iff_of_le h ρ, hodgeTateNumber_eq_of_le h ρ i⟩

-- Hodge–Tate over `ℚ_p` if and only if over a finite extension `L` of `ℚ_p`.
example (L : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] L]
    (ρ : Representation ℚ_[p] (Galois p) V) : ρ.IsHodgeTate ⊥ ↔ ρ.IsHodgeTate L :=
  isHodgeTate_iff_of_le bot_le ρ

-- `ℚ_p(1)` is Hodge–Tate over every finite extension `L` of `ℚ_p`, with `h₁ = 1` there.
example (L : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] L] :
    (cyclotomic p).IsHodgeTate L ∧ (cyclotomic p).hodgeTateNumber L 1 = 1 := by
  refine ⟨(isHodgeTate_iff_of_le bot_le _).1 (isHodgeTate_cyclotomic ⊥), ?_⟩
  rw [← hodgeTateNumber_eq_of_le bot_le, hodgeTateNumber_cyclotomic]
  simp
