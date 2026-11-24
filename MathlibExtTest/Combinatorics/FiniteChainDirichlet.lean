/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.FiniteChainDirichlet
import Mathlib.Data.Finite.Card

@[expose] public section

-- Consumer with the original binders.
example {ι : Type*} [Finite ι] (n : ι → ℕ) (hn : ∀ i, 1 ≤ n i) (r : ι → ℕ → ℤ) :
    ∃ (ν : ι → ℤ) (c : ι → ℕ → ℤ),
      (∀ i, n i = 1 → ν i = 0) ∧ (∀ i, c i 0 = 0) ∧ (∀ i d, n i ≤ d → c i d = 0) ∧
      ∀ i d, 1 ≤ d → d + 1 ≤ n i →
        c i (d - 1) - 2 * c i d + c i (d + 1) = -(if d = 1 then r i d - ν i else r i d) :=
  ModularCurve.ChainDirichlet.exists_depthOne_correction_dirichlet n hn r

-- Boundary consumer: a chain of length one needs no correction, and its
-- only vertex is an endpoint, so the solution vanishes there.
example (r : Unit → ℕ → ℤ) :
    ∃ (ν : Unit → ℤ) (c : Unit → ℕ → ℤ), ν Unit.unit = 0 ∧ c Unit.unit 0 = 0 ∧
      c Unit.unit 1 = 0 := by
  obtain ⟨ν, c, hν, hc0, hcout, -⟩ :=
    ModularCurve.ChainDirichlet.exists_depthOne_correction_dirichlet
      (fun _ => 1) (fun _ => Nat.le.refl) r
  exact ⟨ν, c, hν Unit.unit rfl, hc0 Unit.unit, hcout Unit.unit 1 Nat.le.refl⟩
