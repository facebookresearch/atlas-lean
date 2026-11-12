/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algorithms.UniversalHashing

@[expose] public section

/-- Boundary check: the theorem instantiates for the one-key,
one-bucket case with the identity hash family. -/
example (h : Fin 1 → Fin 1 → Fin 1) :
    (∑ hh : Fin 1, ((Finset.univ.filter
      (fun y => h hh y = h hh 0)).card : ℝ)) ≤
    (Fintype.card (Fin 1) : ℝ) * (1 + (Fintype.card (Fin 1) - 1 : ℝ) / ((1 : ℕ) : ℝ)) := by
  have huniv : ∀ x y : Fin 1, x ≠ y →
      ((Finset.univ.filter (fun hh => h hh x = h hh y)).card : ℝ) ≤
        (Fintype.card (Fin 1) : ℝ) / ((1 : ℕ) : ℝ) := by
    intro x y hxy
    exact absurd (Fin.eq_zero x ▸ Fin.eq_zero y ▸ rfl) hxy
  exact expected_chain_length 1 h huniv 0
