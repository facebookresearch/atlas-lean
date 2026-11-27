/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.FiniteRangePerco

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.FiniteRangePerco`

* the zero kernel is a `FiniteRangeKernel` (the structure is inhabited), and its percolation
  measure is translation invariant (`frpMeasure_translationInvariant`);
* `frp_subcritical_decay` applied to a witness `φ_β(S) < 1`;
* `frp_subcritical_decay_of_lt_tildeBetaC` applied below `β̃_c(K)`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.FiniteRangePerco

open _root_.StatMech _root_.StatMech.Sharpness _root_.StatMech.Lattice

/-- The zero kernel on `ℤ^d`, of range `0`. -/
def zeroKernel (d : ℕ) : FiniteRangeKernel d where
  coupling _ := 0
  nonneg _ := le_rfl
  zero := rfl
  symmetric _ := rfl
  range := 0
  support _ h := absurd rfl h

-- The percolation measure of the zero kernel is translation invariant.
example (β : ℝ) := frpMeasure_translationInvariant (zeroKernel 2) β

-- Exponential decay from a witness.
example (d : ℕ) (K : FiniteRangeKernel d) (β : ℝ) (S : Finset (Site d)) (h0 : 0 ∈ S)
    (hφ : frpPhi K β S < 1) (L : ℕ) (hL : 1 ≤ L) (hK : K.range ≤ L)
    (hS : (S : Set (Site d)) ⊆ box d (L - K.range)) :
    ∃ c > 0, ∃ C > 0, ∀ n : ℕ, frpCrossProb K β n ≤ C * Real.exp (-c * n) :=
  frp_subcritical_decay K β S h0 hφ L hL hK hS

-- Exponential decay below `β̃_c(K)`.
example (d : ℕ) (K : FiniteRangeKernel d) (β : ℝ) (hβ : β < frpTildeBetaC K) :
    ∃ c > 0, ∃ C > 0, ∀ n : ℕ, frpCrossProb K β n ≤ C * Real.exp (-c * n) :=
  frp_subcritical_decay_of_lt_tildeBetaC K hβ

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.FiniteRangePerco
