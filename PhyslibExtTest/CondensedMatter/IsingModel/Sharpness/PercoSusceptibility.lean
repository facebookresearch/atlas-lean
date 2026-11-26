/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.PercoSusceptibility

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.PercoSusceptibility`

* `shk_restrictedSusceptibility_le` and `shk_twoPoint_summable_of_phi_lt_one` applied to a
  witness `φ_p(S) < 1`;
* `exists_phiBeta_witness_of_lt_tildeBetaCPerco` and
  `finite_susceptibility_of_lt_tildeBetaCPerco` applied below `β̃_c^{perc}`, and the summability
  extracted from the latter.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.PercoSusceptibility

open _root_.StatMech _root_.StatMech.Sharpness _root_.StatMech.Lattice

-- The finite-volume susceptibility bound and summability from a witness.
example (d : ℕ) (p : NNReal) (hp : p ≤ 1) (S Lam : Finset (Site d))
    (hS : Percolation.origin d ∈ S) (hL : Percolation.origin d ∈ Lam)
    (hφ : Percolation.phi d p hp S < 1) :
    shk_restrictedSusceptibility p hp Lam (Percolation.origin d) ≤
        S.card / (1 - Percolation.phi d p hp S) ∧ Summable (shk_twoPointProb (d := d) p hp) :=
  ⟨shk_restrictedSusceptibility_le p hp S Lam hS hL hφ,
    shk_twoPoint_summable_of_phi_lt_one p hp S hS hφ⟩

-- A witness exists below `β̃_c^{perc}`.
example (d : ℕ) (β : ℝ) (hβ : β < tildeBetaCPerco d) :
    ∃ S, Percolation.origin d ∈ S ∧ phiBeta d β S < 1 :=
  exists_phiBeta_witness_of_lt_tildeBetaCPerco hβ

-- Finite susceptibility below `β̃_c^{perc}`.
example (d : ℕ) (β : ℝ) (hβ : β < tildeBetaCPerco d) :
    Summable (shk_twoPointProb (d := d) (bondParam β) (bondParam_le_one β)) := by
  obtain ⟨S, -, -, h, -⟩ := finite_susceptibility_of_lt_tildeBetaCPerco hβ
  exact h

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.PercoSusceptibility
