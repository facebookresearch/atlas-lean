/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.PcUpperPeierls

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.PcUpperPeierls`

* `pup_exists_positive_magnetization` (Peierls' theorem in `d = 2`): the spontaneous magnetization
  lies in `(0, 1]` for some `β > 0`, so in particular `m*(β) ≠ -m*(β)`;
* `pup_exists_uniform_fvMagnetization`: the finite-volume magnetizations at that `β` are bounded
  below uniformly in `n`, so in particular `⟨σ_0⟩⁺_0 > 0`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.FKRepresentation.PcUpperPeierls

open _root_.StatMech _root_.StatMech.IsingFK _root_.StatMech.Ising

-- Peierls' theorem: for some `β > 0` the magnetization lies in `(0, 1]`.
example : ∃ β > 0, 0 < magnetization 2 β ∧ magnetization 2 β ≤ 1 := by
  obtain ⟨β, hβ, hm⟩ := pup_exists_positive_magnetization
  exact ⟨β, hβ, hm, (abs_le.mp (abs_magnetization_le_one 2 β)).2⟩

-- Peierls' theorem gives a nonzero magnetization, so `m* ≠ -m*`.
example : ∃ β > 0, magnetization 2 β ≠ -magnetization 2 β := by
  obtain ⟨β, hβ, hm⟩ := pup_exists_positive_magnetization
  exact ⟨β, hβ, by intro h; linarith⟩

-- The finite-volume bound is uniform: in particular the box `Λ_0` has positive magnetization.
example : ∃ β > 0, 0 < fvMagnetization 2 β 0 := by
  obtain ⟨β, hβ, c, hc, hbound⟩ := pup_exists_uniform_fvMagnetization
  exact ⟨β, hβ, lt_of_lt_of_le hc (hbound 0)⟩

end PhyslibExtTest.CondensedMatter.IsingModel.FKRepresentation.PcUpperPeierls
