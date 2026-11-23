/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Peierls
public import PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.PcUpperPeierls

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Peierls`

* `flipConfig` is an involution and negates spins (`spin_flipConfig`), and leaves bonds unchanged
  (`bond_flipConfig`);
* `fvMagOrigin_minus_eq_neg` in `Λ_1 ⊆ ℤ²` at `β = 1`;
* `peierls_lro_criterion` in `d = 2` with its hypothesis `hPeierls` discharged for every box size at
  the inverse temperature given by `pup_exists_uniform_fvMagnetization`
  (`FKRepresentation.PcUpperPeierls`): the plus and minus measures differ in every `Λ_n`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Peierls

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Ising _root_.StatMech.IsingFK

-- Flipping twice is the identity.
example (s : ConfigSpace (Site 2)) : flipConfig (flipConfig s) = s := by simp

-- Flipping negates the spin at the origin.
example (s : ConfigSpace (Site 2)) : spin (flipConfig s) (origin 2) = -spin s (origin 2) :=
  spin_flipConfig s _

-- Flipping the all-plus configuration gives spin `-1` everywhere.
example (x : Site 2) : spin (flipConfig (fun _ => true)) x = -1 := by simp [spin]

-- Flipping leaves bond variables unchanged.
example (s : ConfigSpace (Site 2)) (e : Sym2 (Site 2)) : bond (flipConfig s) e = bond s e :=
  bond_flipConfig s e

-- The minus-boundary magnetization is the negative of the plus-boundary one.
example : fvMagOrigin (minusField 2) 1 (bondFinsetTouch 2 1) 1 0 =
    -fvMagOrigin (plusField 2) 1 (bondFinsetTouch 2 1) 1 0 :=
  fvMagOrigin_minus_eq_neg 1 1

-- The long-range-order criterion with its hypothesis discharged: for some `β > 0` the plus and
-- minus measures differ in every box `Λ_n ⊆ ℤ²`.
example : ∃ β > 0, ∀ n, plusMeasure 2 n β 0 ≠ minusMeasure 2 n β 0 := by
  obtain ⟨β, hβ, c, hc, hbound⟩ := pup_exists_uniform_fvMagnetization
  refine ⟨β, hβ, fun n => peierls_lro_criterion le_rfl n β ?_⟩
  rw [fvMagOrigin_plus_eq_integral]
  exact lt_of_lt_of_le hc (hbound n)

end PhyslibExtTest.CondensedMatter.IsingModel.Peierls
