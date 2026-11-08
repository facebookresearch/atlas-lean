/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.PowerSeries.Christol

-- Constant zero sequence into `Fin 2`: singleton kernel, hence `2`-automatic.
example : MetaMathlibExt.IsKAutomaticSequence 2 (fun _ : ℕ => (0 : Fin 2)) := by
  rw [← MetaMathlibExt.isKAutomatic_iff_isKAutomaticSequence]
  refine ⟨le_refl 2, ?_⟩
  rw [Set.finite_coe_iff]
  apply Set.Finite.subset (Set.finite_singleton (fun _ : ℕ => (0 : Fin 2)))
  intro b hb
  obtain ⟨e, r, _, rfl⟩ := hb
  rfl

-- Christol's theorem over `ZMod 2`: algebraicity iff `2`-automaticity.
example (f : PowerSeries (ZMod 2)) [Fact (Nat.Prime 2)] :
    IsAlgebraic (Polynomial (ZMod 2)) f ↔
      MetaMathlibExt.IsKAutomaticSequence 2 (fun n => PowerSeries.coeff n f) :=
  MetaMathlibExt.christol_theorem_isKAutomaticSequence (ZMod 2) 2 2 1
    Nat.prime_two (by simp) (pow_one 2).symm zero_lt_one f
