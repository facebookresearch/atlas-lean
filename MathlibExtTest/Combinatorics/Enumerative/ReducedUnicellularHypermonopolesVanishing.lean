/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.ReducedUnicellularHypermonopolesVanishing

open MetaMathlibExt

-- Five points can support two fixed-point-free cycles, but the odd difference excludes them.
example :
    Fintype.card {α : Equiv.Perm (Fin 5) //
      cycleQuotientCount (α⁻¹ * finRotate 5) = 1 ∧ (∀ i, α i ≠ i) ∧
        cycleQuotientCount α = 2} = 0 :=
  reduced_unicellular_hypermonopoles_finRotate_vanishing.1 5 2 (by decide)

-- The empty permutation has no face cycle, despite having no fixed points.
example :
    Fintype.card {α : Equiv.Perm (Fin 0) //
      cycleQuotientCount (α⁻¹ * finRotate 0) = 1 ∧ (∀ i, α i ≠ i) ∧
        cycleQuotientCount α = 0} = 0 :=
  reduced_unicellular_hypermonopoles_finRotate_vanishing.2.2 0 (by decide) 0 (by decide)

example :
    Fintype.card {α : Equiv.Perm (Fin 2) //
      cycleQuotientCount (α⁻¹ * finRotate 2) = 1 ∧ (∀ i, α i ≠ i) ∧
        cycleQuotientCount α = 1} = 0 :=
  reduced_unicellular_hypermonopoles_finRotate_vanishing.2.2 2 (by decide) 1 (by decide)

-- The first positive count has exactly one hyperedge cycle.
example :
    0 < Fintype.card {α : Equiv.Perm (Fin 3) //
      cycleQuotientCount (α⁻¹ * finRotate 3) = 1 ∧ (∀ i, α i ≠ i) ∧
        cycleQuotientCount α = 1} := by
  obtain ⟨k, hk, hpos⟩ := reduced_unicellular_hypermonopoles_finRotate_vanishing.2.1
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact (Nat.ne_of_gt hpos)
      (reduced_unicellular_hypermonopoles_finRotate_vanishing.1 3 0 (by decide))
  have : k = 1 := by omega
  simpa only [this] using hpos
