/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.ClosedCofinitaryLocallyCompact
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Order.Interval.Set.Infinite

open MathlibExt.GroupTheory.ClosedCofinitaryLocallyCompactKourovka13Problem28Wanted

-- Extract a counterexample with both topologies specified at their uses.
example : ∃ (Ω : Type) (_ : Infinite Ω) (G : Subgroup (Equiv.Perm Ω)),
    IsCofinitary G ∧
    @IsClosed _ (Equiv.Perm.pointwiseTopology (α := Ω)) (G : Set (Equiv.Perm Ω)) ∧
    ¬ @LocallyCompactSpace G
      (TopologicalSpace.induced ((↑) : G → Equiv.Perm Ω) Equiv.Perm.pointwiseTopology) := by
  by_contra! h
  apply closedCofinitaryLocallyCompact_refuted
  intro Ω hinf G hcof hclosed
  exact h Ω hinf G hcof hclosed

-- The transposition of zero and one fixes the infinite tail of the natural numbers.
example : ¬ IsCofinitary (⊤ : Subgroup (Equiv.Perm ℕ)) := by
  intro h
  have hne : Equiv.swap 0 1 ≠ (1 : Equiv.Perm ℕ) := by
    intro he
    simpa using DFunLike.congr_fun he 0
  have hfin := h (Equiv.swap 0 1) (Subgroup.mem_top _) hne
  apply (Set.Ioi_infinite (1 : ℕ)) (hfin.subset ?_)
  intro n hn
  change 1 < n at hn
  exact Equiv.swap_apply_of_ne_of_ne (Nat.ne_zero_of_lt hn) hn.ne'
