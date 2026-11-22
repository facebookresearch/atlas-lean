/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# An infinite group whose proper subgroups have prime order (Kourovka Notebook Problem 2.73)

Kourovka Notebook, Archive of Solved Problems, Problem 2.73 (A. I. Starostin; well-known problem):
does there exist an infinite group all of whose proper subgroups have prime order?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace MathlibExt.GroupTheory.InfiniteGroupPrimeOrderSubgroupsKourovka2Problem73Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.73 (A. I.
Starostin; well-known problem). UnsolvedMath record UM-00700143 (`KOU-2.73`), dataset
ulamai/UnsolvedMath v1.8.0.

The trivial subgroup, of order `1`, is excluded (otherwise no nontrivial group qualifies);
`Nat.card` of an infinite subgroup is `0`, which is not prime, so every proper nontrivial subgroup
is required to be finite of prime order.
-/

/-- Kourovka 2.73 (A. I. Starostin; well-known problem): there is an infinite group all of whose
proper non-trivial subgroups have prime order (the trivial subgroup, of order `1`, is excluded;
`Nat.card` of an infinite subgroup is `0`, which is not prime). -/
def infiniteGroupWithPrimeOrderSubgroupsExists : Prop :=
  ∃ (G : Type) (_ : Group G), Infinite G ∧
    ∀ H : Subgroup G, H ≠ ⊥ → H ≠ ⊤ → (Nat.card H).Prime

/--
Resolved true: the Kourovka Archive answers 2.73 "Yes, there does", citing Ol'shanskii (1982), whose
infinite groups (Tarski monsters) have all proper nontrivial subgroups of prime order. Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.73 (A. I. Starostin;
well-known problem); resolution: A. Yu. Ol'shanskii, Algebra and Logic 21 (1982), 369-418, Kourovka
Archive, Problem 2.73: Yes, there does (Ol'shanskii; Tarski monsters),
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted infiniteGroupWithPrimeOrderSubgroupsExists_holds :
    infiniteGroupWithPrimeOrderSubgroupsExists

end MathlibExt.GroupTheory.InfiniteGroupPrimeOrderSubgroupsKourovka2Problem73Wanted
