/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Generating sets of equal orders in p-groups (Kourovka Notebook Problem 11.6)

Kourovka Notebook, Archive of Solved Problems, Problem 11.6 (C. Bagiński): let `p` be an odd prime.
Does every finite `p`-group have a set of generators of equal orders?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PGroup

@[expose] public section

namespace MathlibExt.GroupTheory.PGroupEqualOrderGeneratorsKourovka11Problem6Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.6 (C.
Bagiński). UnsolvedMath record UM-00700699 (`KOU-11.6`), dataset ulamai/UnsolvedMath v1.8.0.

The prime is universally quantified over odd primes, so the refutation asserts a counterexample for
some odd prime. A generating set is any subset `S` with `closure S = ⊤` whose elements all have the
same order.
-/

/-- Kourovka 11.6 (C. Bagiński): for every odd prime `p`, every finite `p`-group has a generating
set all of whose elements have the same order. -/
def pGroupEqualOrderGenerators : Prop :=
  ∀ p : ℕ, p.Prime → Odd p → ∀ (G : Type) [Group G] [Finite G], IsPGroup p G →
    ∃ S : Set G, Subgroup.closure S = ⊤ ∧ ∃ m : ℕ, ∀ x ∈ S, orderOf x = m

/--
Resolved false: the Kourovka Archive answers 11.6 "No, it is not true" (O'Brien, Scoppola and
Vaughan-Lee): for odd primes there are finite `p`-groups with no generating set of elements of equal
order. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.6
(C. Bagiński); resolution: E. A. O'Brien, C. M. Scoppola and M. R. Vaughan-Lee, Proc. Amer. Math.
Soc. 134, no. 12 (2006), 3457-3464, Kourovka Archive, Problem 11.6: "No, it is not true",
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted pGroupEqualOrderGenerators_refuted : ¬ pGroupEqualOrderGenerators

end MathlibExt.GroupTheory.PGroupEqualOrderGeneratorsKourovka11Problem6Wanted
