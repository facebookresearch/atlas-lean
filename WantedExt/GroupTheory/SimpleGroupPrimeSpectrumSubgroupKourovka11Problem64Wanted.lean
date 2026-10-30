/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Proper subgroups with the same prime divisors as a simple group (Kourovka Notebook Problem 11.64)

Kourovka Notebook, Archive of Solved Problems, Problem 11.64 (V. S. Monakhov): are there only
finitely many finite simple groups `G`, other than alternating groups, with a proper subgroup `H`
such that `π(H) = π(G)` (`π` the set of prime divisors of the order)?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Subgroup.Simple

@[expose] public section

namespace MathlibExt.GroupTheory.SimpleGroupPrimeSpectrumSubgroupKourovka11Problem64Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.64 (V. S.
Monakhov). UnsolvedMath record UM-00700756 (`KOU-11.64`), dataset ulamai/UnsolvedMath v1.8.0.

"Finitely many" up to isomorphism is a bound on `|G|`, an equivalent form since there are finitely
many groups of each order. "Different from alternating groups" excludes every `G` isomorphic to some
`Alt(n)`. `π(X)` is `(Nat.card X).primeFactors`.
-/

/-- Kourovka 11.64 (V. S. Monakhov): only finitely many finite simple groups `G` that are not
alternating groups have a proper subgroup `H` with `π(H) = π(G)`, `π` the set of prime divisors of
the order. "Finitely many" up to isomorphism is stated as a bound on `|G|`, equivalently, since
there are finitely many groups of each order. -/
def finitelyManySimpleWithFullSpectrumSubgroup : Prop :=
  ∃ N : ℕ, ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    (∀ n : ℕ, IsEmpty (G ≃* alternatingGroup (Fin n))) →
    (∃ H : Subgroup G, H ≠ ⊤ ∧ (Nat.card H).primeFactors = (Nat.card G).primeFactors) →
    Nat.card G ≤ N

/--
Resolved false: the Kourovka Archive records (V. I. Zenkov) that the symplectic groups `G =
S_{4k}(2^s)` have proper subgroups `H ≅ Ω⁻_{4k}(2^s)` with `π(H) = π(G)`, an infinite family of
non-alternating finite simple groups. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 11.64 (V. S. Monakhov); resolution: V. I. Zenkov, letter of 10 March 1994,
Kourovka Archive, Problem 11.64: "No, there are infinitely many such groups. If `G = S_{4k}(2^s)`
and `H ≅ Ω⁻_{4k}(2^s)`, then `π(G) = π(H)`", https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted finitelyManySimpleWithFullSpectrumSubgroup_refuted :
    ¬ finitelyManySimpleWithFullSpectrumSubgroup

end MathlibExt.GroupTheory.SimpleGroupPrimeSpectrumSubgroupKourovka11Problem64Wanted
