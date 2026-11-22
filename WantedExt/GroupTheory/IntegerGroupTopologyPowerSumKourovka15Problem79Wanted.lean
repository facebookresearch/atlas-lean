/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A Hausdorff group topology on the integers with `2ⁿ + 3ⁿ → 0` (Kourovka Notebook Problem 15.79)

Kourovka Notebook, Archive of Solved Problems, Problem 15.79 (I. V. Protasov): does there exist a
Hausdorff group topology on `ℤ` such that the sequence `2ⁿ + 3ⁿ` converges to zero?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

namespace MathlibExt.GroupTheory.IntegerGroupTopologyPowerSumKourovka15Problem79Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 15.79 (I. V.
Protasov). UnsolvedMath record UM-00701167 (`KOU-15.79`), dataset ulamai/UnsolvedMath v1.8.0.

A group topology on `(ℤ, +)` is a topology making it a topological additive group
(`IsTopologicalAddGroup`); Hausdorff is `T2Space`; the sequence is indexed by `n ∈ ℕ`.
-/

/-- Kourovka 15.79 (I. V. Protasov): there is a Hausdorff group topology on `ℤ` in which
`2ⁿ + 3ⁿ → 0`. -/
def integerGroupTopologyPowSumTendstoZero : Prop :=
  ∃ t : TopologicalSpace ℤ, letI := t; IsTopologicalAddGroup ℤ ∧ T2Space ℤ ∧
    Filter.Tendsto (fun n : ℕ => (2 : ℤ) ^ n + 3 ^ n) Filter.atTop (nhds 0)

/--
Resolved true: the Kourovka Archive answers 15.79 "Yes, there does", as follows from Theorem 3 of
Ruzsa; another solution is due to Skresanov. Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 15.79 (I. V. Protasov); resolution: I. Z. Ruzsa, in: Proc. Conf.
Number Theory (Budapest, 1987), Vol. I, Colloq. Math. Soc. János Bolyai 51, North-Holland,
Amsterdam, 1990, 473-504; S. V. Skresanov, Group topologies on integers and S-unit equations,
Siberian Math. J. 61 (2020), no. 3, 542-544, arXiv:1911.11963, Ruzsa, Theorem 3, as applied in the
Kourovka Archive, Problem 15.79 (answer: Yes, there does); another solution by Skresanov, abstract
(for a finite set of primes S, a Hausdorff group topology on ℤ in which every growing sequence of
S-integers tends to 0; as a corollary, 2ⁿ + 3ⁿ tends to 0 in a Hausdorff group topology),
https://arxiv.org/abs/1911.11963.
-/
public theorem_wanted integerGroupTopologyPowSumTendstoZero_holds :
    integerGroupTopologyPowSumTendstoZero

end MathlibExt.GroupTheory.IntegerGroupTopologyPowerSumKourovka15Problem79Wanted
