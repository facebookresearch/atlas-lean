/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Elements of prime-power order outside a proper subgroup (Kourovka Notebook Problem 7.16)

Kourovka Notebook, Archive of Solved Problems, Problem 7.16 (R. L. Griess): if `H` is a proper
subgroup of the finite group `G`, is there always an element of prime-power order not conjugate to
an element of `H`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

namespace MathlibExt.GroupTheory.PrimePowerElementNotConjugateKourovka7Problem16Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 7.16 (R. L.
Griess). UnsolvedMath record UM-00700417 (`KOU-7.16`), dataset ulamai/UnsolvedMath v1.8.0.

Prime-power order means `IsPrimePow (orderOf g)`, a positive power of a prime (the identity lies in
`H` anyway). Equivalently, every transitive permutation group of degree at least `2` (acting on the
cosets of `H`) contains a fixed-point-free element of prime-power order, the form in which Fein,
Kantor and Schacher state the theorem.
-/

/-- Kourovka 7.16 (R. L. Griess): for every proper subgroup `H` of a finite group `G` some element
of `G` of prime-power order is not conjugate to any element of `H`. -/
def properSubgroupMissesPrimePowerClass : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G), H ≠ ⊤ →
    ∃ g : G, IsPrimePow (orderOf g) ∧ ∀ h ∈ H, ¬ IsConj g h

/--
Resolved true: the Kourovka Archive answers 7.16 "Yes, always", modulo the classification of finite
simple groups, citing Fein, Kantor and Schacher (1981): a transitive permutation group of degree at
least `2` contains a fixed-point-free element of prime-power order; applied to the action of `G` on
the cosets of `H` this is an element of prime-power order not conjugate into `H`. Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 7.16 (R. L. Griess);
resolution: B. Fein, W. M. Kantor and M. Schacher, Relative Brauer groups II, J. Reine Angew. Math.
328 (1981), 39-57, Kourovka Archive, Problem 7.16: Yes, always (mod CFSG),
https://doi.org/10.1515/crll.1981.328.39.
-/
public theorem_wanted properSubgroupMissesPrimePowerClass_holds :
    properSubgroupMissesPrimePowerClass

end MathlibExt.GroupTheory.PrimePowerElementNotConjugateKourovka7Problem16Wanted
