/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Derived length of `p`-groups with a 2-generator condition (Kourovka Notebook Problem 17.46)

Kourovka Notebook, Archive of Solved Problems, Problem 17.46 (B. M. Veretennikov): let `G` be a
finite `p`-group in which every 2-generator subgroup has cyclic derived subgroup. Is the derived
length of `G` bounded? (If `p ≠ 2`, then `G⁽²⁾ = 1` (J. Alperin).)
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Solvable

@[expose] public section

namespace MathlibExt.GroupTheory.TwoGeneratorCyclicDerivedLengthKourovka17Problem46Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.46 (B. M.
Veretennikov). UnsolvedMath record UM-00701348 (`KOU-17.46`), dataset ulamai/UnsolvedMath v1.8.0.

The target is the bound of the resolution: derived length at most `4`, that is `G⁽⁴⁾ = 1`
(`derivedSeries G 4 = ⊥`), for every prime `p`. The derived subgroup of `⟨x, y⟩` is the commutator
`⁅⟨x, y⟩, ⟨x, y⟩⁆` of subgroups.
-/

/-- **Kourovka Problem 17.46, with the bound $4$.** The statement that for every prime $p$ and
every finite $p$-group $G$ such that for all $x, y \in G$ the derived subgroup $[H, H]$ of
$H = \langle x, y \rangle$ is cyclic, $G$ has derived length at most $4$, that is, the fourth
term $G^{(4)}$ of the derived series of $G$ is trivial. -/
def twoGeneratorCyclicDerivedLengthAtMostFour : Prop :=
  ∀ (p : ℕ) (G : Type) [Group G] [Finite G], p.Prime → IsPGroup p G →
    (∀ x y : G, IsCyclic ↥⁅Subgroup.closure {x, y}, Subgroup.closure {x, y}⁆) →
      derivedSeries G 4 = ⊥

/--
**Derived length of $p$-groups whose $2$-generator subgroups have cyclic derived subgroups
(Kourovka Problem 17.46).** Let $p$ be a prime and $G$ a finite $p$-group such that for all
$x, y \in G$ the derived subgroup $[H, H]$ of $H = \langle x, y \rangle$ is cyclic. Then $G$ has
derived length at most $4$, that is, the fourth term $G^{(4)}$ of the derived series of $G$ is
trivial.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.46
(B. M. Veretennikov); resolution: B. Wilkens, J. Group Theory 17 (2014), 151-174, Kourovka Archive,
Problem 17.46 (Yes, it is at most 4).
-/
public theorem_wanted twoGeneratorCyclicDerivedLengthAtMostFour_holds :
    twoGeneratorCyclicDerivedLengthAtMostFour

end MathlibExt.GroupTheory.TwoGeneratorCyclicDerivedLengthKourovka17Problem46Wanted
