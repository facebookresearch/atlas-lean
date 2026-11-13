/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Lennox's index condition and nilpotency (Kourovka Notebook Problem 8.32)

Kourovka Notebook, Archive of Solved Problems, Problem 8.32 (J. C. Lennox): suppose `G` is a
finitely generated group such that, for any set `π` of primes and any subgroup `H` of `G`, if `G /
⟨H^G⟩` is a finite `π`-group then `|G : H|` is a finite `π`-number. Is `G` nilpotent?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Nilpotent
public import WantedExt.GroupTheory.HallSubgroupPrimeSetIntersectionKourovka18Problem38Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.LennoxPiIndexNilpotentKourovka8Problem32Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 8.32 (J. C.
Lennox). UnsolvedMath record UM-00700484 (`KOU-8.32`), dataset ulamai/UnsolvedMath v1.8.0.

`π` ranges over all sets of natural numbers (only primes matter). A `π`-number is `IsPiNumber` from
`WantedExt/GroupTheory/HallSubgroupPrimeSetIntersectionKourovka18Problem38Wanted.lean` (every prime
divisor lies in `π`); a finite `π`-group is a finite group whose order is one; `|G : H|` is
`Subgroup.index`, which is `0` for infinite index, so a finite `π`-number index is `index ≠ 0` and
`IsPiNumber`; `⟨H^G⟩` is the normal closure. The empty `π` is allowed, as printed.
-/

open MathlibExt.GroupTheory.HallSubgroupPrimeSetIntersectionKourovka18Problem38Wanted

/-- Kourovka 8.32 (J. C. Lennox): a finitely generated group `G` such that, for every set `π` of
primes and every subgroup `M`, `|G : M|` is a finite `π`-number whenever `G / M^G` is a finite
`π`-group (`M^G` the normal closure of `M`), is nilpotent. -/
def lennoxConditionImpliesNilpotent : Prop :=
  ∀ (G : Type) [Group G], Group.FG G →
    (∀ (π : Set ℕ) (M : Subgroup G), Finite (G ⧸ Subgroup.normalClosure (M : Set G)) →
      IsPiNumber π (Nat.card (G ⧸ Subgroup.normalClosure (M : Set G))) →
        M.index ≠ 0 ∧ IsPiNumber π M.index) →
    Group.IsNilpotent G

/--
Resolved false: the Kourovka Archive answers 8.32 "Not always", citing Obraztsov (1996). The
Corollary to his Theorem G (p. 275, an application noted by H. Smith and J. Wiegold) gives a
`2`-generator group `G` with a normal simple infinite subgroup `L` and `G / L ≅ ℤ²` in which every
subgroup `M` with `G / M^G` finite is normal; Obraztsov notes that a negative answer to Lennox's
question follows immediately. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 8.32 (J. C. Lennox); resolution: V. N. Obraztsov, A new embedding scheme for
groups and some applications, J. Austral. Math. Soc. Ser. A 61 (1996), 267-288, Kourovka Archive,
Problem 8.32: Not always; paper, Corollary to Theorem G (p. 275): a 2-generator group G with a
normal simple infinite subgroup L, G / L free abelian of rank 2, in which every subgroup M with G /
M^G finite is normal, https://doi.org/10.1017/S1446788700000252.
-/
public theorem_wanted lennoxConditionImpliesNilpotent_refuted : ¬ lennoxConditionImpliesNilpotent

end MathlibExt.GroupTheory.LennoxPiIndexNilpotentKourovka8Problem32Wanted
