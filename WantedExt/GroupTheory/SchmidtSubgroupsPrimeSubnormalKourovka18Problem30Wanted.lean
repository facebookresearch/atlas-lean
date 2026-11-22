/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Groups whose Schmidt subgroups are ℙ-subnormal (Kourovka Notebook Problem 18.30)

Kourovka Notebook, Archive of Solved Problems, Problem 18.30 (A. F. Vasil'ev, T. I. Vasil'eva, V. N.
Tyutyanov): a subgroup `H` of `G` is `ℙ`-subnormal if `H = G` or there is a chain `H = H₀ ⊂ H₁ ⊂ ⋯ ⊂
Hₙ = G` with every `|Hᵢ : Hᵢ₋₁|` prime. Must a finite group be soluble if every Schmidt subgroup of
it is `ℙ`-subnormal?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Nilpotent

@[expose] public section

namespace MathlibExt.GroupTheory.SchmidtSubgroupsPrimeSubnormalKourovka18Problem30Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.30 (A. F.
Vasil'ev, T. I. Vasil'eva, V. N. Tyutyanov). UnsolvedMath record UM-00701459 (`KOU-18.30`), dataset
ulamai/UnsolvedMath v1.8.0.

A Schmidt (Shmidt) group is a finite non-nilpotent group all of whose proper subgroups are
nilpotent; a Schmidt subgroup is a subgroup that is a Schmidt group. `ℙ`-subnormality is the
reflexive-transitive closure of the relation `A ≤ B` with `|B : A|` prime, ending at `⊤`.
-/

/-- `H` is a Schmidt (Shmidt) subgroup: `H` is not nilpotent but every proper subgroup of `H` is
nilpotent. -/
def IsSchmidtSubgroup {G : Type} [Group G] (H : Subgroup G) : Prop :=
  ¬ Group.IsNilpotent H ∧ ∀ K : Subgroup G, K < H → Group.IsNilpotent K

/-- `H` is `ℙ`-subnormal in `G`: `H = G`, or there is a chain `H = H₀ < H₁ < ⋯ < Hₙ = G` in which
every index `|Hᵢ : Hᵢ₋₁|` is a prime. -/
def IsPSubnormal {G : Type} [Group G] (H : Subgroup G) : Prop :=
  Relation.ReflTransGen (fun A B : Subgroup G => A ≤ B ∧ (A.relIndex B).Prime) H ⊤

/-- Kourovka 18.30 (A. F. Vasil'ev, T. I. Vasil'eva, V. N. Tyutyanov): a finite group in which every
Schmidt subgroup is `ℙ`-subnormal is soluble. -/
def schmidtSubgroupsPSubnormalImpliesSoluble : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    (∀ H : Subgroup G, IsSchmidtSubgroup H → IsPSubnormal H) → Group.IsSolvable G

/--
Resolved true: the Kourovka Archive answers 18.30 "Yes, it must" (V. N. Tyutyanov, 2015): a finite
group all of whose Schmidt subgroups are `ℙ`-subnormal is soluble. Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.30 (A. F. Vasil'ev, T. I.
Vasil'eva, V. N. Tyutyanov); resolution: V. N. Tyutyanov, Probl. Fiz. Mat. Tekhn. 2015, no. 1 (22),
88-91 (Russian), Kourovka Archive, Problem 18.30: Yes, it must, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted schmidtSubgroupsPSubnormalImpliesSoluble_holds :
    schmidtSubgroupsPSubnormalImpliesSoluble

end MathlibExt.GroupTheory.SchmidtSubgroupsPrimeSubnormalKourovka18Problem30Wanted
