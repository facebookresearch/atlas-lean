/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Frobenius's conjecture on the solutions of x ^ n = 1 (Open Problem Garden 732)

Open Problem Garden, Subgroup formed by elements of order dividing n (F. G. Frobenius): if `G` is a
finite group, `n` a positive integer dividing `|G|`, and `G` has exactly `n` solutions of `x ^ n =
1`, do these solutions form a subgroup of `G`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace MathlibExt.GroupTheory.FrobeniusSolutionsSubgroupOpenGardenProblem732Wanted

/-!
Source: Open Problem Garden, Subgroup formed by elements of order dividing n (node 732; F. G.
Frobenius), http://www.openproblemgarden.org/op/subgroup_formed_by_elements_of_order_dividing_n.
UnsolvedMath record UM-00003330 (`OPG-732`), dataset ulamai/UnsolvedMath v1.8.0.

`G` is a finite group (`Finite G`, order `Nat.card G`); the solution set is `{x | x ^ n = 1}` and
"form a subgroup" means that this set is the carrier of a subgroup of `G`. Such a subgroup is
automatically characteristic, as the source and Iiyori-Yamaki remark.
-/

/-- Frobenius's conjecture: if `n` is a positive integer dividing the order of a finite group `G`
and `x ^ n = 1` has exactly `n` solutions in `G`, then these solutions form a subgroup of `G`. -/
def frobeniusSolutionsSubgroup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n : ℕ), 0 < n → n ∣ Nat.card G →
    Nat.card {x : G // x ^ n = 1} = n → ∃ H : Subgroup G, (H : Set G) = {x | x ^ n = 1}

/--
Resolved true: Iiyori and Yamaki announced, with the proof via the classification of finite simple
groups completed in their J. Algebra papers, that Frobenius's conjecture holds: if `n ∣ |G|` and `x
^ n = 1` has exactly `n` solutions, they form a (characteristic) subgroup. Source: Open Problem
Garden, Subgroup formed by elements of order dividing n (node 732; F. G. Frobenius),
http://www.openproblemgarden.org/op/subgroup_formed_by_elements_of_order_dividing_n; resolution: N.
Iiyori and H. Yamaki, On a conjecture of Frobenius, Bull. Amer. Math. Soc. (N.S.) 25 (1991),
413-416, doi:10.1090/S0273-0979-1991-16084-2, p. 413: 'Frobenius conjecture. If k = 1, then the e
elements of L_e(G) form a characteristic subgroup of G' and 'Theorem. The conjecture of Frobenius is
always true', proved via the classification of finite simple groups (details in N. Iiyori and H.
Yamaki, J. Algebra 145 (1992), 329-332, and N. Iiyori, J. Algebra 154 (1993), 188-214),
https://www.ams.org/journals/bull/1991-25-02/S0273-0979-1991-16084-2/.
-/
public theorem_wanted frobeniusSolutionsSubgroup_holds : frobeniusSolutionsSubgroup

end MathlibExt.GroupTheory.FrobeniusSolutionsSubgroupOpenGardenProblem732Wanted
