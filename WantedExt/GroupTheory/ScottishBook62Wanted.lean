/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.ScottishBook62Wanted

/-- **Claim of Scottish Book Problem 62.** The claim that for every abelian group $G$ and
every sequence of subgroups $H_0 \le H_1 \le H_2 \le \cdots$ of $G$ whose union is $G$ and
each of which is isomorphic to $H_1$, the group $G$ is itself isomorphic to $H_1$.

The problem is posed for groups; the claim here is restricted to abelian groups, which loses
nothing for its refutation since Baer's counterexample is abelian. -/
def ScottishBookProblem62Claim : Prop :=
  ∀ (G : Type) [AddCommGroup G] (H : ℕ → AddSubgroup G),
    (∀ n, H n ≤ H (n + 1)) →
    (∀ n, Nonempty (↥(H n) ≃+ ↥(H 1))) →
    (⨆ n, H n) = ⊤ →
    Nonempty (G ≃+ ↥(H 1))

/--
**Refutation of Scottish Book Problem 62.** The claim of Scottish Book Problem 62 is false:
there are an abelian group $G$ and subgroups $H_0 \le H_1 \le H_2 \le \cdots$ of $G$ whose
union is $G$, each isomorphic to $H_1$, such that $G$ is not isomorphic to $H_1$.

R. Baer's counterexample is $G = \mathbb{Q}$ with $H_n = \frac{1}{n!}\mathbb{Z}$: each $H_n$
is isomorphic to $\mathbb{Z}$ and their union is $\mathbb{Q}$, but $\mathbb{Q}$ is not
isomorphic to $\mathbb{Z}$.

Source: S. Mazur and
S. Ulam, Problem 62 of the Scottish Book; the typescript Ad 62 records
R. Baer's remark giving the counterexample, with `G` the group of
rational numbers and `G 1` the integers: the rationals are the union of
an increasing chain of subgroups each isomorphic to the integers (for
example the subgroups `(1 / n !) ℤ`), but the rationals are not
isomorphic to the integers.
-/
theorem_wanted mazurUlam62_refuted : ¬ ScottishBookProblem62Claim

end MathlibExt.GroupTheory.ScottishBook62Wanted
