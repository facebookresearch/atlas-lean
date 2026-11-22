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

/-- Mazur and Ulam's Problem 62 from the Scottish Book: if a group `G`
is the union of an increasing chain of subgroups `H n`, each isomorphic
to `H 1`, is `G` itself isomorphic to `H 1`? -/
def ScottishBookProblem62Claim : Prop :=
  ∀ (G : Type) [AddCommGroup G] (H : ℕ → AddSubgroup G),
    (∀ n, H n ≤ H (n + 1)) →
    (∀ n, Nonempty (↥(H n) ≃+ ↥(H 1))) →
    (⨆ n, H n) = ⊤ →
    Nonempty (G ≃+ ↥(H 1))

/--
Mazur–Ulam Problem 62 is false: the answer is no. Source: S. Mazur and
S. Ulam, Problem 62 of the Scottish Book; the typescript Ad 62 records
R. Baer's remark giving the counterexample, with `G` the group of
rational numbers and `G 1` the integers: the rationals are the union of
an increasing chain of subgroups each isomorphic to the integers (for
example the subgroups `(1 / n !) ℤ`), but the rationals are not
isomorphic to the integers.
-/
theorem_wanted mazurUlam62_refuted : ¬ ScottishBookProblem62Claim

end MathlibExt.GroupTheory.ScottishBook62Wanted
