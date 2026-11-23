/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 939, finiteness question
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Basic
public import MathlibExt.NumberTheory.KFull
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosProblem939Question2Wanted

/-! Source record `UM-00002394-Q002`. -/

/-- A finite set of naturals is collectively coprime when its gcd is one. -/
@[reducible] def IsCoprime (S : Finset ℕ) : Prop :=
  S.gcd id = 1

/-- Sets of `r - 2` distinct positive, collectively coprime, `r`-powerful numbers whose sum is
itself `r`-powerful (the same set as `ErdosProblem939.Erdos939Sums`). -/
def Erdos939Sums (r : ℕ) :=
  {S : Finset ℕ | S.card = r - 2 ∧ IsCoprime S ∧ Nat.IsKFull r (∑ s ∈ S, s) ∧
    ∀ s ∈ S, 0 < s ∧ Nat.IsKFull r s}

/-- Are there at most finitely many solutions for each fixed `r ≥ 4`? -/
def conjecture : Prop :=
  ∀ r : ℕ, 4 ≤ r →
    (Erdos939Sums r).Finite

-- Carried source audit `UM-00002394-Q002` (see the Moved/ record).

/--
Resolved false: The proposed finiteness for every r ≥ 4 is false: for every r ≥ 6 there are
infinitely many solutions. Source: Liam Price, comment recording an infinite construction for
every r ≥ 6, https://www.erdosproblems.com/forum/thread/939#post-6640; T. F. Bloom, Erdős
Problem #939, erdosproblems.com, https://www.erdosproblems.com/939. Moved from
`OpenConjectures/NumberTheory/ErdosProblem939Question2`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.NumberTheory.ErdosProblem939Question2Wanted
