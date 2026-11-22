/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.ScottishBook95Wanted

/--
The additive group of real numbers embeds into the group `S_∞` of all
permutations of the natural numbers. Source: J. Schreier and S. Ulam,
Problem 95 of the Scottish Book; affirmative answer of Schreier and Ulam,
November 1935, recorded in the typescript addendum Ad 95. `Multiplicative ℝ`
is the additive group `ℝ` viewed multiplicatively, so a monoid homomorphism
out of it is an additive homomorphism out of `ℝ`.
-/
theorem_wanted real_addGroup_embeds_in_perm_nat :
    ∃ f : Multiplicative ℝ →* Equiv.Perm ℕ, Function.Injective f

end MathlibExt.GroupTheory.ScottishBook95Wanted
