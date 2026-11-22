/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sets of conjugacy class sizes of `p`-groups (Kourovka Notebook Problem 14.77)

Kourovka Notebook, Archive of Solved Problems, Problem 14.77 (J. Sangroniz): let `p` be a prime and
`X` a finite set of powers of `p` containing `1`. Is `X` the set of all conjugacy class sizes of
some finite `p`-group?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PGroup

@[expose] public section

namespace MathlibExt.GroupTheory.PGroupConjugacyClassSizesKourovka14Problem77Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.77 (J.
Sangroniz). UnsolvedMath record UM-00701062 (`KOU-14.77`), dataset ulamai/UnsolvedMath v1.8.0.

The set of class sizes is `Set.range (fun c : ConjClasses G => Nat.card c.carrier)`.
-/

/-- **Prescribed sets of conjugacy class sizes of finite p-groups (Kourovka 14.77).** The
statement that for every prime $p$ and every finite set $X$ of natural numbers that contains $1$
and consists of powers of $p$, there is a finite $p$-group $G$ whose set of conjugacy class sizes
$\{|C| : C \text{ a conjugacy class of } G\}$ equals $X$. -/
def everyPowerSetIsClassSizeSet : Prop :=
  ∀ p : ℕ, p.Prime → ∀ X : Finset ℕ, 1 ∈ X → (∀ x ∈ X, ∃ k : ℕ, x = p ^ k) →
    ∃ (G : Type) (_ : Group G) (_ : Finite G), IsPGroup p G ∧
      Set.range (fun c : ConjClasses G => Nat.card c.carrier) = (X : Set ℕ)

/--
**Cossey–Hawkes theorem on conjugacy class sizes of p-groups.** For every prime $p$ and every
finite set $X$ of natural numbers that contains $1$ and consists of powers of $p$, there is a
finite $p$-group whose set of conjugacy class sizes is exactly $X$. This answers Kourovka
Problem 14.77 (Sangroniz) in the affirmative.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.77
(J. Sangroniz); resolution: J. Cossey and T. Hawkes, Proc. Amer. Math. Soc. 128 (2000), no. 1,
49-51, Kourovka Archive, Problem 14.77 (answer: Yes, it is).
-/
public theorem_wanted everyPowerSetIsClassSizeSet_holds : everyPowerSetIsClassSizeSet

end MathlibExt.GroupTheory.PGroupConjugacyClassSizesKourovka14Problem77Wanted
