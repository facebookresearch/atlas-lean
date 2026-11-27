/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.Order.BooleanFunction.SelfDual
public import MathlibExt.Combinatorics.Enumerative.BooleanFunctionInclusionExclusion
public import MathlibExt.Combinatorics.Enumerative.UnateMonotoneBoolean

namespace MetaMathlibExt

@[expose] public section

/-- **Counting Boolean functions by their non-degenerate restrictions.** Let $P$ be a property
of Boolean functions on any number of variables that is invariant under renaming variables
along injections: for all $m, n$, every injective map $e$ from $\{1, \dots, m\}$ to
$\{1, \dots, n\}$ and every $m$-variable function $g$, the $n$-variable function
$x \mapsto g(x_{e(1)}, \dots, x_{e(m)})$ has $P$ if and only if $g$ has $P$. Write $P_n$ for the
number of $n$-variable Boolean functions with $P$ and $\mathrm{nd}\text{-}P_i$ for the number of
non-degenerate $i$-variable Boolean functions with $P$. Then for every $n \ge 0$,

$$P_n = \sum_{i=0}^{n} \binom{n}{i} \, \mathrm{nd}\text{-}P_i.$$

The invariance hypothesis cannot be dropped: if $P$ holds exactly for the four $1$-variable
functions, then $P_1 = 4$ but the right-hand side is $0 + 2 = 2$.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 1 (`jis-2025-25.3.4-prop-1`). -/
public theorem_wanted card_boolFun_eq_sum_choose_card_nondegenerate
    (P : ∀ n : ℕ, ((Fin n → Bool) → Bool) → Prop)
    (hP : ∀ (m n : ℕ) (e : Fin m ↪ Fin n) (g : (Fin m → Bool) → Bool),
      P n (fun x => g (x ∘ e)) ↔ P m g)
    (n : ℕ) :
    Nat.card {f : (Fin n → Bool) → Bool // P n f}
      = ∑ i ∈ Finset.range (n + 1),
          n.choose i * Nat.card {f : (Fin i → Bool) → Bool // IsNondegenerateBoolFun f ∧ P i f}

/-- **Unate and monotone functions have equally many NN- and NPN-classes.** For every $n$, the
number of NN-inequivalent unate $n$-variable Boolean functions equals the number of
NN-inequivalent monotone ones, and the number of NPN-inequivalent unate $n$-variable Boolean
functions equals the number of NPN-inequivalent monotone ones. Here monotone means nondecreasing
for the coordinatewise order with $0 < 1$.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 14(a) (`jis-2025-25.3.4-prop-14`). -/
public theorem_wanted boolFunClassCount_unate_eq_monotone (n : ℕ) :
    boolFunClassCount (n := n) IsBoolFunNNEquiv IsUnateBoolFun
        = boolFunClassCount (n := n) IsBoolFunNNEquiv Monotone ∧
      boolFunClassCount (n := n) IsBoolFunNPNEquiv IsUnateBoolFun
        = boolFunClassCount (n := n) IsBoolFunNPNEquiv Monotone

end

end MetaMathlibExt
