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

/-- **Unate versus monotone Boolean function counts.** For $n \ge 0$, write $U_n$ and $M_n$ for
the numbers of unate and of monotone $n$-variable Boolean functions, $BU_n$ and $BM_n$ for the
numbers of those that are moreover balanced, that is, twice their weight equals $2^n$, and write
the prefix $\mathrm{nd}\text{-}$ for the same counts restricted to non-degenerate functions.
Then $\mathrm{nd}\text{-}U_n = 2^n \, \mathrm{nd}\text{-}M_n$,
$\mathrm{nd}\text{-}BU_n = 2^n \, \mathrm{nd}\text{-}BM_n$, $U_n \le 2^n M_n$ and
$BU_n \le 2^n BM_n$.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 3 (`jis-2025-25.3.4-prop-3`). -/
public theorem_wanted card_unate_boolFun_relations (n : ℕ) :
    Nat.card {f : (Fin n → Bool) → Bool // IsNondegenerateBoolFun f ∧ IsUnateBoolFun f}
        = 2 ^ n * Nat.card {f : (Fin n → Bool) → Bool //
            IsNondegenerateBoolFun f ∧ Monotone f} ∧
      Nat.card {f : (Fin n → Bool) → Bool //
          IsNondegenerateBoolFun f ∧ IsUnateBoolFun f ∧ 2 * boolFunWeight f = 2 ^ n}
        = 2 ^ n * Nat.card {f : (Fin n → Bool) → Bool //
            IsNondegenerateBoolFun f ∧ Monotone f ∧ 2 * boolFunWeight f = 2 ^ n} ∧
      Nat.card {f : (Fin n → Bool) → Bool // IsUnateBoolFun f}
        ≤ 2 ^ n * Nat.card {f : (Fin n → Bool) → Bool // Monotone f} ∧
      Nat.card {f : (Fin n → Bool) → Bool // IsUnateBoolFun f ∧ 2 * boolFunWeight f = 2 ^ n}
        ≤ 2 ^ n * Nat.card {f : (Fin n → Bool) → Bool //
            Monotone f ∧ 2 * boolFunWeight f = 2 ^ n}

/-- **Permutation classes counted by non-degenerate ones.** Let $(P_n)_{n \ge 0}$ be a family of
properties, $P_n$ a property of $n$-variable Boolean functions, that is invariant under renaming
variables: for all $m$ and $n$, every injection $e$ from $\{1, \dots, m\}$ to $\{1, \dots, n\}$
and every $m$-variable function $g$, the $n$-variable function $x \mapsto g(x \circ e)$ has $P_n$
if and only if $g$ has $P_m$. Write $[P]_n$ for the number of classes of $n$-variable functions
with $P_n$ under permutation of the variables, and $\mathrm{nd}[P]_n$ for the same count over the
non-degenerate $n$-variable functions with $P_n$. Then for every $n$,
$$[P]_n = \sum_{i=0}^{n} \mathrm{nd}[P]_i.$$

The paper assumes only closure under permutations of the variables; the counting argument also
needs invariance under adding or removing dummy variables. Closure under permutations alone is not
enough: if $P_1$ holds for all four $1$-variable functions and $P_n$ holds for none when
$n \ne 1$, then $[P]_1 = 4$ but $\mathrm{nd}[P]_0 + \mathrm{nd}[P]_1 = 0 + 2 = 2$.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 11 (`jis-2025-25.3.4-prop-11`). -/
public theorem_wanted boolFunClassCount_varPerm_eq_sum_nondegenerate
    (P : ∀ n : ℕ, ((Fin n → Bool) → Bool) → Prop)
    (hP : ∀ (m n : ℕ) (e : Fin m ↪ Fin n) (g : (Fin m → Bool) → Bool),
      P n (fun x => g (x ∘ e)) ↔ P m g)
    (n : ℕ) :
    boolFunClassCount IsBoolFunVarPermEquiv (P n)
      = ∑ i ∈ Finset.range (n + 1),
          boolFunClassCount IsBoolFunVarPermEquiv (fun f => IsNondegenerateBoolFun f ∧ P i f)

/-- **Unate versus monotone permutation classes.** Write $[Q]_n$ for the number of classes of
$n$-variable Boolean functions with property $Q$ under permutation of the variables. Let $U$, $M$,
$B$ and $\mathrm{nd}$ be the properties of being unate, monotone (nondecreasing for the
coordinatewise order with $0 < 1$), balanced (true of a function $f$ when $2\,\mathrm{wt}(f) = 2^n$,
where $\mathrm{wt}(f)$ is the weight of $f$) and non-degenerate, and write juxtaposition for
conjunction, so that $BU$ is the property of being balanced and unate. Then for every $n$,
$[\mathrm{nd}\,U]_n \le 2^n [\mathrm{nd}\,M]_n$, $[\mathrm{nd}\,BU]_n \le 2^n [\mathrm{nd}\,BM]_n$,
$[U]_n \le 2^n [M]_n$ and $[BU]_n \le 2^n [BM]_n$.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 12 (`jis-2025-25.3.4-prop-12`). -/
public theorem_wanted boolFunClassCount_varPerm_unate_le (n : ℕ) :
    boolFunClassCount (n := n) IsBoolFunVarPermEquiv
        (fun f => IsNondegenerateBoolFun f ∧ IsUnateBoolFun f)
      ≤ 2 ^ n * boolFunClassCount (n := n) IsBoolFunVarPermEquiv
        (fun f => IsNondegenerateBoolFun f ∧ Monotone f) ∧
    boolFunClassCount (n := n) IsBoolFunVarPermEquiv
        (fun f => IsNondegenerateBoolFun f ∧ IsUnateBoolFun f ∧ 2 * boolFunWeight f = 2 ^ n)
      ≤ 2 ^ n * boolFunClassCount (n := n) IsBoolFunVarPermEquiv
        (fun f => IsNondegenerateBoolFun f ∧ Monotone f ∧ 2 * boolFunWeight f = 2 ^ n) ∧
    boolFunClassCount (n := n) IsBoolFunVarPermEquiv IsUnateBoolFun
      ≤ 2 ^ n * boolFunClassCount (n := n) IsBoolFunVarPermEquiv Monotone ∧
    boolFunClassCount (n := n) IsBoolFunVarPermEquiv
        (fun f => IsUnateBoolFun f ∧ 2 * boolFunWeight f = 2 ^ n)
      ≤ 2 ^ n * boolFunClassCount (n := n) IsBoolFunVarPermEquiv
        (fun f => Monotone f ∧ 2 * boolFunWeight f = 2 ^ n)

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

/-- **Balanced unate and balanced monotone functions have equally many NN- and NPN-classes.**
For every $n$, call an $n$-variable Boolean function $f$ balanced when $2\,\mathrm{wt}(f) = 2^n$,
where $\mathrm{wt}(f)$ is the weight of $f$. The number of NN-inequivalent balanced unate
$n$-variable Boolean functions equals the number of NN-inequivalent balanced monotone ones, and
the number of NPN-inequivalent balanced unate $n$-variable Boolean functions equals the number of
NPN-inequivalent balanced monotone ones. Here monotone means nondecreasing for the coordinatewise
order with $0 < 1$.

Source: Biswas and Sarkar, *Counting Unate and Monotone Boolean Functions
under Restrictions of Balancedness and Non-Degeneracy*, Journal of Integer
Sequences 28 (2025), Article 25.3.4, Proposition 14(b) (`jis-2025-25.3.4-prop-14`). -/
public theorem_wanted boolFunClassCount_balanced_unate_eq_monotone (n : ℕ) :
    boolFunClassCount (n := n) IsBoolFunNNEquiv
        (fun f => IsUnateBoolFun f ∧ 2 * boolFunWeight f = 2 ^ n)
        = boolFunClassCount (n := n) IsBoolFunNNEquiv
          (fun f => Monotone f ∧ 2 * boolFunWeight f = 2 ^ n) ∧
      boolFunClassCount (n := n) IsBoolFunNPNEquiv
        (fun f => IsUnateBoolFun f ∧ 2 * boolFunWeight f = 2 ^ n)
        = boolFunClassCount (n := n) IsBoolFunNPNEquiv
          (fun f => Monotone f ∧ 2 * boolFunWeight f = 2 ^ n)

end

end MetaMathlibExt
