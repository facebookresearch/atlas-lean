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
public import MathlibExt.Combinatorics.Enumerative.BooleanFunctionEssentialSupport

namespace MetaMathlibExt

@[expose] public section

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
