/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.YoungTableaux.HookLength
public import MathlibExt.Combinatorics.YoungTableaux.SumSYTCountSq
public import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# The hook length formula

The hook length formula of Frame, Robinson and Thrall is Theorem 8.1 of Stanley,
*Topics in Algebraic Combinatorics*, author's draft of 1 February 2013
(https://math.mit.edu/~rstan/algcomb/algcomb.pdf).
-/

@[expose] public section

open MathlibExt.Combinatorics.YoungTableaux.HookLength

namespace MathlibExt.Combinatorics.YoungTableaux.HookLengthWanted

/-- **Hook length formula.** For a partition `λ ⊢ n`, the number of standard Young tableaux of
shape `λ` is `f^λ = n! / ∏_{u ∈ λ} h(u)`, the product running over the cells `u` of the diagram
of `λ` and `h(u)` the hook length; stated here with the denominator cleared (Stanley, *Topics in
Algebraic Combinatorics*, author's draft of 1 February 2013, Theorem 8.1). -/
theorem_wanted sytCount_mul_prod_hookLength (μ : YoungDiagram) :
    sytCount μ * ∏ c ∈ μ.cells, hookLength μ c = μ.card.factorial

end MathlibExt.Combinatorics.YoungTableaux.HookLengthWanted
