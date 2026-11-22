/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.YoungTableaux.HookLength
public import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# The hook length formula and the sum of squares of `f^λ`

Two central enumerative facts about standard Young tableaux, from Stanley, *Topics in
Algebraic Combinatorics*, author's draft of 1 February 2013
(https://math.mit.edu/~rstan/algcomb/algcomb.pdf; published as *Algebraic Combinatorics: Walks,
Trees, Tableaux, and More*, Springer, 2013), Chapter 8:

* the hook length formula of Frame, Robinson and Thrall (Theorem 8.1);
* `∑_{λ ⊢ n} (f^λ)² = n!` (Corollary 8.5), which the RSK algorithm proves bijectively
  (Theorem 8.13: RSK is a bijection between `𝔖ₙ` and pairs of standard Young tableaux of the
  same shape `λ ⊢ n`).
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

/-- **Sum of the squares of the numbers of standard Young tableaux.** For every `n`,
`∑_{λ ⊢ n} (f^λ)² = n!` (Stanley, *Topics in Algebraic Combinatorics*, author's draft of
1 February 2013, Corollary 8.5; bijectively by the RSK algorithm, Theorem 8.13). -/
theorem_wanted sum_sytCount_sq (n : ℕ) :
    ∑ p : n.Partition, sytCount (YoungDiagram.ofPartition p) ^ 2 = n.factorial

end MathlibExt.Combinatorics.YoungTableaux.HookLengthWanted
