/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Logic.Equiv.Defs

/-!
# Classical permutation pattern containment

`HasPattern` expresses classical pattern containment by an increasing sequence of positions.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted

/-- **Classical pattern containment in a permutation.** Let $\sigma$ be a permutation of
$\{0, 1, \dots, n-1\}$ and let $\pi$ be a map from $\{0, 1, \dots, k-1\}$ to itself. Then
$\sigma$ contains the pattern $\pi$ if there are positions $e_0 < e_1 < \dots < e_{k-1}$ in
$\{0, 1, \dots, n-1\}$ such that for all $i, j < k$, $\sigma(e_i) < \sigma(e_j)$ holds exactly
when $\pi(i) < \pi(j)$. -/
def HasPattern {n k : ℕ} (σ : Equiv.Perm (Fin n))
    (π : Fin k → Fin k) : Prop :=
  ∃ e : Fin k → Fin n, (∀ i j : Fin k, i < j → e i < e j) ∧
    ∀ i j : Fin k, σ (e i) < σ (e j) ↔ π i < π j

end MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted
