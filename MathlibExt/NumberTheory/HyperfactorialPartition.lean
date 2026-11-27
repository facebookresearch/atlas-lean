/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-! Provenance: concept `jis_sem_c632991dc77d0efec89f490f`,
source statement `jis_2803b664db749f0c99721a41`. -/

namespace MetaMathlibExt

@[expose] public section

/-- **Normalized hyperfactorial digit vectors.** A vector $(h_1, \dots, h_k)$ of natural numbers
is normalized when either $k = 0$ or its last entry $h_k$ is nonzero. In particular the empty
vector is normalized; it is the canonical representation of zero. -/
def HyperfactorialDigitsNormalized (k : ℕ) (digits : Fin k → ℕ) : Prop :=
  ∀ h : 0 < k, digits ⟨k - 1, Nat.sub_lt h (by decide)⟩ ≠ 0

/-- **Hyperfactorial partition.** A hyperfactorial partition of a natural number $n$ consists of
a length $k \in \mathbb{N}$ and natural numbers $h_1, \dots, h_k$ such that $h_i \le 2i$ for
every $1 \le i \le k$, the digit vector is normalized (either $k = 0$ or $h_k \neq 0$), and

$$n = \sum_{i=1}^{k} h_i \cdot i!.$$

Source: concept `jis_sem_c632991dc77d0efec89f490f`, source statement
`jis_2803b664db749f0c99721a41`. -/
structure HyperfactorialPartition (n : ℕ) where
  /-- Length `k` of the digit list (clause `digits`;
  source statement `jis_2803b664db749f0c99721a41`). -/
  k : ℕ
  /-- One-based digit list `[h₁, …, hₖ]!` as a `Fin k` vector of naturals
  (clause `digits`; source statement `jis_2803b664db749f0c99721a41`). -/
  digits : Fin k → ℕ
  /-- Upper digit bound `hᵢ ≤ 2 * i` at one-based index `i.val + 1`
  (clause `bounds`; source statement `jis_2803b664db749f0c99721a41`). -/
  bound : ∀ i : Fin k, digits i ≤ 2 * (i.val + 1)
  /-- The final digit is nonzero when `k > 0`, ruling out trailing-zero extensions. -/
  normalized : HyperfactorialDigitsNormalized k digits
  /-- Exact value `n = ∑_{i=1}^k hᵢ * i!` (clause `value`;
  source statement `jis_2803b664db749f0c99721a41`). -/
  value : n = Finset.sum Finset.univ (fun i : Fin k => digits i * Nat.factorial (i.val + 1))

end

end MetaMathlibExt
