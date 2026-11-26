/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic

/-!
# Conway–Hofstadter-like sequences

This file formalizes the `k`-sequences introduced by John A. Pelesko in
*Generalizing the Conway-Hofstadter $10,000 Sequence*:
<https://cs.uwaterloo.ca/journals/JIS/VOL7/Pelesko/pel11.tex>.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **One-based residue.** For natural numbers $a$ and $m$, the one-based residue of $a$ modulo
$m$ is $a \bmod m$ if this is nonzero, and $m$ if $a \bmod m = 0$ (here $a \bmod 0 = a$). This is
the residue convention used in Pelesko's recurrence. -/
def conwayHofstadterResidue (a m : ℕ) : ℕ :=
  if a % m = 0 then m else a % m

/-- **Conway–Hofstadter-like sequence.** Let $k$ be a natural number. A sequence
$c : \mathbb{N} \to \mathbb{N}$ is a Conway–Hofstadter-like sequence of order $k$ when
$c(1) = c(2) = 1$ and, for every $n \ge 3$,

$$c(n) = c(i_n) + c(n - i_n),$$

where $i_n$ is the one-based residue of $k \, c(n-1)$ modulo $n - 1$: it equals
$k \, c(n-1) \bmod (n-1)$ when this is nonzero, and $n - 1$ otherwise.

The value $c(0)$ is not constrained. -/
def IsConwayHofstadterLikeSequence (k : ℕ) (c : ℕ → ℕ) : Prop :=
  c 1 = 1 ∧ c 2 = 1 ∧ ∀ n : ℕ, 3 ≤ n →
    let i := conwayHofstadterResidue (k * c (n - 1)) (n - 1)
    c n = c i + c (n - i)

end MetaMathlibExt
