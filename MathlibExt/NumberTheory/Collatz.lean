/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.Lattice.Nat

/-!
# Collatz iteration

Shared definitions for the Collatz map, its iterates, and the stopping time.
-/

@[expose] public section

namespace Nat

/-- **The Collatz map.** The Collatz map $T : \mathbb{N} \to \mathbb{N}$ sends a natural number
$n$ to $n / 2$ if $n$ is even and to $3n + 1$ if $n$ is odd. -/
def collatzStep (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- **Iterates of the Collatz map.** Let $T : \mathbb{N} \to \mathbb{N}$ be the Collatz map, which
sends $n$ to $n / 2$ if $n$ is even and to $3n + 1$ if $n$ is odd. For natural numbers $k$ and
$n$, the $k$-th Collatz iterate of $n$ is $T^k(n)$, the result of applying $T$ to $n$ exactly $k$
times: $T^0(n) = n$ and $T^{k+1}(n) = T(T^k(n))$. -/
def collatzIterate : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => collatzStep (collatzIterate k n)

open Classical in
/-- **Collatz stopping time.** Let $T : \mathbb{N} \to \mathbb{N}$ be the Collatz map, which sends
$n$ to $n / 2$ if $n$ is even and to $3n + 1$ if $n$ is odd, and let $T^k$ denote its $k$-fold
iterate, with $T^0(n) = n$. For a natural number $n$, the Collatz stopping time of $n$ is
undefined if $n = 0$ or if $T^k(n) \ne 1$ for every $k \in \mathbb{N}$; otherwise it is the least
$k \in \mathbb{N}$ with $T^k(n) = 1$.

In the Collatz literature this quantity is often called the total stopping time. -/
noncomputable def collatzStoppingTime (n : ℕ) : Option ℕ :=
  if n = 0 then none
  else if ∃ k : ℕ, collatzIterate k n = 1 then
    some (sInf {k : ℕ | collatzIterate k n = 1})
  else
    none

end Nat
