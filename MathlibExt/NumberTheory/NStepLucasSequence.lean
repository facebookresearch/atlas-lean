/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic

/-!
# n-step Lucas sequence

Formalizes the `n`-step Lucas sequence from Saito (JIS VOL14).
See `nStepLucas` for the indexed sequence and `nStepLucasList`
for the finite-prefix computation.

Source: <https://cs.uwaterloo.ca/journals/JIS/VOL14/Saito/saito22.tex>.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Finite prefixes of the n-step Lucas numbers.** For natural numbers $n$ and $m$, this is the
list $[L^{(n)}_1, \dots, L^{(n)}_m]$ of length $m$ (empty for $m = 0$), where
$L^{(n)}_k = 2^k - 1$ for $1 \le k \le n$ and $L^{(n)}_k$ is the sum of the $n$ preceding terms
for $k \ge n + 1$. For $n = 0$ every term is $0$.

Source: <https://cs.uwaterloo.ca/journals/JIS/VOL14/Saito/saito22.tex> (source
`jis_1628603e2683fb05481e5bfb`, concept `jis_sem_4e0294575601a2b8a5f0d3d7`). -/
def nStepLucasList (n : ℕ) : ℕ → List ℕ
  | Nat.zero => []
  | Nat.succ m =>
    let prev := nStepLucasList n m
    let next :=
      if m + 1 ≤ n then 2 ^ (m + 1) - 1
      else (prev.drop (prev.length - n)).foldl (· + ·) 0
    prev ++ [next]

/-- **n-step Lucas numbers.** For natural numbers $n \ge 1$ and $m$, the $n$-step Lucas number
$L^{(n)}_m$ is defined by $L^{(n)}_0 = 0$, $L^{(n)}_m = 2^m - 1$ for $1 \le m \le n$, and
$L^{(n)}_m = \sum_{i=1}^{n} L^{(n)}_{m-i}$ for $m \ge n + 1$. For $n = 0$ we set
$L^{(0)}_m = 0$ for every $m$.

The source defines $L^{(n)}_m$ only for $m \ge 1$; the value $L^{(n)}_0 = 0$ is a convention.

Source: <https://cs.uwaterloo.ca/journals/JIS/VOL14/Saito/saito22.tex> (source
`jis_1628603e2683fb05481e5bfb`, concept `jis_sem_4e0294575601a2b8a5f0d3d7`). -/
def nStepLucas (n m : ℕ) : ℕ :=
  match n with
  | Nat.zero => 0
  | Nat.succ n => (nStepLucasList (n + 1) m).getLast?.getD 0

end MetaMathlibExt
