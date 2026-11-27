/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecificLimits.Basic

open scoped BigOperators

/-!
# Takagi function on dyadic rationals

Formalizes Definition `takagi_newdef` (source statement `jis_23b2f8f9e624bca533bd6deb`,
concept `jis_sem_95dbf183cc4eaf1172157db5`): binary digits, the `ell` coefficients,
and the Takagi sum over dyadic presentations `n / 2 ^ (k + 1)`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Binary digits of a natural number.** For a natural number $n$ and an integer $i$, the binary
digit $n_i \in \{0, 1\}$ of $n$ is the coefficient of $2^i$ in the binary expansion of $n$ when
$i \ge 0$, and $n_i = 0$ when $i < 0$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Definition `takagi_newdef` (concept
`jis_sem_95dbf183cc4eaf1172157db5`, source statement `jis_23b2f8f9e624bca533bd6deb`). -/
public def takagiBit (n : Nat) (i : Int) : Nat :=
  if 0 ≤ i then (if Nat.testBit n i.toNat then 1 else 0) else 0

/-- **Takagi coefficients.** Let $n$ be a natural number and $k$ an integer, and write $n_j$ for
the binary digit of $n$ at position $j$ (so $n_j = 0$ for $j < 0$). The Takagi coefficients
$\ell_i(n, k)$, for natural numbers $i$, are the natural numbers given by $\ell_0(n, k) = 0$ and,
for every natural number $i$, with $s_i = \sum_{j=0}^{i-1} n_{k-j}$, by $\ell_{i+1}(n, k) = s_i$
if $n_{k-i} = 0$ and $\ell_{i+1}(n, k) = i - s_i$ otherwise.

In particular $\ell_1(n, k) = 0$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Definition `takagi_newdef` (concept
`jis_sem_95dbf183cc4eaf1172157db5`, source statement `jis_23b2f8f9e624bca533bd6deb`). -/
public def takagiEll (n : Nat) (k : Int) : Nat → Nat
  | 0 => 0
  | (i + 1) =>
    if takagiBit n (k - (i : Int)) = 0 then
      ∑ j ∈ Finset.range i, takagiBit n (k - (j : Int))
    else i - ∑ j ∈ Finset.range i, takagiBit n (k - (j : Int))

/-- **Takagi function on dyadic presentations.** For a natural number $n$ and an integer $k$, the
Takagi value $\tau(n, k)$ of the dyadic presentation $n / 2^{k+1}$ is the sum of the real series
$\sum_{i=0}^{\infty} \ell_{i+1}(n, k) / 2^{i+1}$, where $\ell_i(n, k)$ denotes the $i$-th Takagi
coefficient of $n$ and $k$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Definition `takagi_newdef` (concept
`jis_sem_95dbf183cc4eaf1172157db5`, source statement `jis_23b2f8f9e624bca533bd6deb`). -/
public noncomputable def takagiNewdef (n : Nat) (k : Int) : Real :=
  ∑' i, (takagiEll n k (i + 1) : Real) / 2 ^ (i + 1)

/-- **Formula for the binary digits.** For every natural number $n$ and every integer $i$, the
binary digit $n_i$ of $n$ equals $1$ if $i \ge 0$ and the coefficient of $2^i$ in the binary
expansion of $n$ is $1$, and equals $0$ otherwise.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Definition `takagi_newdef` (concept
`jis_sem_95dbf183cc4eaf1172157db5`, source statement `jis_23b2f8f9e624bca533bd6deb`). -/
public theorem takagiBit_eq (n : Nat) (i : Int) :
    takagiBit n i =
      (if 0 ≤ i then (if Nat.testBit n i.toNat then 1 else 0) else 0) := rfl

/-- **The Takagi coefficient at index zero.** For every natural number $n$ and every integer $k$,
the Takagi coefficient $\ell_0(n, k)$ is $0$.

The index $0$ is only an auxiliary base value: the Takagi series starts at $\ell_1$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Definition `takagi_newdef` (concept
`jis_sem_95dbf183cc4eaf1172157db5`, source statement `jis_23b2f8f9e624bca533bd6deb`). -/
public theorem takagiEll_zero (n : Nat) (k : Int) : takagiEll n k 0 = 0 := rfl

/-- **Formula for the Takagi coefficients.** For every natural number $n$, every integer $k$ and
every natural number $i$, let $s_i = \sum_{j=0}^{i-1} n_{k-j}$, where $n_j$ denotes the binary
digit of $n$ at position $j$. Then the Takagi coefficient $\ell_{i+1}(n, k)$ equals $s_i$ if
$n_{k-i} = 0$, and equals $i - s_i$ otherwise.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Definition `takagi_newdef` (concept
`jis_sem_95dbf183cc4eaf1172157db5`, source statement `jis_23b2f8f9e624bca533bd6deb`). -/
public theorem takagiEll_succ (n : Nat) (k : Int) (i : Nat) :
    takagiEll n k (i + 1) =
      (if takagiBit n (k - (i : Int)) = 0 then
        ∑ j ∈ Finset.range i, takagiBit n (k - (j : Int))
      else i - ∑ j ∈ Finset.range i, takagiBit n (k - (j : Int))) := rfl

/-- **Series for the Takagi value.** For every natural number $n$ and every integer $k$, the
Takagi value $\tau(n, k)$ of the dyadic presentation $n / 2^{k+1}$ satisfies
$\tau(n, k) = \sum_{i=0}^{\infty} \ell_{i+1}(n, k) / 2^{i+1}$, where $\ell_i(n, k)$ denotes the
$i$-th Takagi coefficient of $n$ and $k$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Definition `takagi_newdef` (concept
`jis_sem_95dbf183cc4eaf1172157db5`, source statement `jis_23b2f8f9e624bca533bd6deb`). -/
public theorem takagiNewdef_eq (n : Nat) (k : Int) :
    takagiNewdef n k =
      ∑' i, (takagiEll n k (i + 1) : Real) / 2 ^ (i + 1) := rfl

/-- **Binary digits at negative positions vanish.** For every natural number $n$ and every
integer $i < 0$, the binary digit $n_i$ of $n$ is $0$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Definition `takagi_newdef` (concept
`jis_sem_95dbf183cc4eaf1172157db5`, source statement `jis_23b2f8f9e624bca533bd6deb`). -/
public theorem takagiBit_neg (n : Nat) (i : Int) (h : i < 0) :
    takagiBit n i = 0 := by
  unfold takagiBit
  rw [ite_eq_right (not_le.mpr h)]

/-- **The first Takagi coefficient vanishes.** For every natural number $n$ and every integer $k$,
the Takagi coefficient $\ell_1(n, k)$ is $0$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Definition `takagi_newdef` (concept
`jis_sem_95dbf183cc4eaf1172157db5`, source statement `jis_23b2f8f9e624bca533bd6deb`). -/
public theorem takagiEll_one (n : Nat) (k : Int) : takagiEll n k 1 = 0 := by
  simp [takagiEll]

end

end MetaMathlibExt
