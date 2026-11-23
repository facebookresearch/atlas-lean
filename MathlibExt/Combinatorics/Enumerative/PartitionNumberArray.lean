/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Partition number array (concept jis_sem_4bcead3a4bcda58a1d4dbb9f)
-/

namespace MetaMathlibExt

@[expose] public section

namespace PartitionNumberArray

/-- **Extension of a vector by zero.** A vector $(a_0, \dots, a_{n-1})$ of natural numbers
extends to the sequence $\mathbb{N} \to \mathbb{N}$ that sends $j$ to $a_j$ for $j < n$ and to $0$
for $j \ge n$.

Source: concept `jis_sem_4bcead3a4bcda58a1d4dbb9f`; D3 `jis_352979520d341b10e3330dad`. -/
def extendA (n : Nat) (a : Fin n → Nat) (j : Nat) : Nat :=
  if h : j < n then a ⟨j, h⟩ else 0

/-- **Index-weighted partial sum.** For $n \in \mathbb{N}$ and a function
$f \colon \mathbb{N} \to \mathbb{N}$, this is the sum $\sum_{i=0}^{n-1} (i + 1)\,f(i)$.

Source: concept `jis_sem_4bcead3a4bcda58a1d4dbb9f`; source D3
`jis_352979520d341b10e3330dad`. -/
def weightSumAux : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => weightSumAux n f + (n + 1) * f n

/-- **Sum of the first n values of a sequence.** For a natural number $n$ and a sequence
$f \colon \mathbb{N} \to \mathbb{N}$, this is the natural number $\sum_{i=0}^{n-1} f(i)$.

Source: concept `jis_sem_4bcead3a4bcda58a1d4dbb9f`; D3 `jis_352979520d341b10e3330dad`. -/
def countSumAux : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => countSumAux n f + f n

/-- **Weighted size of a multiplicity vector.** For $n \in \mathbb{N}$ and nonnegative integers
$a_1, \dots, a_n$, the weighted size is $\sum_{j=1}^{n} j\,a_j$, the sum of the parts of the
partition with $a_j$ parts equal to $j$.

Source: concept `jis_sem_4bcead3a4bcda58a1d4dbb9f`; source D3
`jis_352979520d341b10e3330dad`. -/
def multWeightSum (n : Nat) (a : Fin n → Nat) : Nat :=
  weightSumAux n (extendA n a)

/-- **Number of parts of an exponent vector.** For a vector $(a_1, \dots, a_n)$ of natural
numbers, this is the natural number $\sum_{j=1}^{n} a_j$.

When $a_j$ is the number of parts equal to $j$ in a partition of $n$, this is the number of parts
of the partition.

Source: concept `jis_sem_4bcead3a4bcda58a1d4dbb9f`; D3 `jis_352979520d341b10e3330dad`. -/
def countSum (n : Nat) (a : Fin n → Nat) : Nat :=
  countSumAux n (extendA n a)

/-- **Partition multiplicity vectors.** A partition multiplicity vector of $n \in \mathbb{N}$
is a tuple $(a_1, \dots, a_n)$ of nonnegative integers with $\sum_{j=1}^{n} j\,a_j = n$. It
encodes the partition of $n$ that has $a_j$ parts equal to $j$.

Source: concept `jis_sem_4bcead3a4bcda58a1d4dbb9f`; source D3
`jis_352979520d341b10e3330dad`. -/
structure PartitionMultiplicity (n : Nat) where
  /-- Exponent coordinates. Concept `jis_sem_4bcead3a4bcda58a1d4dbb9f`;
  source D3 `jis_352979520d341b10e3330dad`. -/
  vec : Fin n → Nat
  /-- Weighted-sum certificate. Concept `jis_sem_4bcead3a4bcda58a1d4dbb9f`;
  source D3 `jis_352979520d341b10e3330dad`. -/
  weighted : multWeightSum n vec = n

/-- **Number of parts of a partition.** Let $(a_1, \dots, a_n)$ be a partition multiplicity
vector of $n$, that is, nonnegative integers with $\sum_{j=1}^{n} j\,a_j = n$, where $a_j$
counts the parts equal to $j$. Its part count is $\sum_{j=1}^{n} a_j$.

Source: concept `jis_sem_4bcead3a4bcda58a1d4dbb9f`; source D3
`jis_352979520d341b10e3330dad`. -/
def partCount {n : Nat} (p : PartitionMultiplicity n) : Nat :=
  countSum n p.vec

/-- **Generalized Stirling numbers of the second kind with parameter k.** For a positive
integer $k$, the numbers $S_2(k; n, m)$, for natural numbers $n$ and $m$, are defined by
$S_2(k; 0, 0) = 1$, by $S_2(k; 0, m) = 0$ and $S_2(k; m, 0) = 0$ for $m \ge 1$, and by

$$S_2(k; n + 1, m + 1) = ((k - 1)n + m + 1)\, S_2(k; n, m + 1) + S_2(k; n, m).$$

Source: concept `jis_sem_4bcead3a4bcda58a1d4dbb9f`; D4 `jis_5d77e2e79b2e6bc427920b34` and
P13 `jis_b4758df0448a56ca110f8d96`. -/
def genStirlingSecond (k : { k : Nat // 0 < k }) : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _m + 1 => 0
  | _n + 1, 0 => 0
  | n + 1, m + 1 =>
    ((k.val - 1) * n + (m + 1)) * genStirlingSecond k n (m + 1) +
      genStirlingSecond k n m

/-- **Factorial product of a sequence.** For a natural number $n$ and a sequence
$g \colon \mathbb{N} \to \mathbb{N}$, this is the natural number
$\prod_{i=0}^{n-1} g(i)!\,\bigl((i+1)!\bigr)^{g(i)}$.

Source: concept `jis_sem_4bcead3a4bcda58a1d4dbb9f`; M3 note `jis_cce30bb8ff6bad04c639b7b6`,
P13 `jis_b4758df0448a56ca110f8d96`, and P14 `jis_15ade3b0c1e657b464e3fd9b`. -/
def denomProdAux : Nat → (Nat → Nat) → Nat
  | 0, _ => 1
  | n + 1, g =>
    denomProdAux n g * (Nat.factorial (g n) * (Nat.factorial (n + 1)) ^ (g n))

/-- **Finite power product.** For $n \in \mathbb{N}$ and functions
$g, f \colon \mathbb{N} \to \mathbb{N}$, this is the product $\prod_{i=0}^{n-1} f(i)^{g(i)}$,
with the convention $0^0 = 1$.

Source: concept `jis_sem_4bcead3a4bcda58a1d4dbb9f`; sources P13
`jis_b4758df0448a56ca110f8d96` and P14 `jis_15ade3b0c1e657b464e3fd9b`. -/
def powProdAux : Nat → (Nat → Nat) → (Nat → Nat) → Nat
  | 0, _, _ => 1
  | n + 1, g, f => powProdAux n g f * (f n) ^ (g n)

/-- **Denominator of the M3 partition number.** Let $p$ be a partition of $n$ with multiplicity
vector $(a_1, \dots, a_n)$, so that exactly $a_j$ parts of $p$ equal $j$ and $\sum_j j a_j = n$.
The $M_3$ denominator of $p$ is the natural number $\prod_{j=1}^{n} a_j!\,(j!)^{a_j}$.

Source: concept `jis_sem_4bcead3a4bcda58a1d4dbb9f`; M3 note `jis_cce30bb8ff6bad04c639b7b6`,
P13 `jis_b4758df0448a56ca110f8d96`, and P14 `jis_15ade3b0c1e657b464e3fd9b`. -/
def m3DenomProd {n : Nat} (p : PartitionMultiplicity n) : Nat :=
  denomProdAux n (extendA n p.vec)

/-- **The M3 partition number.** Let $p$ be a partition of $n$ with multiplicity vector
$(a_1, \dots, a_n)$, so that exactly $a_j$ parts of $p$ equal $j$ and $\sum_j j a_j = n$. The
number $M_3(p)$ is the quotient of $n!$ by $\prod_{j=1}^{n} a_j!\,(j!)^{a_j}$ in natural-number
division.

This division is exact, so $M_3(p) = n! / \prod_{j=1}^{n} a_j!\,(j!)^{a_j}$.

Source: concept `jis_sem_4bcead3a4bcda58a1d4dbb9f`; M3 note `jis_cce30bb8ff6bad04c639b7b6`,
P13 `jis_b4758df0448a56ca110f8d96`, and P14 `jis_15ade3b0c1e657b464e3fd9b`. -/
def M3 {n : Nat} (p : PartitionMultiplicity n) : Nat :=
  Nat.factorial n / m3DenomProd p

/-- **Product of powers over a partition.** Let $p$ be a partition of $n$ with multiplicity
vector $(a_1, \dots, a_n)$, so that exactly $a_j$ parts of $p$ equal $j$ and $\sum_j j a_j = n$.
For natural numbers $f_1, \dots, f_n$, the product of powers of $f$ over $p$ is the natural
number $\prod_{j=1}^{n} f_j^{a_j}$.

Source: concept `jis_sem_4bcead3a4bcda58a1d4dbb9f`; sources P13
`jis_b4758df0448a56ca110f8d96` and P14 `jis_15ade3b0c1e657b464e3fd9b`. -/
def arrayPowProd {n : Nat} (p : PartitionMultiplicity n) (f : Fin n → Nat) : Nat :=
  powProdAux n (extendA n p.vec) (extendA n f)

/-- **The hat M32 partition number array.** Let $k$ be a positive integer and let $p$ be a
partition of $n$ with multiplicity vector $(a_1, \dots, a_n)$, so that exactly $a_j$ parts of $p$
equal $j$ and $\sum_j j a_j = n$. Write $S_2(k; j, 1)$ for the generalized Stirling numbers of
the second kind with parameter $k$. The entry $\widehat{M}_{32}(k; p)$ is the natural number
$\prod_{j=1}^{n} S_2(k; j, 1)^{a_j}$.

Source: concept `jis_sem_4bcead3a4bcda58a1d4dbb9f`; D5 `jis_10fbc6d36dfbad8b53d9b3ee`. -/
def hatM32 (k : { k : Nat // 0 < k }) {n : Nat} (p : PartitionMultiplicity n) : Nat :=
  arrayPowProd p (fun i => genStirlingSecond k (i.val + 1) 1)

/-- **The partition number array $M_{32}(k)$.** Let $k$ be a positive integer and let
$a = (a_1, \dots, a_n)$ be a partition multiplicity vector of $n$, that is, nonnegative integers
with $\sum_{j=1}^{n} j\,a_j = n$, where $a_j$ counts the parts equal to $j$. Then
$M_{32}(k; a) = M_3(a) \prod_{j=1}^{n} S_2(k; j, 1)^{a_j}$, where $M_3(a)$ is $n!$ divided by
$\prod_{j=1}^{n} a_j!\,(j!)^{a_j}$ (the division is exact), and
$S_2(k; j, 1) = \prod_{i=1}^{j-1} ((k - 1)i + 1)$ is the first column of the generalized
Stirling numbers of the second kind.

Source: concept `jis_sem_4bcead3a4bcda58a1d4dbb9f`; sources D4
`jis_5d77e2e79b2e6bc427920b34` and P13 `jis_b4758df0448a56ca110f8d96`. -/
def M32 (k : { k : Nat // 0 < k }) {n : Nat} (p : PartitionMultiplicity n) : Nat :=
  M3 p * hatM32 k p

/-- **Absolute first column of the generalized Stirling numbers of the first kind.** For
positive integers $k$ and $j$, the absolute value $|S_1(k; j, 1)|$ is defined as the quotient
$(j + k - 2)!/(k - 1)!$.

Source: concept `jis_sem_4bcead3a4bcda58a1d4dbb9f`; source P14
`jis_15ade3b0c1e657b464e3fd9b`. -/
def stirlingFirstAbsFirstCol (k : { k : Nat // 0 < k }) (j : { j : Nat // 0 < j }) : Nat :=
  Nat.factorial (j.val + k.val - 2) / Nat.factorial (k.val - 1)

/-- **The M31 partition number array.** Let $k$ be a positive integer and let $p$ be a
partition of $n$ with multiplicity vector $(a_1, \dots, a_n)$, so that exactly $a_j$ parts of $p$
equal $j$ and $\sum_j j a_j = n$. Write $M_3(p)$ for the M3 partition number of $p$, and for
$j \ge 1$ write $c_j = (j + k - 2)!/(k - 1)!$, the absolute value of the generalized Stirling
number of the first kind $S_1(k; j, 1)$. The entry $M_{31}(k; p)$ is the natural number
$M_3(p) \prod_{j=1}^{n} c_j^{a_j}$.

Source: concept `jis_sem_4bcead3a4bcda58a1d4dbb9f`; D7 `jis_5d8cd038f955171c2a77fec1` and
P14 `jis_15ade3b0c1e657b464e3fd9b`. -/
def M31 (k : { k : Nat // 0 < k }) {n : Nat} (p : PartitionMultiplicity n) : Nat :=
  M3 p * arrayPowProd p (fun i => stirlingFirstAbsFirstCol k ⟨i.val + 1, Nat.succ_pos _⟩)

end PartitionNumberArray

end

end MetaMathlibExt
