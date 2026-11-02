/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Order.Lattice.Nat

@[expose] public section

/-!
# Mex-related partition congruences — wishlist

Source: Rupam Barman and Ajit Singh, "Mex-Related Partition Functions of Andrews and
Newman", Journal of Integer Sequences 24 (2021), Article 21.6.3.
Live TeX: https://cs.uwaterloo.ca/journals/JIS/VOL24/Barman/barman3.tex
- Complete-source SHA-256:
  `51b9a755f8d2ed45c02aa446de36927b92ca727a1368832693178415216afff0`
- Definition lines 89–94 SHA-256:
  `0f6a48279816237320a39e44b91cee7622c69ddd9873db25d145588a75d6976e`
- Congruence context lines 192–211 SHA-256:
  `6753b88c5c658cdb51b1111f6a6f0f2298ade4c939bda92df01b49b7b873b003`
- Corollary lines 199–209 SHA-256:
  `d227c029ad086c5ee3945f8dbb97d58a92e58369aa09f006374a8c673feecf34`

Exact definition choices: for a partition `λ` of `n`, `mex_{A,a}(λ)` is the smallest
positive natural number congruent to `a` modulo `A` that is not a part of `λ`
(rendered with `sInf` over positive naturals with `m ≡ a [MOD A]` absent from
`λ.parts`); `p_{A,a}(n)` counts the partitions `λ` of `n` with
`mex_{A,a}(λ) ≡ a [MOD 2 * A]`; `δ_{p,k}` is the least natural representative of
the inverse of 24 modulo `p ^ k` (rendered with `sInf` over naturals with
`24 * δ ≡ 1 [MOD p ^ k]`; the theorem only uses `p = 5, 7, 11` and `k > 0`,
where that set is nonempty). The source floor `⌊k/2⌋ + 1` is preserved as
natural `k / 2 + 1`.

Correction from the archive (`wanted317_308_ramanujan_mesh_partition_congruences_c3c0556b.zip`,
SHA-256 `b1afb1af1916926b753de342ecf2f5ec149ae61650795e94f1c1d4b3daacedfe`):
the donor candidate `RamanujanMeshCongruences.lean` (SHA-256
`c3c0556b0ffb807e14352acc8eda0e99b4525e57aba0eb914509a69b6498762e`) is untrusted.
It misspells "mex" as "mesh" and quantifies arbitrary functions `meshPartition` and
`meshDelta` whose hypotheses do not define the partition function, so its claimed
theorem is false for arbitrary inputs. This module does not retain that abstraction;
it states the congruences about the concrete helpers above.

Archive provenance: `wanted317_308_ramanujan_mesh_partition_congruences_c3c0556b.zip`.
-/

namespace MetaMathlibExt

/-- **Mex of a partition in a residue class.** For natural numbers $A$, $a$ and $n$ and a
partition $\lambda$ of $n$, $\operatorname{mex}_{A,a}(\lambda)$ is the smallest positive integer
congruent to $a$ modulo $A$ that is not a part of $\lambda$, and $0$ if there is no such integer
(which happens only when $A = 0$). -/
noncomputable def partitionMex (A a : ℕ) {n : ℕ} (lam : Nat.Partition n) : ℕ :=
  sInf { m : ℕ | 0 < m ∧ m ≡ a [MOD A] ∧ m ∉ lam.parts }

/-- **Mex-related partition function of Andrews and Newman.** For natural numbers $A$, $a$ and $n$,
$p_{A,a}(n)$ is the number of partitions $\lambda$ of $n$ such that
$\operatorname{mex}_{A,a}(\lambda) \equiv a \pmod{2A}$, where $\operatorname{mex}_{A,a}(\lambda)$
is the smallest positive integer congruent to $a$ modulo $A$ that is not a part of $\lambda$, and
$0$ if there is no such integer. -/
noncomputable def mexPartitionNumber (A a n : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Nat.Partition n)).filter
    (fun lam => decide (partitionMex A a lam ≡ a [MOD 2 * A]))).card

/-- **Least inverse of 24 modulo a power.** For natural numbers $p$ and $k$, $\delta_{p,k}$ is the
least natural number $\delta$ with $24\delta \equiv 1 \pmod{p^k}$, and $0$ if there is no such
$\delta$, which happens exactly when $p^k$ and $24$ have a common factor greater than $1$. -/
noncomputable def ramanujanDelta (p k : ℕ) : ℕ :=
  sInf { delta : ℕ | 24 * delta ≡ 1 [MOD p ^ k] }

/-- **Ramanujan congruences for mex-related partition functions.** For a positive integer $A$, a
natural number $a$ and a partition $\lambda$, let $\operatorname{mex}_{A,a}(\lambda)$ be the
smallest positive integer congruent to $a$ modulo $A$ that is not a part of $\lambda$; let
$p_{A,a}(N)$ be the number of partitions $\lambda$ of $N$ with
$\operatorname{mex}_{A,a}(\lambda) \equiv a \pmod{2A}$; and let $\delta_{p,k}$ be the least
natural number $\delta$ with $24\delta \equiv 1 \pmod{p^k}$. Then for all natural numbers
$k \ge 1$, $t \ge 1$ and $n$, for each $p \in \{5, 7, 11\}$ and for both $A = p^k t$ and
$A = 2p^k t$,

$$p_{A,\,p^k t}(p^k n + \delta_{p,k}) \equiv 0 \pmod{p^{e}},$$

where $e = k$ for $p = 5$ and $p = 11$, and $e = \lfloor k/2 \rfloor + 1$ for $p = 7$.

Source: Barman–Singh, JIS 24 (2021), Art. 21.6.3, corollary. -/
public theorem_wanted ramanujan_mex_partition_congruences
    (k t n : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t) :
    mexPartitionNumber (5 ^ k * t) (5 ^ k * t) (5 ^ k * n + ramanujanDelta 5 k) ≡
      0 [MOD 5 ^ k] ∧
    mexPartitionNumber (7 ^ k * t) (7 ^ k * t) (7 ^ k * n + ramanujanDelta 7 k) ≡
      0 [MOD 7 ^ (k / 2 + 1)] ∧
    mexPartitionNumber (11 ^ k * t) (11 ^ k * t)
      (11 ^ k * n + ramanujanDelta 11 k) ≡ 0 [MOD 11 ^ k] ∧
    mexPartitionNumber (2 * (5 ^ k * t)) (5 ^ k * t)
      (5 ^ k * n + ramanujanDelta 5 k) ≡ 0 [MOD 5 ^ k] ∧
    mexPartitionNumber (2 * (7 ^ k * t)) (7 ^ k * t)
      (7 ^ k * n + ramanujanDelta 7 k) ≡ 0 [MOD 7 ^ (k / 2 + 1)] ∧
    mexPartitionNumber (2 * (11 ^ k * t)) (11 ^ k * t)
      (11 ^ k * n + ramanujanDelta 11 k) ≡ 0 [MOD 11 ^ k]

end MetaMathlibExt
