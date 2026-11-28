/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Enumerative.Partition.ReciprocalEulerDissection
public import MathlibExt.Combinatorics.Enumerative.Partition.RegularPartitionsLK
public import WantedExt.Combinatorics.Enumerative.Partition.PondPendCongruencesWanted

/-!
# Congruences for `(ℓ, k)`-regular partitions

Statements from Manjil P. Saikia and James A. Sellers, *Generalizing Recent Results of
Kathiravan, Majumdar, Sangale, and Srinivas on `(ℓ, k)`-regular Partitions*, Journal of
Integer Sequences 28 (2025), Article 25.6.1.

`b_{ℓ,k}(n)` counts the partitions of `n` with no part divisible by `ℓ` or by `k`. The paper
writes `f_k = (q^k; q^k)_∞`, which is `qEulerProduct k` (written `𝔣 k` below). Eta-quotient
identities are stated in `ℤ⟦X⟧` with denominators cleared.
-/

open PowerSeries

namespace MetaMathlibExt

@[expose] public section

local notation "𝔣" => qEulerProduct

/-- **Congruences modulo $12$ for $b_{4,9}$ along powers of $2$.** Let $b_{4,9}(n)$ be the
number of partitions of $n$ with no part divisible by $4$ or by $9$. For all natural numbers
$\alpha \ge 3$ and $n$, $b_{4,9}(2^\alpha n + 6 \cdot 2^{\alpha - 3} + 1) \equiv 0 \pmod{12}$.

Source: Manjil P. Saikia and James A. Sellers, *Generalizing Recent Results of Kathiravan,
Majumdar, Sangale, and Srinivas on `(ℓ, k)`-regular Partitions*, Journal of Integer Sequences
28 (2025), Article 25.6.1, Theorem 3 (`jis-2025-25.6.1-thm-3`). -/
public theorem_wanted regularPartitionCount_four_nine_mod_twelve {α : ℕ} (hα : 3 ≤ α) (n : ℕ) :
    regularPartitionCount 4 9 (2 ^ α * n + 6 * 2 ^ (α - 3) + 1) ≡ 0 [MOD 12]

/-- **The 2-dissection of $f_9/f_1$.** Write $f_k = (q^k; q^k)_\infty$ for the Euler products. In
the ring of integer power series in $q$,
$$
f_9 f_2^3 f_6 f_{12} f_{36} = f_1 f_2 f_{12}^4 f_{18} + q f_1 f_4^2 f_6^2 f_{36}^2.
$$
Since each $f_k$ with $k \ge 1$ has constant term $1$ and is therefore invertible, this is the
identity $f_9 / f_1 = f_{12}^3 f_{18} / (f_2^2 f_6 f_{36}) + q f_4^2 f_6 f_{36} / (f_2^3 f_{12})$
with both sides multiplied by $f_1 f_2^3 f_6 f_{12} f_{36}$.

Source: Manjil P. Saikia and James A. Sellers, *Generalizing Recent Results of Kathiravan,
Majumdar, Sangale, and Srinivas on `(ℓ, k)`-regular Partitions*, Journal of Integer Sequences
28 (2025), Article 25.6.1, Lemma 7 (`jis-2025-25.6.1-lem-7`). -/
public theorem_wanted f9_div_f1_two_dissection :
    𝔣 9 * 𝔣 2 ^ 3 * 𝔣 6 * 𝔣 12 * 𝔣 36 =
      𝔣 1 * 𝔣 2 * 𝔣 12 ^ 4 * 𝔣 18 + X * 𝔣 1 * 𝔣 4 ^ 2 * 𝔣 6 ^ 2 * 𝔣 36 ^ 2

/-- **The 2-dissection of $f_3/f_1^3$.** Write $f_k = (q^k; q^k)_\infty$ for the Euler products. In
the ring of integer power series in $q$,
$$
f_3 f_2^9 f_{12}^2 = f_1^3 f_4^6 f_6^3 + 3q f_1^3 f_2^2 f_4^2 f_6 f_{12}^4.
$$
Since each $f_k$ with $k \ge 1$ has constant term $1$ and is therefore invertible, this is the
identity $f_3 / f_1^3 = f_4^6 f_6^3 / (f_2^9 f_{12}^2) + 3q f_4^2 f_6 f_{12}^2 / f_2^7$ with both
sides multiplied by $f_1^3 f_2^9 f_{12}^2$.

Source: Manjil P. Saikia and James A. Sellers, *Generalizing Recent Results of Kathiravan,
Majumdar, Sangale, and Srinivas on `(ℓ, k)`-regular Partitions*, Journal of Integer Sequences
28 (2025), Article 25.6.1, Lemma 8 (`jis-2025-25.6.1-lem-8`). -/
public theorem_wanted f3_div_f1_cube_two_dissection :
    𝔣 3 * 𝔣 2 ^ 9 * 𝔣 12 ^ 2 =
      𝔣 1 ^ 3 * 𝔣 4 ^ 6 * 𝔣 6 ^ 3 + 3 * X * 𝔣 1 ^ 3 * 𝔣 2 ^ 2 * 𝔣 4 ^ 2 * 𝔣 6 * 𝔣 12 ^ 4

/-- **The 2-dissection of $f_3^2/f_1^2$.** Write $f_k = (q^k; q^k)_\infty$ for the Euler products.
In the ring of integer power series in $q$,
$$
f_3^2 f_2^5 f_8 f_{12} f_{24} = f_1^2 f_4^4 f_6 f_{12}^3 + 2q f_1^2 f_2 f_4 f_6^2 f_8^2 f_{24}^2.
$$
Since each $f_k$ with $k \ge 1$ has constant term $1$ and is therefore invertible, this is the
identity $f_3^2 / f_1^2 = f_4^4 f_6 f_{12}^2 / (f_2^5 f_8 f_{24}) +
2q f_4 f_6^2 f_8 f_{24} / (f_2^4 f_{12})$ with both sides multiplied by
$f_1^2 f_2^5 f_8 f_{12} f_{24}$.

Source: Manjil P. Saikia and James A. Sellers, *Generalizing Recent Results of Kathiravan,
Majumdar, Sangale, and Srinivas on `(ℓ, k)`-regular Partitions*, Journal of Integer Sequences
28 (2025), Article 25.6.1, Lemma 9 (`jis-2025-25.6.1-lem-9`). -/
public theorem_wanted f3_sq_div_f1_sq_two_dissection :
    𝔣 3 ^ 2 * 𝔣 2 ^ 5 * 𝔣 8 * 𝔣 12 * 𝔣 24 =
      𝔣 1 ^ 2 * 𝔣 4 ^ 4 * 𝔣 6 * 𝔣 12 ^ 3 +
        2 * X * 𝔣 1 ^ 2 * 𝔣 2 * 𝔣 4 * 𝔣 6 ^ 2 * 𝔣 8 ^ 2 * 𝔣 24 ^ 2

/-- **The 2-dissection of $1/(f_1 f_3)$.** Write $f_k = (q^k; q^k)_\infty$ for the Euler
products. In the ring of integer power series in $q$,
$$
f_2^4 f_4 f_6^4 f_8^2 f_{12} f_{24}^2 =
f_1 f_3 f_2^2 f_8^4 f_{12}^6 + q f_1 f_3 f_4^6 f_6^2 f_{24}^4.
$$
Since each $f_k$ with $k \ge 1$ has constant term $1$ and is therefore invertible, this is the
identity $1 / (f_1 f_3) = f_8^2 f_{12}^5 / (f_2^2 f_4 f_6^4 f_{24}^2) +
q f_4^5 f_{24}^2 / (f_2^4 f_6^2 f_8^2 f_{12})$ with both sides multiplied by
$f_1 f_3 f_2^4 f_4 f_6^4 f_8^2 f_{12} f_{24}^2$.

Source: Manjil P. Saikia and James A. Sellers, *Generalizing Recent Results of Kathiravan,
Majumdar, Sangale, and Srinivas on `(ℓ, k)`-regular Partitions*, Journal of Integer Sequences
28 (2025), Article 25.6.1, Lemma 11 (`jis-2025-25.6.1-lem-11`). -/
public theorem_wanted one_div_f1_f3_two_dissection :
    𝔣 2 ^ 4 * 𝔣 4 * 𝔣 6 ^ 4 * 𝔣 8 ^ 2 * 𝔣 12 * 𝔣 24 ^ 2 =
      𝔣 1 * 𝔣 3 * 𝔣 2 ^ 2 * 𝔣 8 ^ 4 * 𝔣 12 ^ 6 +
        X * 𝔣 1 * 𝔣 3 * 𝔣 4 ^ 6 * 𝔣 6 ^ 2 * 𝔣 24 ^ 4

/-- **Generating function of $b_{4,9}$ at odd arguments.** Let $b_{4,9}(n)$ be the number of
partitions of $n$ with no part divisible by $4$ or by $9$, and write $f_k = (q^k; q^k)_\infty$
for the Euler products. In the ring of integer power series in $q$,
$$
f_1^3 f_6 \sum_{n \ge 0} b_{4,9}(2n + 1) q^n = f_2^3 f_3.
$$
Since $f_1$ and $f_6$ have constant term $1$ and are therefore invertible, this says
$\sum_{n \ge 0} b_{4,9}(2n + 1) q^n = f_2^3 f_3 / (f_1^3 f_6)$.

Source: Manjil P. Saikia and James A. Sellers, *Generalizing Recent Results of Kathiravan,
Majumdar, Sangale, and Srinivas on `(ℓ, k)`-regular Partitions*, Journal of Integer Sequences
28 (2025), Article 25.6.1, Theorem 12 (`jis-2025-25.6.1-thm-12`). -/
public theorem_wanted regularPartitionCount_four_nine_odd_generatingFunction :
    𝔣 1 ^ 3 * 𝔣 6 * PowerSeries.mk (fun n => (regularPartitionCount 4 9 (2 * n + 1) : ℤ)) =
      𝔣 2 ^ 3 * 𝔣 3

/-- **An internal congruence modulo $4$ for $b_{4,9}$.** Let $b_{4,9}(n)$ be the number of
partitions of $n$ with no part divisible by $4$ or by $9$. For every natural number $n$,
$b_{4,9}(16n + 1) \equiv b_{4,9}(4n + 1) \pmod 4$.

Source: Manjil P. Saikia and James A. Sellers, *Generalizing Recent Results of Kathiravan,
Majumdar, Sangale, and Srinivas on `(ℓ, k)`-regular Partitions*, Journal of Integer Sequences
28 (2025), Article 25.6.1, Theorem 13 (`jis-2025-25.6.1-thm-13`). -/
public theorem_wanted regularPartitionCount_four_nine_internal_mod_four (n : ℕ) :
    regularPartitionCount 4 9 (16 * n + 1) ≡ regularPartitionCount 4 9 (4 * n + 1) [MOD 4]

/-- **$b_{4,9}(16n + 13)$ is divisible by $4$.** Let $b_{4,9}(n)$ be the number of partitions of
$n$ with no part divisible by $4$ or by $9$. For every natural number $n$,
$b_{4,9}(16n + 13) \equiv 0 \pmod 4$.

Source: Manjil P. Saikia and James A. Sellers, *Generalizing Recent Results of Kathiravan,
Majumdar, Sangale, and Srinivas on `(ℓ, k)`-regular Partitions*, Journal of Integer Sequences
28 (2025), Article 25.6.1, Theorem 14 (`jis-2025-25.6.1-thm-14`). -/
public theorem_wanted regularPartitionCount_four_nine_sixteen_mul_add_thirteen (n : ℕ) :
    regularPartitionCount 4 9 (16 * n + 13) ≡ 0 [MOD 4]

/-- **$b_{4,9}(32n + 25)$ is divisible by $4$.** Let $b_{4,9}(n)$ be the number of partitions of
$n$ with no part divisible by $4$ or by $9$. For every natural number $n$,
$b_{4,9}(32n + 25) \equiv 0 \pmod 4$.

Source: Manjil P. Saikia and James A. Sellers, *Generalizing Recent Results of Kathiravan,
Majumdar, Sangale, and Srinivas on `(ℓ, k)`-regular Partitions*, Journal of Integer Sequences
28 (2025), Article 25.6.1, Theorem 15 (`jis-2025-25.6.1-thm-15`). -/
public theorem_wanted regularPartitionCount_four_nine_thirtyTwo_mul_add_twentyFive (n : ℕ) :
    regularPartitionCount 4 9 (32 * n + 25) ≡ 0 [MOD 4]

end

end MetaMathlibExt
