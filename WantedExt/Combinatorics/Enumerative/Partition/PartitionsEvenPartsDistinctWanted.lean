/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.ModEq
public import WantedExt.Combinatorics.Enumerative.OverpartitionsOddPartsWanted

namespace MetaMathlibExt

@[expose] public section

/--
**Congruences modulo 24 for partitions with distinct even parts.** Write $\mathrm{ped}(m)$ for the
number of partitions of $m$ in which the even parts are distinct (odd parts may repeat). For every
natural number $n$, each of $\mathrm{ped}(225n+43)$, $\mathrm{ped}(225n+88)$,
$\mathrm{ped}(225n+133)$ and $\mathrm{ped}(225n+223)$ is congruent to $0$ modulo $24$.

Source: Hemjyoti Nath, *New Congruences for Partitions Where the Even Parts Are Distinct*, INTEGERS 24 (2024), Article A79, Theorem 1.1.
-/
public theorem_wanted partitionsEvenPartsDistinct_mod24_progressions (n : ℕ) :
    Nat.ModEq 24 (distinctEvenPartsCount (225 * n + 43)) 0 ∧
      Nat.ModEq 24 (distinctEvenPartsCount (225 * n + 88)) 0 ∧
      Nat.ModEq 24 (distinctEvenPartsCount (225 * n + 133)) 0 ∧
      Nat.ModEq 24 (distinctEvenPartsCount (225 * n + 223)) 0

/--
**Power-of-five congruence modulo 24 for partitions with distinct even parts.** Write
$\mathrm{ped}(m)$ for the number of partitions of $m$ in which the even parts are distinct (odd
parts may repeat). For all natural numbers $k \ge 1$ and $n$,

$$
\mathrm{ped}(9n+7) \equiv \mathrm{ped}\left(9 \cdot 5^{2k} n + \frac{57 \cdot 5^{2k} - 1}{8}\right)
  \pmod{24}.
$$

The quotient is exact, since $57 \cdot 5^{2k} - 1$ is divisible by $8$.

Source: Hemjyoti Nath, *New Congruences for Partitions Where the Even Parts Are Distinct*, INTEGERS 24 (2024), Article A79, Theorem 1.1.
-/
public theorem_wanted partitionsEvenPartsDistinct_mod24_five_power
    (k n : ℕ) (hk : 1 ≤ k) :
    Nat.ModEq 24 (distinctEvenPartsCount (9 * n + 7))
      (distinctEvenPartsCount
        (9 * 5 ^ (2 * k) * n + (57 * 5 ^ (2 * k) - 1) / 8))

end

end MetaMathlibExt
