/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Enumerative.Partition.FixedPerimeterArmLegEquality
public import MathlibExt.Combinatorics.Enumerative.Partition.FixedPerimeterDistinctArmLeg
public import MathlibExt.Combinatorics.Enumerative.Partition.FixedPerimeterDistinctMonotone
public import MathlibExt.Combinatorics.Enumerative.Partition.FixedPerimeterPMResidueArmLeg
public import MathlibExt.Combinatorics.Enumerative.Partition.FixedPerimeterResidueArmLeg

/-!
# Alder-type inequalities for fixed perimeter partitions

Statements from Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of
Alder-Type Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024),
Article A102 (arXiv:2406.07655).

A partition is a multiset of positive parts; its perimeter is `α + λ - 1`, with `α` the largest
part and `λ` the number of parts (Section 1 of the paper). The paper's `h_d^(a)`, `f_d^(a)` and
`ℓ_d^(a)` are `perimeterDistinctCount`, `perimeterResidueCount` and `perimeterPMResidueCount`;
their refinements by largest part `α = m` and number of parts `λ = k` carry the suffix `ArmLeg`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Fixed-perimeter identity for $d$-distinct parts.** Let $d$ and $n$ be positive integers and
let $a$ be an integer with $1 \le a \le d + 1$. Then the number $h_d^{(a)}(n)$ of partitions of
perimeter $n$ into $d$-distinct parts (no part repeats and any two parts differ by at least $d$),
all at least $a$, equals the number $f_d^{(a)}(n)$ of partitions of perimeter $n$ into parts
congruent to $a$ modulo $d + 1$. Here the perimeter of a partition is its largest part plus its
number of parts minus $1$.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Theorem 1. -/
public theorem_wanted perimeterDistinctCount_eq_perimeterResidueCount {d a n : ℕ} (hd : 0 < d)
    (hn : 0 < n) (ha : 1 ≤ a) (had : a ≤ d + 1) :
    perimeterDistinctCount d a n = perimeterResidueCount d a n

/-- **Reverse Alder-type inequality for fixed perimeter partitions.** Let $d$, $n$ and $a$ be
positive integers with $a < (d + 3)/2$. Then the number $h_d^{(a)}(n)$ of partitions of perimeter
$n$ into $d$-distinct parts (no part repeats and any two parts differ by at least $d$), all at
least $a$, is at most the number $\ell_d^{(a)}(n)$ of partitions of perimeter $n$ into parts
congruent to $a$ or $-a$ modulo $d + 3$. Here the perimeter of a partition is its largest part
plus its number of parts minus $1$.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Theorem 2. -/
public theorem_wanted perimeterDistinctCount_le_perimeterPMResidueCount {d a n : ℕ} (hd : 0 < d)
    (hn : 0 < n) (ha : 0 < a) (had : 2 * a < d + 3) :
    perimeterDistinctCount d a n ≤ perimeterPMResidueCount d a n

/-- **Monotonicity of fixed perimeter counts with parts $\equiv \pm a \pmod{d+3}$.** For natural
numbers $d$, $a$ and $n$, let $\ell_d^{(a)}(n)$ be the number of partitions of perimeter $n$
(largest part plus number of parts minus $1$) into parts congruent to $a$ or $-a$ modulo $d + 3$.
If $d$, $n$ and $a$ are positive with $a < (d + 3)/2$, then
$\ell_d^{(a)}(n) \le \ell_d^{(a)}(n + 1)$ and $\ell_{d+1}^{(a)}(n) \le \ell_d^{(a)}(n)$.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Proposition 1. -/
public theorem_wanted perimeterPMResidueCount_shift_inequalities {d a n : ℕ} (hd : 0 < d)
    (hn : 0 < n) (ha : 0 < a) (had : 2 * a < d + 3) :
    perimeterPMResidueCount d a n ≤ perimeterPMResidueCount d a (n + 1) ∧
      perimeterPMResidueCount (d + 1) a n ≤ perimeterPMResidueCount d a n

/-- **Alder-type inequality in the degenerate case $a = (d + 3)/2$.** Let $n$ be a positive
integer, let $d$ be an odd natural number and put $a = (d + 3)/2$. Then the number
$\ell_d^{(a)}(n)$ of partitions of perimeter $n$ into parts congruent to $a$ or $-a$ modulo
$d + 3$ is at most the number $h_d^{(a)}(n)$ of partitions of perimeter $n$ into $d$-distinct
parts (no part repeats and any two parts differ by at least $d$), all at least $a$. Here the
perimeter of a partition is its largest part plus its number of parts minus $1$.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Proposition 2. -/
public theorem_wanted perimeterPMResidueCount_le_perimeterDistinctCount_of_odd {d n : ℕ}
    (hn : 0 < n) (hd : d % 2 = 1) :
    perimeterPMResidueCount d ((d + 3) / 2) n ≤ perimeterDistinctCount d ((d + 3) / 2) n

end

end MetaMathlibExt
