/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.FixedPerimeterAlder
import MathlibExt.Combinatorics.Enumerative.Partition.FixedPerimeterAlderIdentity
import MathlibExt.Combinatorics.Enumerative.Partition.FixedPerimeterDistinctMonotone
import all MathlibExt.Combinatorics.Enumerative.Partition.FixedPerimeterPMResidueArmLeg

/-!
# The degenerate fixed-perimeter Alder inequality

At half the modulus, the two residue classes coincide. The single-residue identity
then reduces the comparison to monotonicity in the gap between distinct parts.

## References

* Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher,
  *Analogues of Alder-Type Partition Inequalities for Fixed Perimeter Partitions*,
  INTEGERS 24 (2024), Article A102, pp. 1–17, Proposition 2 (using Theorem 1).
* Shishuo Fu and Dazhao Tang, *Partitions with fixed largest hook length*,
  The Ramanujan Journal 45 (2018), pp. 375–390. Their fixed-perimeter identity
  is the case $a = 1$ of Chen et al.'s Theorem 1.
* Armin Straub, *Core partitions into distinct parts and an analog of Euler’s theorem*,
  European Journal of Combinatorics 57 (2016), pp. 40–49, Theorem 1.4.
  This is the initial case $d = a = 1$ of that identity.
-/

namespace MetaMathlibExt

/-- **Alder-type inequality in the degenerate case $a = (d + 3)/2$.** Let $n$ be a positive
integer, let $d$ be an odd natural number and put $a = (d + 3)/2$. Then the number
$\ell_d^{(a)}(n)$ of partitions of perimeter $n$ into parts congruent to $a$ or $-a$ modulo
$d + 3$ is at most the number $h_d^{(a)}(n)$ of partitions of perimeter $n$ into $d$-distinct
parts (no part repeats and any two parts differ by at least $d$), all at least $a$. Here the
perimeter of a partition is its largest part plus its number of parts minus $1$.

Source: Ling Chen, Isabelle Hernandez, Zain Shields, and Holly Swisher, *Analogues of Alder-Type
Partition Inequalities for Fixed Perimeter Partitions*, INTEGERS 24 (2024), Article A102,
Proposition 2. -/
public theorem perimeterPMResidueCount_le_perimeterDistinctCount_of_odd {d n : ℕ}
    (hn : 0 < n) (hd : d % 2 = 1) :
    perimeterPMResidueCount d ((d + 3) / 2) n ≤ perimeterDistinctCount d ((d + 3) / 2) n := by
  let a := (d + 3) / 2
  have hhalf : 2 * a = d + 3 := by dsimp [a]; omega
  have ha : 0 < a := by omega
  have hda : a ≤ d + 3 := by omega
  have hsingle : perimeterPMResidueCount d a n = perimeterResidueCount (d + 2) a n := by
    have hneg : d + 3 - a = a := by omega
    have hcast : (d : ℤ) + 3 = ((d + 3 : ℕ) : ℤ) := by simp
    unfold perimeterPMResidueCount perimeterResidueCount
    congr 1
    ext s
    simp only [Finset.mem_filter, hcast, Int.natCast_modEq_iff,
      perimeterPMResidueArmLegCount_ne_zero_iff_and_eq_choose.modEq_neg_iff hda, hneg, or_self]
  calc
    perimeterPMResidueCount d a n = perimeterResidueCount (d + 2) a n := hsingle
    _ = perimeterDistinctCount (d + 2) a n :=
      (perimeterDistinctCount_eq_perimeterResidueCount (by omega) hn ha hda).symm
    _ ≤ perimeterDistinctCount (d + 1) a n :=
      (perimeterDistinctCount_shift_inequalities (Nat.succ_pos d) hn ha).2.1
    _ ≤ perimeterDistinctCount d a n :=
      (perimeterDistinctCount_shift_inequalities (by omega) hn ha).2.1

end MetaMathlibExt
