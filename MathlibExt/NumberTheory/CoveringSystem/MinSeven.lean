/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.GCDMonoid.Finset
public import MathlibExt.NumberTheory.CoveringSystem
import MathlibExt.NumberTheory.CoveringSystem.TrifonovCovering

/-!
# A distinct covering system with minimum modulus seven

`MetaMathlibExt.exists_distinct_covering_min_seven_lcm_15120` exhibits a covering of the
integers by congruences with distinct moduli, smallest modulus 7 and least common multiple 15120.
We use `TrifonovCovering.isCoveringSystem_of_coverMask_eq` to check all residues in one period.
The witness adapts the partial cover modulo 5040 of Shiliang Zhang and Jiheng Zhang
([arXiv:2607.19029](https://arxiv.org/abs/2607.19029)).
-/

namespace MetaMathlibExt

/-- The witness as pairs of reduced residues and moduli, in increasing order of modulus. -/
private def minSevenClasses : List (ℕ × ℕ) :=
  [(6, 7), (7, 8), (8, 9), (3, 10), (0, 12), (8, 14), (9, 15), (3, 16), (2, 18), (5, 20), (4, 21),
    (6, 24), (23, 27), (2, 28), (27, 30), (0, 35), (29, 36), (1, 40), (10, 42), (14, 45),
    (43, 48), (14, 54), (26, 56), (37, 60), (40, 63), (56, 70), (61, 72), (11, 80), (16, 84),
    (77, 90), (49, 105), (13, 108), (10, 112), (21, 120), (82, 126), (86, 135), (112, 140),
    (11, 144), (18, 168), (109, 180), (5, 189), (28, 210), (157, 216), (75, 240), (124, 252),
    (248, 270), (42, 280), (124, 315), (66, 336), (181, 360), (248, 378), (289, 420), (59, 432),
    (502, 504), (301, 540), (462, 560), (169, 630), (464, 756), (378, 840), (32, 945),
    (409, 1008), (581, 1080), (589, 1260), (742, 1680), (410, 1890), (635, 2160), (1249, 2520),
    (409, 3780), (2929, 5040), (3542, 15120)]

/-- **A distinct covering system with minimum modulus 7 and moduli of lcm 15120.** There is a
distinct covering system, that is, a finite set of congruences $x \equiv r \pmod m$ with
$r \in \mathbb{Z}$, $m \in \mathbb{N}$ and no two with the same modulus, such that every
integer satisfies at least one of them, whose moduli are all at least $7$, include $7$, and have
least common multiple $15120$.

Source: Jonah Klein, *On a Conjecture of Krukenberg and a Problem of Dalton and Trifonov*,
INTEGERS 26 (2026), Article A38, Theorem 5 (`integers-2026-A38-thm-5`). -/
public theorem exists_distinct_covering_min_seven_lcm_15120 :
    ∃ classes : Finset (ℤ × ℕ), Int.IsCoveringSystem classes ∧
      Set.InjOn Prod.snd (classes : Set (ℤ × ℕ)) ∧ (∀ c ∈ classes, 7 ≤ c.2) ∧
      (∃ c ∈ classes, c.2 = 7) ∧ classes.lcm Prod.snd = 15120 := by
  let classes := (minSevenClasses.map fun c => ((c.1 : ℤ), c.2)).toFinset
  refine ⟨classes, ?_, Finset.card_image_iff.mp ?_, ?_, ?_, ?_⟩
  · exact TrifonovCovering.isCoveringSystem_of_coverMask_eq (L := 15120) (by decide)
      (by decide +kernel) (by decide +kernel)
  all_goals decide +kernel

end MetaMathlibExt
