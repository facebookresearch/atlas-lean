/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.SpecialFunctions.QPochhammer
public import MathlibExt.Combinatorics.Enumerative.Partition.Overpartition

/-!
# Congruences for `spt2‾(n)` (statements)

Statement-only targets from Robson da Silva, *Extending Congruences for the Number of Smallest Parts in Overpartitions with Smallest Part Even*, INTEGERS 26 (2026), Article A62.
`spt2‾(n)` is the number of smallest parts in the overpartitions of `n` whose smallest part is even
and not overlined, counted over the repo's `Nat.Overpartition`. The q-series dissections are
stated with `f_k = (q^k;q^k)_∞ = qPochhammerInfRaw (q^k) (q^k)` for complex `‖q‖ < 1`, with
Ramanujan's `ψ(q) = f_2^2/f_1`, `ψ(-q) = f_1 f_4/f_2`, `φ(-q) = f_1^2/f_2` substituted.
-/

namespace MetaMathlibExt

open QPochhammer

@[expose] public section

/-- Contribution of one overpartition to `spt2‾`: if its smallest part `s` is even and `s` is
not overlined, the number of copies of `s`; otherwise `0` (also for the empty overpartition).

Source: Robson da Silva, *Extending Congruences for the Number of Smallest Parts in Overpartitions with Smallest Part Even*, INTEGERS 26 (2026), Article A62, Section 1 (definition of `spt2‾(n)`). -/
public def overpartitionSpt2Contribution {n : ℕ} (O : Nat.Overpartition n) : ℕ :=
  if h : O.toPartition.parts.toFinset.Nonempty then
    let s := O.toPartition.parts.toFinset.min' h
    if Even s ∧ s ∉ O.overlines then O.toPartition.parts.count s else 0
  else
    0

/-- `spt2‾(n)`: the number of smallest parts in the overpartitions of `n` whose smallest part is
even and not overlined. The paper's example gives `spt2‾(4) = 3` (from `4` and `2 + 2`; `2̄ + 2`
does not count); the values for `n = 0, …, 8` are `0, 0, 1, 0, 3, 2, 6, 6, 15`.

Source: Robson da Silva, *Extending Congruences for the Number of Smallest Parts in Overpartitions with Smallest Part Even*, INTEGERS 26 (2026), Article A62, Section 1. -/
public def overpartitionSpt2 (n : ℕ) : ℕ :=
  ∑ O : Nat.Overpartition n, overpartitionSpt2Contribution O

/-- `spt2‾(0) = 0`: the empty overpartition has no smallest part.

Source: Robson da Silva, *Extending Congruences for the Number of Smallest Parts in Overpartitions with Smallest Part Even*, INTEGERS 26 (2026), Article A62, Section 1. -/
public theorem overpartitionSpt2_zero : overpartitionSpt2 0 = 0 := by
  refine Finset.sum_eq_zero fun O _ => ?_
  have h : O.toPartition.parts = 0 := by
    have := O.toPartition.parts_sum
    exact Multiset.eq_zero_of_forall_notMem fun a ha =>
      absurd (Multiset.le_sum_of_mem ha) (by have := O.toPartition.parts_pos ha; omega)
  simp [overpartitionSpt2Contribution]

/-- An overpartition whose smallest part is odd contributes nothing to `spt2‾`.

Source: Robson da Silva, *Extending Congruences for the Number of Smallest Parts in Overpartitions with Smallest Part Even*, INTEGERS 26 (2026), Article A62, Section 1. -/
public theorem overpartitionSpt2Contribution_eq_zero_of_odd {n : ℕ} (O : Nat.Overpartition n)
    (h : O.toPartition.parts.toFinset.Nonempty)
    (hodd : Odd (O.toPartition.parts.toFinset.min' h)) :
    overpartitionSpt2Contribution O = 0 := by
  simp [overpartitionSpt2Contribution, h, Nat.not_even_iff_odd.mpr hodd]

/--
For every natural `n`, the three clauses state respectively that
`overpartitionSpt2 (36 * n + 30)`, `overpartitionSpt2 (48 * n + 34)`, and
`overpartitionSpt2 (72 * n + 42)` have remainder zero modulo four. Natural-number remainder
equalities encode the paper's congruences; there is no other deviation.
Source: Robson da Silva, *Extending Congruences for the Number of Smallest Parts in
Overpartitions with Smallest Part Even*, INTEGERS 26 (2026), Article A62, Theorem 1.
-/
public theorem_wanted overpartitionSpt2_basic_congruences (n : ℕ) :
    overpartitionSpt2 (36 * n + 30) % 4 = 0 ∧
      overpartitionSpt2 (48 * n + 34) % 4 = 0 ∧
      overpartitionSpt2 (72 * n + 42) % 4 = 0

/--
For all natural `j` and `n`, the six clauses state the modulo-four vanishing of
`overpartitionSpt2` at, in order, `2^(j+4) n + 7·2^(j+1)`,
`2^(j+2)·9 n + 15·2^(j+1)`, `2^(j+4)·3 n + 17·2^(j+1)`,
`2^(j+3)·9 n + 21·2^(j+1)`, `2^(j+4)·5 n + 17·2^(j+1)`, and
`2^(j+4)·5 n + 33·2^(j+1)`. Natural-number remainder equalities encode congruence modulo
four; there is no other deviation.
Source: Robson da Silva, *Extending Congruences for the Number of Smallest Parts in
Overpartitions with Smallest Part Even*, INTEGERS 26 (2026), Article A62, Theorem 2.
-/
public theorem_wanted overpartitionSpt2_dyadic_congruences (j n : ℕ) :
    overpartitionSpt2 (2 ^ (j + 4) * n + 7 * 2 ^ (j + 1)) % 4 = 0 ∧
      overpartitionSpt2 (2 ^ (j + 2) * 9 * n + 15 * 2 ^ (j + 1)) % 4 = 0 ∧
      overpartitionSpt2 (2 ^ (j + 4) * 3 * n + 17 * 2 ^ (j + 1)) % 4 = 0 ∧
      overpartitionSpt2 (2 ^ (j + 3) * 9 * n + 21 * 2 ^ (j + 1)) % 4 = 0 ∧
      overpartitionSpt2 (2 ^ (j + 4) * 5 * n + 17 * 2 ^ (j + 1)) % 4 = 0 ∧
      overpartitionSpt2 (2 ^ (j + 4) * 5 * n + 33 * 2 ^ (j + 1)) % 4 = 0

/--
If `p` is prime, `3 < p`, and its remainder modulo eight is five or seven, then for every
natural `k` and `m` with `p ∤ m`, `overpartitionSpt2` at
`32 * p^(2*k+1) * m + 24 * p^(2*k+2)` has remainder zero modulo four. The paper's congruence
and nondivisibility are represented by natural-number remainder and divisibility predicates;
there is no other deviation.
Source: Robson da Silva, *Extending Congruences for the Number of Smallest Parts in
Overpartitions with Smallest Part Even*, INTEGERS 26 (2026), Article A62, Theorem 3.
-/
public theorem_wanted overpartitionSpt2_prime_congruence
    (p k m : ℕ) (hp : Nat.Prime p) (hp3 : 3 < p)
    (hp8 : p % 8 = 5 ∨ p % 8 = 7) (hm : ¬p ∣ m) :
    overpartitionSpt2 (32 * p ^ (2 * k + 1) * m + 24 * p ^ (2 * k + 2)) % 4 = 0

/--
For every complex `q` of norm less than one, this is the first 2-dissection:
`f₁² = f₂ f₈⁵/(f₄² f₁₆²) - 2q f₂ f₁₆²/f₈`. Every `f_k` is expanded as
`qPochhammerInfRaw (q ^ k) (q ^ k)`; this expansion is the only notational deviation.
Source: Robson da Silva, *Extending Congruences for the Number of Smallest Parts in
Overpartitions with Smallest Part Even*, INTEGERS 26 (2026), Article A62, Lemma 1.
-/
public theorem_wanted qPochhammer_two_dissection_square (q : ℂ) (hq : ‖q‖ < 1) :
    qPochhammerInfRaw q q ^ 2 =
      qPochhammerInfRaw (q ^ 2) (q ^ 2) *
          qPochhammerInfRaw (q ^ 8) (q ^ 8) ^ 5 /
        (qPochhammerInfRaw (q ^ 4) (q ^ 4) ^ 2 *
          qPochhammerInfRaw (q ^ 16) (q ^ 16) ^ 2) -
      2 * q * qPochhammerInfRaw (q ^ 2) (q ^ 2) *
          qPochhammerInfRaw (q ^ 16) (q ^ 16) ^ 2 /
        qPochhammerInfRaw (q ^ 8) (q ^ 8)

/--
For every complex `q` of norm less than one, this is the reciprocal-square 2-dissection:
`1/f₁² = f₈⁵/(f₂⁵ f₁₆²) + 2q f₄² f₁₆²/(f₂⁵ f₈)`. Every `f_k` is expanded as
`qPochhammerInfRaw (q ^ k) (q ^ k)`; this expansion is the only notational deviation.
Source: Robson da Silva, *Extending Congruences for the Number of Smallest Parts in
Overpartitions with Smallest Part Even*, INTEGERS 26 (2026), Article A62, Lemma 1.
-/
public theorem_wanted qPochhammer_two_dissection_inverse_square (q : ℂ) (hq : ‖q‖ < 1) :
    1 / qPochhammerInfRaw q q ^ 2 =
      qPochhammerInfRaw (q ^ 8) (q ^ 8) ^ 5 /
          (qPochhammerInfRaw (q ^ 2) (q ^ 2) ^ 5 *
            qPochhammerInfRaw (q ^ 16) (q ^ 16) ^ 2) +
        2 * q * qPochhammerInfRaw (q ^ 4) (q ^ 4) ^ 2 *
            qPochhammerInfRaw (q ^ 16) (q ^ 16) ^ 2 /
          (qPochhammerInfRaw (q ^ 2) (q ^ 2) ^ 5 *
            qPochhammerInfRaw (q ^ 8) (q ^ 8))

/--
For every complex `q` of norm less than one, this is the cubic 3-dissection:
`f₁³ = f₆ f₉⁶/(f₃ f₁₈³) + 4q³ f₃² f₁₈⁶/(f₆² f₉³) - 3q f₉³`. Every `f_k` is
expanded as `qPochhammerInfRaw (q ^ k) (q ^ k)`; this is the only notational deviation.
Source: Robson da Silva, *Extending Congruences for the Number of Smallest Parts in
Overpartitions with Smallest Part Even*, INTEGERS 26 (2026), Article A62, Lemma 2.
-/
public theorem_wanted qPochhammer_three_dissection_cube (q : ℂ) (hq : ‖q‖ < 1) :
    qPochhammerInfRaw q q ^ 3 =
      qPochhammerInfRaw (q ^ 6) (q ^ 6) *
          qPochhammerInfRaw (q ^ 9) (q ^ 9) ^ 6 /
        (qPochhammerInfRaw (q ^ 3) (q ^ 3) *
          qPochhammerInfRaw (q ^ 18) (q ^ 18) ^ 3) +
      4 * q ^ 3 * qPochhammerInfRaw (q ^ 3) (q ^ 3) ^ 2 *
          qPochhammerInfRaw (q ^ 18) (q ^ 18) ^ 6 /
        (qPochhammerInfRaw (q ^ 6) (q ^ 6) ^ 2 *
          qPochhammerInfRaw (q ^ 9) (q ^ 9) ^ 3) -
      3 * q * qPochhammerInfRaw (q ^ 9) (q ^ 9) ^ 3

/--
For every complex `q` of norm less than one, this 3-dissection states
`f₄/f₁ = f₁₂ f₁₈⁴/(f₃³ f₃₆²) + q f₆² f₉³ f₃₆/(f₃⁴ f₁₈²) +
2q² f₆ f₁₈ f₃₆/f₃³`. Every `f_k` is expanded as
`qPochhammerInfRaw (q ^ k) (q ^ k)`; this is the only notational deviation.
Source: Robson da Silva, *Extending Congruences for the Number of Smallest Parts in
Overpartitions with Smallest Part Even*, INTEGERS 26 (2026), Article A62, Lemma 2.
-/
public theorem_wanted qPochhammer_three_dissection_ratio_four_one (q : ℂ) (hq : ‖q‖ < 1) :
    qPochhammerInfRaw (q ^ 4) (q ^ 4) / qPochhammerInfRaw q q =
      qPochhammerInfRaw (q ^ 12) (q ^ 12) *
          qPochhammerInfRaw (q ^ 18) (q ^ 18) ^ 4 /
        (qPochhammerInfRaw (q ^ 3) (q ^ 3) ^ 3 *
          qPochhammerInfRaw (q ^ 36) (q ^ 36) ^ 2) +
      q * qPochhammerInfRaw (q ^ 6) (q ^ 6) ^ 2 *
          qPochhammerInfRaw (q ^ 9) (q ^ 9) ^ 3 *
          qPochhammerInfRaw (q ^ 36) (q ^ 36) /
        (qPochhammerInfRaw (q ^ 3) (q ^ 3) ^ 4 *
          qPochhammerInfRaw (q ^ 18) (q ^ 18) ^ 2) +
      2 * q ^ 2 * qPochhammerInfRaw (q ^ 6) (q ^ 6) *
          qPochhammerInfRaw (q ^ 18) (q ^ 18) *
          qPochhammerInfRaw (q ^ 36) (q ^ 36) /
        qPochhammerInfRaw (q ^ 3) (q ^ 3) ^ 3

/--
For every complex `q` of norm less than one, this 3-dissection states
`f₁ f₂ = f₆ f₉⁴/(f₃ f₁₈²) - q f₉ f₁₈ - 2q² f₃ f₁₈⁴/(f₆ f₉²)`. Every `f_k`
is expanded as `qPochhammerInfRaw (q ^ k) (q ^ k)`; this is the only notational deviation.
Source: Robson da Silva, *Extending Congruences for the Number of Smallest Parts in
Overpartitions with Smallest Part Even*, INTEGERS 26 (2026), Article A62, Lemma 2.
-/
public theorem_wanted qPochhammer_three_dissection_product_one_two (q : ℂ) (hq : ‖q‖ < 1) :
    qPochhammerInfRaw q q * qPochhammerInfRaw (q ^ 2) (q ^ 2) =
      qPochhammerInfRaw (q ^ 6) (q ^ 6) *
          qPochhammerInfRaw (q ^ 9) (q ^ 9) ^ 4 /
        (qPochhammerInfRaw (q ^ 3) (q ^ 3) *
          qPochhammerInfRaw (q ^ 18) (q ^ 18) ^ 2) -
      q * qPochhammerInfRaw (q ^ 9) (q ^ 9) *
          qPochhammerInfRaw (q ^ 18) (q ^ 18) -
      2 * q ^ 2 * qPochhammerInfRaw (q ^ 3) (q ^ 3) *
          qPochhammerInfRaw (q ^ 18) (q ^ 18) ^ 4 /
        (qPochhammerInfRaw (q ^ 6) (q ^ 6) *
          qPochhammerInfRaw (q ^ 9) (q ^ 9) ^ 2)

/--
For every complex `q` of norm less than one, the product form
`f₂²/f₁` of Ramanujan's `ψ(q)` equals `f₆ f₉²/(f₃ f₁₈) + q f₁₈²/f₉`.
Both the left-hand product substitution for `ψ` and every `f_k` expansion are explicit; these
are the only notational deviations.
Source: Robson da Silva, *Extending Congruences for the Number of Smallest Parts in
Overpartitions with Smallest Part Even*, INTEGERS 26 (2026), Article A62, Lemma 3.
-/
public theorem_wanted ramanujanPsi_three_dissection (q : ℂ) (hq : ‖q‖ < 1) :
    qPochhammerInfRaw (q ^ 2) (q ^ 2) ^ 2 / qPochhammerInfRaw q q =
      qPochhammerInfRaw (q ^ 6) (q ^ 6) *
          qPochhammerInfRaw (q ^ 9) (q ^ 9) ^ 2 /
        (qPochhammerInfRaw (q ^ 3) (q ^ 3) *
          qPochhammerInfRaw (q ^ 18) (q ^ 18)) +
      q * qPochhammerInfRaw (q ^ 18) (q ^ 18) ^ 2 /
        qPochhammerInfRaw (q ^ 9) (q ^ 9)

/--
For every complex `q` of norm less than one, the product form `f₁ f₄/f₂` of Ramanujan's
`ψ(-q)` equals `f₃ f₁₂ f₁₈⁵/(f₆² f₉² f₃₆²) - q f₉ f₃₆/f₁₈`.
Both the left-hand product substitution for `ψ(-q)` and every `f_k` expansion are explicit;
these are the only notational deviations.
Source: Robson da Silva, *Extending Congruences for the Number of Smallest Parts in
Overpartitions with Smallest Part Even*, INTEGERS 26 (2026), Article A62, Lemma 4.
-/
public theorem_wanted ramanujanPsi_neg_dissection (q : ℂ) (hq : ‖q‖ < 1) :
    qPochhammerInfRaw q q * qPochhammerInfRaw (q ^ 4) (q ^ 4) /
        qPochhammerInfRaw (q ^ 2) (q ^ 2) =
      qPochhammerInfRaw (q ^ 3) (q ^ 3) *
          qPochhammerInfRaw (q ^ 12) (q ^ 12) *
          qPochhammerInfRaw (q ^ 18) (q ^ 18) ^ 5 /
        (qPochhammerInfRaw (q ^ 6) (q ^ 6) ^ 2 *
          qPochhammerInfRaw (q ^ 9) (q ^ 9) ^ 2 *
          qPochhammerInfRaw (q ^ 36) (q ^ 36) ^ 2) -
      q * qPochhammerInfRaw (q ^ 9) (q ^ 9) *
          qPochhammerInfRaw (q ^ 36) (q ^ 36) /
        qPochhammerInfRaw (q ^ 18) (q ^ 18)

/--
For every complex `q` of norm less than one, the product form `f₁²/f₂` of Ramanujan's
`φ(-q)` equals `f₉²/f₁₈ - 2q f₃ f₁₈²/(f₆ f₉)`. Both the left-hand product substitution
for `φ(-q)` and every `f_k` expansion are explicit; these are the only notational deviations.
Source: Robson da Silva, *Extending Congruences for the Number of Smallest Parts in
Overpartitions with Smallest Part Even*, INTEGERS 26 (2026), Article A62, Lemma 5.
-/
public theorem_wanted ramanujanPhi_neg_dissection (q : ℂ) (hq : ‖q‖ < 1) :
    qPochhammerInfRaw q q ^ 2 / qPochhammerInfRaw (q ^ 2) (q ^ 2) =
      qPochhammerInfRaw (q ^ 9) (q ^ 9) ^ 2 /
          qPochhammerInfRaw (q ^ 18) (q ^ 18) -
        2 * q * qPochhammerInfRaw (q ^ 3) (q ^ 3) *
            qPochhammerInfRaw (q ^ 18) (q ^ 18) ^ 2 /
          (qPochhammerInfRaw (q ^ 6) (q ^ 6) *
            qPochhammerInfRaw (q ^ 9) (q ^ 9))

end

end MetaMathlibExt
