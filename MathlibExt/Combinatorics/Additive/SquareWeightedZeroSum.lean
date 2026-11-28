/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.PrimeFin
import Mathlib.FieldTheory.Finite.Basic
import MathlibExt.Combinatorics.Additive.ConsecutiveZeroSum

/-!
# Square-weighted zero sums modulo integers

For a natural number $n$, write $S(n)$ for the set of nonzero squares in $\mathbb{Z}/n\mathbb{Z}$
and $U(n)^2$ for the squares of its units. An $A$-weighted zero sum uses a weight from $A$ at
each term of a sequence; an $A$-weighted zero-sum subsequence uses weights at a nonempty set of
indices. In either case the weighted terms sum to zero. A consecutive weighted zero-sum
subsequence requires those indices to form an interval.

This file proves results of Paul and Paul. Lemma 5 counts the unit squares modulo a prime
power after scaling by an even power of the prime. For odd $n \ge 2$, Proposition 17 gives units
$u, v$ whose reductions modulo every prime $p$ dividing $n$ have no $S(p)$-weighted zero-sum
subsequence. Lemma 13 lifts a $U(p^2)^2$-weighted zero sum modulo $p^2$ to an $S(p^r)$-weighted
zero sum modulo $p^r$ when $p \ge 2$ and $r$ is positive and even; $p$ need not be prime.
Lemma 7 lifts an $S(p^r)$-weighted zero sum of the reduction modulo $p^r$, where $p^r$ exactly
divides $n$, to an $S(n)$-weighted zero sum modulo $n$. Corollary 8 uses this to bound the
consecutive constant $C_{S(n)}$ by $C_{S(p^r)}$ when $n \ge 2$, $p$ is a prime divisor of $n$,
and $r = v_p(n)$ is its full exponent in $n$.

## Main definitions

* `MetaMathlibExt.squareSet`: the nonzero squares of $\mathbb{Z}/n\mathbb{Z}$.
* `MetaMathlibExt.unitSquareSet`: the squares of units of $\mathbb{Z}/n\mathbb{Z}$.
* `MetaMathlibExt.HasWeightedZeroSum`: a sequence is an $A$-weighted zero sum.
* `MetaMathlibExt.HasWeightedZeroSumSubseq`: a sequence has an $A$-weighted zero-sum subsequence.
* `MetaMathlibExt.HasConsecutiveWeightedZeroSumSubseq`: such a subsequence occupies an interval.
* `MetaMathlibExt.weightedConsecutiveDefiningSet`: the positive lengths forcing such a block.
* `MetaMathlibExt.weightedConsecutiveConstant`: the least such length, or $0$ when none exists.

## Main results

* `MetaMathlibExt.ncard_scale_unitSquares_primePower`: Lemma 5.
* `MetaMathlibExt.exists_pair_units_avoiding_prime_squareWeights`: Proposition 17.
* `MetaMathlibExt.squareWeightedZeroSum_of_reduction_square`: Lemma 13.
* `MetaMathlibExt.squareWeightedZeroSum_of_primePower_reduction`: Lemma 7.
* `MetaMathlibExt.weightedConsecutiveConstant_squareSet_le_primePower`: Corollary 8.

## Implementation notes

As in the paper, the pair is assembled from one pair modulo each prime divisor by the Chinese
remainder theorem. Modulo an odd prime $p$ we take the pair $(1, c_p)$, where $-c_p$ is not a
square: a single nonzero term has no weighted zero sum, and $a \cdot 1 + b c_p = 0$ with nonzero
squares $a, b$ would make $-c_p = a / b$ a square. So $u = 1$, and $v$ is congruent to $c_p$
modulo every prime $p \mid n$.

For the lifting lemma, lift the unit square roots and scale their squares by $p^{r-2}$.
The even exponent makes this scale a square; multiplying by it lifts the zero-sum congruence
from modulo $p^2$ to modulo $p^r$ without making any weight zero.

For the prime-power component, write $n = p^r m$ with $p^r$ and $m$ coprime and take $e$ with
$e \equiv 1 \pmod{p^r}$ and $e \equiv 0 \pmod m$. If $b_i = c_i^2$, the weights $(e c_i)^2$ reduce
to $b_i$ modulo $p^r$ and to $0$ modulo $m$, so the weighted sum vanishes modulo both factors.

For Corollary 8, the prime-power defining set is nonempty: among $p^r$ terms there is a
nonempty consecutive ordinary zero sum, and $1$ is a nonzero square because $p^r > 1$. At the
least forcing length, apply Lemma 7 to the terms indexed by a zero-sum block in the reduction,
keeping that block of indices unchanged.

## References

* Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
  Sequences 27 (2024), Article 24.6.6, pp. 1–16, Introduction (Remark 1) and Corollary 8
  (pp. 4–5), using Lemma 7 and Observation 2; arXiv:2202.13143.
* Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants of
  $\mathbb{Z}_n$*, INTEGERS 24 (2024), Article A38, pp. 1–16, Theorem 3.1. Its upper bound
  is also credited there to the same authors, *On a different weighted zero-sum constant*,
  Discrete Mathematics 346 (2023), Article 113350, Theorem 1.
* The unweighted block existence is reused from `consecutive_constant_eq_card` in
  `MathlibExt.Combinatorics.Additive.ConsecutiveZeroSum`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Nonzero squares modulo $n$.** For a natural number $n$, $S(n)$ is the set of elements $x$
of $\mathbb{Z}_n = \mathbb{Z}/n\mathbb{Z}$ with $x \neq 0$ and $x = y^2$ for some
$y \in \mathbb{Z}_n$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Introduction. -/
public def squareSet (n : ℕ) : Set (ZMod n) := {x | x ≠ 0 ∧ ∃ y, x = y ^ 2}

/-- **Weighted zero-sum subsequences.** Let $A \subseteq \mathbb{Z}/n\mathbb{Z}$ and let
$S = (x_1, \dots, x_k)$ be a sequence in $\mathbb{Z}/n\mathbb{Z}$. Then $S$ has an $A$-weighted
zero-sum subsequence if there are a nonempty set $J \subseteq \{1, \dots, k\}$ of indices and
weights $a_i \in A$ for $i \in J$ with $\sum_{i \in J} a_i x_i = 0$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Introduction. -/
public def HasWeightedZeroSumSubseq {n k : ℕ} (A : Set (ZMod n))
    (S : Fin k → ZMod n) : Prop :=
  ∃ J : Finset (Fin k), J.Nonempty ∧
    ∃ a : Fin k → ZMod n, (∀ i ∈ J, a i ∈ A) ∧ ∑ i ∈ J, a i * S i = 0

/-- **Squares of units modulo n.** For a natural number $n$, $U(n)^2$ is the set of elements of
$\mathbb{Z}/n\mathbb{Z}$ of the form $u^2$ with $u$ a unit of $\mathbb{Z}/n\mathbb{Z}$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Introduction. -/
public def unitSquareSet (n : ℕ) : Set (ZMod n) := {x | ∃ u, IsUnit u ∧ x = u ^ 2}

/-- **Weighted zero-sum sequences.** Let $A \subseteq \mathbb{Z}/n\mathbb{Z}$ and let
$S = (x_1, \dots, x_k)$ be a sequence in $\mathbb{Z}/n\mathbb{Z}$. Then $S$ is an $A$-weighted
zero-sum sequence if there are weights $a_1, \dots, a_k \in A$ with
$a_1 x_1 + a_2 x_2 + \dots + a_k x_k = 0$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Introduction. -/
public def HasWeightedZeroSum {n k : ℕ} (A : Set (ZMod n)) (S : Fin k → ZMod n) : Prop :=
  ∃ a : Fin k → ZMod n, (∀ i, a i ∈ A) ∧ ∑ i, a i * S i = 0

/-- **Consecutive weighted zero-sum subsequences.** Let $A \subseteq \mathbb{Z}/n\mathbb{Z}$ and let
$S = (x_1, \dots, x_k)$ be a sequence in $\mathbb{Z}/n\mathbb{Z}$. Then $S$ has an $A$-weighted
zero-sum consecutive subsequence if there are indices $1 \le l \le h \le k$ and weights
$a_l, \dots, a_h \in A$ with $\sum_{i=l}^{h} a_i x_i = 0$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Introduction. -/
public def HasConsecutiveWeightedZeroSumSubseq {n k : ℕ} (A : Set (ZMod n))
    (S : Fin k → ZMod n) : Prop :=
  ∃ J : Finset (Fin k), J.Nonempty ∧
    (∃ lo hi : ℕ, J = Finset.univ.filter fun i => lo ≤ i.1 ∧ i.1 ≤ hi) ∧
    ∃ a : Fin k → ZMod n, (∀ i ∈ J, a i ∈ A) ∧ ∑ i ∈ J, a i * S i = 0

/-- **Lengths forcing a consecutive weighted zero sum.** Let $n$ be a natural number and $A$ a
subset of $\mathbb{Z}_n = \mathbb{Z}/n\mathbb{Z}$. This is the set of positive integers $k$ such
that every sequence $(x_1, \dots, x_k)$ of elements of $\mathbb{Z}_n$ has a nonempty block of
consecutive terms $x_i, \dots, x_j$ with weights $a_i, \dots, a_j \in A$ such that
$a_i x_i + \dots + a_j x_j = 0$. Its least element, or $0$ when it is empty, is the $A$-weighted
consecutive constant $C_A$ of $\mathbb{Z}_n$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Introduction. -/
public def weightedConsecutiveDefiningSet (n : ℕ) (A : Set (ZMod n)) : Set ℕ :=
  {k | 0 < k ∧ ∀ S : Fin k → ZMod n, HasConsecutiveWeightedZeroSumSubseq A S}

/-- **Weighted consecutive zero-sum constant.** Let $n$ be a natural number and $A$ a subset of
$\mathbb{Z}_n = \mathbb{Z}/n\mathbb{Z}$. The $A$-weighted consecutive constant $C_A$ of
$\mathbb{Z}_n$ is the least positive integer $k$ such that every sequence $(x_1, \dots, x_k)$ of
elements of $\mathbb{Z}_n$ has a nonempty block of consecutive terms $x_i, \dots, x_j$ with
weights $a_i, \dots, a_j \in A$ such that $a_i x_i + \dots + a_j x_j = 0$; it is $0$ when no
such $k$ exists.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Introduction. -/
public noncomputable def weightedConsecutiveConstant (n : ℕ) (A : Set (ZMod n)) : ℕ :=
  sInf (weightedConsecutiveDefiningSet n A)

end

/-- Modulo an odd prime $p$, some natural number $c$ has $-c$ not a square. -/
private lemma exists_natCast_neg_not_isSquare {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ c : ℕ, ¬IsSquare (-(c : ZMod p)) := by
  have := Fact.mk hp
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare ((ZMod.ringChar_zmod_n p).trans_ne hp2)
  refine ⟨(-a).val, ?_⟩
  rwa [ZMod.natCast_zmod_val, neg_neg]

/-- Modulo a prime $p$, if $-c$ is not a square, then the pair $(1, c)$ has no $S(p)$-weighted
zero-sum subsequence. -/
private lemma not_hasWeightedZeroSumSubseq_one_pair {p : ℕ} [Fact p.Prime] {c : ZMod p}
    (hc : ¬IsSquare (-c)) : ¬HasWeightedZeroSumSubseq (squareSet p) ![1, c] := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc ⟨0, by simp⟩
  rintro ⟨J, ⟨j, hj⟩, a, ha, hsum⟩
  rw [← Finset.univ_inter J, ← Finset.sum_ite_mem, Fin.sum_univ_two] at hsum
  by_cases h0 : (0 : Fin 2) ∈ J <;> by_cases h1 : (1 : Fin 2) ∈ J
  · -- Both terms: `y ^ 2 + z ^ 2 * c = 0` with `z ≠ 0` makes `-c = (y / z) ^ 2` a square.
    obtain ⟨-, y, hy⟩ := ha 0 h0
    obtain ⟨ha1, z, hz⟩ := ha 1 h1
    have hz0 : z ≠ 0 := by
      rintro rfl
      simp [hz] at ha1
    simp only [h0, h1, ite_true, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, hy, hz]
      at hsum
    refine hc ⟨y / z, ?_⟩
    field_simp
    linear_combination -hsum
  · -- Only the first term: its weight would vanish.
    obtain ⟨ha0, -⟩ := ha 0 h0
    simp only [h0, h1, ite_true, ite_false, Matrix.cons_val_zero, mul_one, add_zero] at hsum
    exact ha0 hsum
  · -- Only the second term: a product of two nonzero elements of a field would vanish.
    obtain ⟨ha1, -⟩ := ha 1 h1
    simp only [h0, h1, ite_true, ite_false, Matrix.cons_val_one, zero_add] at hsum
    exact mul_ne_zero ha1 hc0 hsum
  · -- No term: the index set would be empty.
    fin_cases j <;> simp_all

/-- **Two units without square-weighted zero sums modulo any prime divisor.** Let $n \ge 2$ be
odd, and write $S(m)$ for the set of nonzero squares in $\mathbb{Z}/m\mathbb{Z}$. Then there are
units $u, v$ of $\mathbb{Z}/n\mathbb{Z}$ such that for every prime $p$ dividing $n$, the sequence
$(u \bmod p, v \bmod p)$ in $\mathbb{Z}/p\mathbb{Z}$ has no $S(p)$-weighted zero-sum subsequence.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Proposition 17. -/
public theorem exists_pair_units_avoiding_prime_squareWeights (n : ℕ)
    (hn : 2 ≤ n) (hnOdd : Odd n) :
    ∃ u v : ZMod n, IsUnit u ∧ IsUnit v ∧
      ∀ p : ℕ, p.Prime → p ∣ n →
        ¬HasWeightedZeroSumSubseq (squareSet p)
          (fun i : Fin 2 => (ZMod.cast (![u, v] i) : ZMod p)) := by
  have hn0 : n ≠ 0 := by omega
  -- Every prime factor `p` of `n` is odd, so some `c p` has `-c p` not a square modulo `p`.
  have hodd : ∀ p ∈ n.primeFactors, p ≠ 2 := by
    rintro p hp rfl
    exact Nat.not_even_iff_odd.mpr hnOdd (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hp))
  choose! c hc using fun p (hp : p ∈ n.primeFactors) =>
    exists_natCast_neg_not_isSquare (Nat.prime_of_mem_primeFactors hp) (hodd p hp)
  -- The Chinese remainder theorem gives `k` with `k ≡ c p [MOD p]` for every prime factor `p`.
  obtain ⟨k, hk⟩ := Nat.chineseRemainderOfFinset c id n.primeFactors
    (fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero)
    (fun p hp q hq hpq => (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr hpq)
  have hkp : ∀ p ∈ n.primeFactors, (k : ZMod p) = c p := fun p hp =>
    (ZMod.natCast_eq_natCast_iff k (c p) p).mpr (hk p hp)
  refine ⟨1, k, isUnit_one, (ZMod.isUnit_iff_coprime k n).mpr ?_, fun p hp hpn => ?_⟩
  · -- A common prime factor `q` of `k` and `n` would make `-c q ≡ -k ≡ 0` a square modulo `q`.
    refine Nat.coprime_of_dvd fun q hq hqk hqn => ?_
    have hqmem : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqn, hn0⟩
    apply hc q hqmem
    rw [← hkp q hqmem, (ZMod.natCast_eq_zero_iff k q).mpr hqk, neg_zero]
    exact ⟨0, by simp⟩
  · -- Modulo `p` the pair is `(1, c p)`.
    have := Fact.mk hp
    have hpmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, hn0⟩
    have hS : (fun i : Fin 2 => (ZMod.cast (![(1 : ZMod n), (k : ZMod n)] i) : ZMod p)) =
        ![1, (c p : ZMod p)] := by
      funext i
      fin_cases i
      · simp [ZMod.cast_one hpn]
      · simp [ZMod.cast_natCast hpn, hkp p hpmem]
    rw [hS]
    exact not_hasWeightedZeroSumSubseq_one_pair (hc p hpmem)

/-- **Lifting weighted zero sums from p² to an even power of p.** Let $p \ge 2$, $r \ne 0$
and $k$ be natural numbers with $r$ even, and let $t_1, \dots, t_k$ be elements of
$\mathbb{Z}/p^r\mathbb{Z}$, with reductions $\bar t_1, \dots, \bar t_k$ modulo $p^2$. Write
$U(p^2)^2$ for the set of squares of units of $\mathbb{Z}/p^2\mathbb{Z}$ and $S(p^r)$ for the
set of nonzero squares of $\mathbb{Z}/p^r\mathbb{Z}$. If there are
$a_1, \dots, a_k \in U(p^2)^2$ with $a_1 \bar t_1 + \dots + a_k \bar t_k = 0$ in
$\mathbb{Z}/p^2\mathbb{Z}$, then there are $b_1, \dots, b_k \in S(p^r)$ with
$b_1 t_1 + \dots + b_k t_k = 0$ in $\mathbb{Z}/p^r\mathbb{Z}$.

The arXiv preprint states $p > 0$, but the published lemma assumes $p \ge 2$, as in this
statement. The restriction matters: if $p = 1$ and $k > 0$, the only residue is a unit and
its square is $0$, so the hypothesis holds but there are no nonzero square weights.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Lemma 13. -/
public theorem squareWeightedZeroSum_of_reduction_square (p r k : ℕ)
    (hp : 2 ≤ p) (hr0 : r ≠ 0) (hrEven : Even r)
    (T : Fin k → ZMod (p ^ r))
    (hT : HasWeightedZeroSum (unitSquareSet (p ^ 2))
      (fun i => (ZMod.cast (T i) : ZMod (p ^ 2)))) :
    HasWeightedZeroSum (squareSet (p ^ r)) T := by
  obtain ⟨j, hj⟩ : ∃ j : ℕ, r = 2 * j + 2 := by
    obtain ⟨t, ht⟩ := hrEven
    exact ⟨t - 1, by omega⟩
  subst r
  have hp0 : 0 < p := by omega
  have hm : 1 < p ^ 2 := one_lt_pow₀ (by omega : 1 < p) (by decide)
  have : Fact (1 < p ^ 2) := ⟨hm⟩
  have : NeZero (p ^ 2) := ⟨by omega⟩
  have : NeZero (p ^ (2 * j + 2)) := ⟨(pow_pos hp0 _).ne'⟩
  let d := p ^ (2 * j)
  have hd : 0 < d := pow_pos hp0 _
  have hmod : p ^ (2 * j + 2) = d * p ^ 2 := pow_add p _ _
  obtain ⟨a, ha, hsum⟩ := hT
  choose u hu heq using ha
  let z := ∑ i : Fin k, (u i).val ^ 2 * (T i).val
  have hz : (z : ZMod (p ^ 2)) = 0 := by
    rw [← hsum]
    simp only [z, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, ZMod.natCast_zmod_val,
      ZMod.cast_eq_val, heq]
  -- Scaling by d transports the divisibility of the sum to modulus d * p².
  have hdz : ((d * z : ℕ) : ZMod (p ^ (2 * j + 2))) = 0 := by
    apply (ZMod.natCast_eq_zero_iff _ _).mpr
    rw [hmod]
    exact Nat.mul_dvd_mul_left d ((ZMod.natCast_eq_zero_iff z _).mp hz)
  refine ⟨fun i => (d : ZMod (p ^ (2 * j + 2))) * ((u i).val : ZMod _) ^ 2, ?_, ?_⟩
  · intro i
    refine ⟨?_, ⟨(p : ZMod (p ^ (2 * j + 2))) ^ j * ((u i).val : ZMod _), ?_⟩⟩
    · intro he
      have he' : ((d * (u i).val ^ 2 : ℕ) : ZMod (p ^ (2 * j + 2))) = 0 := by
        push_cast
        exact he
      have hbig := (ZMod.natCast_eq_zero_iff _ (p ^ (2 * j + 2))).mp he'
      rw [hmod] at hbig
      have hsmall := (ZMod.natCast_eq_zero_iff ((u i).val ^ 2) (p ^ 2)).mpr
        (Nat.dvd_of_mul_dvd_mul_left hd hbig)
      exact ((hu i).pow 2).ne_zero
        (by simpa only [Nat.cast_pow, ZMod.natCast_zmod_val] using hsmall)
    · rw [mul_pow, ← pow_mul]
      simp [d, Nat.mul_comm]
  · simpa only [z, Nat.cast_mul, Nat.cast_sum, Nat.cast_pow, ZMod.natCast_zmod_val,
      Finset.mul_sum, ← mul_assoc] using hdz

open scoped Pointwise in
/-- **Scaled unit squares modulo a prime power.** Let $p$ be a prime and $r, k$ natural numbers
with $k = 0$ or $2k < r$, and write $U(m)^2$ for the set of squares of units of
$\mathbb{Z}/m\mathbb{Z}$. Then the set $p^{2k} U(p^r)^2 = \{p^{2k} x : x \in U(p^r)^2\}$ in
$\mathbb{Z}/p^r\mathbb{Z}$ has the same number of elements as $U(p^{r-2k})^2$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Lemma 5. -/
public theorem ncard_scale_unitSquares_primePower (p r k : ℕ) (hp : p.Prime)
    (hk : k ≤ (r - 1) / 2) :
    (((p : ZMod (p ^ r)) ^ (2 * k)) • unitSquareSet (p ^ r)).ncard =
      (unitSquareSet (p ^ (r - 2 * k))).ncard := by
  by_cases hk0 : k = 0
  · subst k
    simp
  have hr : 2 * k < r := by omega
  let d := p ^ (2 * k)
  let q := p ^ (r - 2 * k)
  have hmod : p ^ r = d * q := by
    dsimp [d, q]
    rw [← pow_add, Nat.add_sub_of_le hr.le]
  have hd : 0 < d := pow_pos hp.pos _
  have : NeZero q := ⟨(pow_pos hp.pos (r - 2 * k)).ne'⟩
  have : NeZero (p ^ r) := ⟨(pow_pos hp.pos r).ne'⟩
  let f : ZMod q → ZMod (p ^ r) := fun x => (d * x.val : ℕ)
  -- Multiplying canonical representatives by d embeds the smaller residue set.
  have hfval (x : ZMod q) : (f x).val = d * x.val := by
    apply ZMod.val_natCast_of_lt
    rw [hmod]
    exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt x) hd
  have hf : Function.Injective f := by
    intro x y h
    apply ZMod.val_injective q
    apply Nat.eq_of_mul_eq_mul_left hd
    simpa only [hfval] using congrArg ZMod.val h
  have hf_cast (a : ℕ) : f (a : ZMod q) = (d : ZMod (p ^ r)) * (a : ZMod (p ^ r)) := by
    apply ZMod.val_injective (p ^ r)
    calc
      (f (a : ZMod q)).val = d * (a % q) := by rw [hfval, ZMod.val_natCast]
      _ = (d * a) % p ^ r := by rw [hmod, Nat.mul_mod_mul_left]
      _ = ((d : ZMod (p ^ r)) * (a : ZMod (p ^ r))).val := by
        rw [← Nat.cast_mul, ZMod.val_natCast]
  have hf_sq (a : ℕ) : f ((a : ZMod q) ^ 2) =
      ((p : ZMod (p ^ r)) ^ (2 * k)) * (a : ZMod (p ^ r)) ^ 2 := by
    have hqpow : ((a ^ 2 : ℕ) : ZMod q) = (a : ZMod q) ^ 2 := Nat.cast_pow a 2
    have hppow : ((a ^ 2 : ℕ) : ZMod (p ^ r)) = (a : ZMod (p ^ r)) ^ 2 := Nat.cast_pow a 2
    have hdpow : (d : ZMod (p ^ r)) = (p : ZMod (p ^ r)) ^ (2 * k) := Nat.cast_pow p (2 * k)
    rw [← hqpow, ← hppow, ← hdpow]
    exact hf_cast (a ^ 2)
  -- Both exponents are positive, so the same representatives are units in either modulus.
  have hunit (a : ℕ) : IsUnit (a : ZMod (p ^ r)) ↔ IsUnit (a : ZMod q) := by
    change IsUnit (a : ZMod (p ^ r)) ↔ IsUnit (a : ZMod (p ^ (r - 2 * k)))
    simp only [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (by omega : 0 < r),
      Nat.coprime_pow_right_iff (by omega : 0 < r - 2 * k)]
  have himage : ((p : ZMod (p ^ r)) ^ (2 * k)) • unitSquareSet (p ^ r) = f '' unitSquareSet q := by
    ext y
    rw [Set.mem_smul_set, Set.mem_image]
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      have huq : IsUnit (u.val : ZMod q) :=
        (hunit u.val).mp (by simpa only [ZMod.natCast_zmod_val] using hu)
      refine ⟨(u.val : ZMod q) ^ 2, ⟨(u.val : ZMod q), huq, rfl⟩, ?_⟩
      simpa only [ZMod.natCast_zmod_val, smul_eq_mul] using hf_sq u.val
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      have hup : IsUnit (u.val : ZMod (p ^ r)) :=
        (hunit u.val).mpr (by simpa only [ZMod.natCast_zmod_val] using hu)
      refine ⟨(u.val : ZMod (p ^ r)) ^ 2, ⟨(u.val : ZMod (p ^ r)), hup, rfl⟩, ?_⟩
      simpa only [ZMod.natCast_zmod_val, smul_eq_mul] using (hf_sq u.val).symm
  rw [himage]
  exact Set.ncard_image_of_injective _ hf

-- The exponent hypothesis alone gives the coprime splitting `n = p ^ r * m`; `hpn` is redundant.
set_option linter.unusedVariables false in
/-- **Square-weighted zero sums lift from a prime-power component.** Let $n \ge 2$, let $p$ be a
prime dividing $n$, and let $r$ be the exponent of $p$ in $n$. Write $S(m)$ for the set of
nonzero squares in $\mathbb{Z}_m$. Let $x_1, \dots, x_k$ be a sequence in $\mathbb{Z}_n$ whose
reduction $\bar x_1, \dots, \bar x_k$ modulo $p^r$ has an $S(p^r)$-weighted zero sum, that is,
there are $b_1, \dots, b_k \in S(p^r)$ with $\sum_i b_i \bar x_i = 0$. Then there are
$a_1, \dots, a_k \in S(n)$ with $\sum_i a_i x_i = 0$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Lemma 7. -/
public theorem squareWeightedZeroSum_of_primePower_reduction (n p r k : ℕ)
    (hn : 2 ≤ n) (hp : p.Prime) (hpn : p ∣ n) (hval : n.factorization p = r)
    (S : Fin k → ZMod n)
    (hS : HasWeightedZeroSum (squareSet (p ^ r))
      (fun i => (ZMod.cast (S i) : ZMod (p ^ r)))) :
    HasWeightedZeroSum (squareSet n) S := by
  have hn0 : n ≠ 0 := by omega
  have : NeZero n := ⟨hn0⟩
  have : NeZero (p ^ r) := ⟨(pow_pos hp.pos r).ne'⟩
  -- Split `n = p ^ r * m` with `p ^ r` and `m` coprime.
  set m := n / p ^ r with hm
  have hqm : p ^ r * m = n := by
    rw [hm, ← hval]
    exact Nat.ordProj_mul_ordCompl_eq_self n p
  have hco : (p ^ r).Coprime m := by
    rw [hm, ← hval]
    exact (Nat.coprime_ordCompl hp hn0).pow_left _
  have hqn : p ^ r ∣ n := ⟨m, hqm.symm⟩
  -- The Chinese remainder theorem gives `e ≡ 1 [MOD p ^ r]` and `e ≡ 0 [MOD m]`.
  obtain ⟨e, he1, he0⟩ := Nat.chineseRemainder hco 1 0
  have he1' : (e : ZMod (p ^ r)) = 1 := by
    simpa using (ZMod.natCast_eq_natCast_iff e 1 (p ^ r)).mpr he1
  have hme : m ∣ e := Nat.modEq_zero_iff_dvd.mp he0
  obtain ⟨b, hb, hsum⟩ := hS
  choose hb0 c hc using hb
  -- The weight `a i = (e c_i) ^ 2` reduces to `b i` modulo `p ^ r` and to `0` modulo `m`.
  have hred (i : Fin k) :
      (ZMod.cast (((e * (c i).val : ℕ) : ZMod n) ^ 2) : ZMod (p ^ r)) = b i := by
    rw [ZMod.cast_pow hqn, ZMod.cast_natCast hqn, Nat.cast_mul, he1', one_mul,
      ZMod.natCast_zmod_val, hc]
  refine ⟨fun i => ((e * (c i).val : ℕ) : ZMod n) ^ 2, fun i => ⟨fun h => hb0 i ?_, _, rfl⟩, ?_⟩
  · rw [← hred i, show ((e * (c i).val : ℕ) : ZMod n) ^ 2 = 0 from h, ZMod.cast_zero]
  · let Y : ℕ := ∑ i, (e * (c i).val) ^ 2 * (S i).val
    have hY : ∑ i, ((e * (c i).val : ℕ) : ZMod n) ^ 2 * S i = (Y : ZMod n) := by
      simp only [Y, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, ZMod.natCast_zmod_val]
    rw [hY, ZMod.natCast_eq_zero_iff, ← hqm]
    refine hco.mul_dvd_of_dvd_of_dvd ?_ ?_
    · rw [← ZMod.natCast_eq_zero_iff, ← hsum]
      simp only [Y, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, he1', one_mul, ZMod.natCast_val,
        ZMod.cast_id', id, hc]
    · exact Finset.dvd_sum fun i _ =>
        Dvd.dvd.mul_right (Dvd.dvd.pow (hme.mul_right _) two_ne_zero) _

/-- **Membership in the nonzero square weights.** For a natural number $n$ and
$x \in \mathbb{Z}/n\mathbb{Z}$, $x \in S(n)$ if and only if $x \ne 0$ and
$x = y^2$ for some $y \in \mathbb{Z}/n\mathbb{Z}$. -/
public theorem mem_squareSet_iff {n : ℕ} {x : ZMod n} :
    x ∈ squareSet n ↔ x ≠ 0 ∧ ∃ y : ZMod n, x = y ^ 2 := Iff.rfl

/-- **Consecutive weighted zero sums as closed intervals.** Let $A \subseteq \mathbb{Z}_n$ and
let $S = (x_0, \ldots, x_{k-1})$ be a sequence in $\mathbb{Z}_n$. Then $S$ has an $A$-weighted
consecutive zero-sum subsequence if and only if there are $0 \le s \le t < k$ and weights
$a_i \in A$ for $s \le i \le t$ such that $\sum_{i=s}^t a_i x_i = 0$. -/
public theorem hasConsecutiveWeightedZeroSumSubseq_iff {n k : ℕ} {A : Set (ZMod n)}
    {S : Fin k → ZMod n} :
    HasConsecutiveWeightedZeroSumSubseq A S ↔
      ∃ s t : Fin k, s ≤ t ∧
        ∃ a : Fin k → ZMod n, (∀ i ∈ Finset.Icc s t, a i ∈ A) ∧
          ∑ i ∈ Finset.Icc s t, a i * S i = 0 := by
  constructor
  · rintro ⟨J, hJ, ⟨lo, hi, hI⟩, a, ha, hsum⟩
    let s := J.min' hJ
    let t := J.max' hJ
    have hs : s ∈ J := J.min'_mem hJ
    have ht : t ∈ J := J.max'_mem hJ
    have heq : J = Finset.Icc s t := by
      ext i
      rw [Finset.mem_Icc]
      refine ⟨fun hi' => ⟨J.min'_le i hi', J.le_max' i hi'⟩, ?_⟩
      rintro ⟨hsi, hit⟩
      rw [hI] at hs ht ⊢
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ht ⊢
      exact ⟨Nat.le_trans hs.1 hsi, Nat.le_trans hit ht.2⟩
    exact ⟨s, t, J.le_max' s hs, a, heq ▸ ha, heq ▸ hsum⟩
  · rintro ⟨s, t, hst, a, ha, hsum⟩
    refine ⟨Finset.Icc s t, ⟨s, Finset.mem_Icc.mpr ⟨le_rfl, hst⟩⟩, ⟨s, t, ?_⟩, a, ha, hsum⟩
    ext i
    simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]

/-- **Membership in the set of consecutive forcing lengths.** For $A \subseteq \mathbb{Z}_n$,
$k$ lies in the defining set of $C_A$ if and only if $k > 0$ and every sequence
$x_0, \dots, x_{k-1}$ in $\mathbb{Z}_n$ has an $A$-weighted consecutive zero-sum subsequence. -/
public theorem mem_weightedConsecutiveDefiningSet {n k : ℕ} {A : Set (ZMod n)} :
    k ∈ weightedConsecutiveDefiningSet n A ↔
      0 < k ∧ ∀ S : Fin k → ZMod n, HasConsecutiveWeightedZeroSumSubseq A S := Iff.rfl

/-- **Characterization of a positive weighted consecutive constant.** Let $A \subseteq \mathbb{Z}_n$
and $k > 0$. Then $C_A = k$ if and only if $k$ is the least element of the set of positive
lengths at which every sequence in $\mathbb{Z}_n$ has an $A$-weighted consecutive zero-sum
subsequence. -/
public theorem weightedConsecutiveConstant_eq_iff_isLeast {n k : ℕ} {A : Set (ZMod n)}
    (hk : 0 < k) :
    weightedConsecutiveConstant n A = k ↔ IsLeast (weightedConsecutiveDefiningSet n A) k := by
  unfold weightedConsecutiveConstant
  refine ⟨fun h => ?_, fun h => h.csInf_eq⟩
  subst k
  refine ⟨Nat.sInf_mem ?_, fun _ hj => Nat.sInf_le hj⟩
  by_contra! hempty
  rw [hempty, Nat.sInf_empty] at hk
  exact (lt_irrefl 0) hk

private theorem weightedConsecutiveDefiningSet_squareSet_nonempty {n : ℕ} (hn : 1 < n) :
    (weightedConsecutiveDefiningSet n (squareSet n)).Nonempty := by
  have : NeZero n := ⟨by omega⟩
  have h := (consecutive_constant_eq_card (ZMod n)).1
  rw [Set.mem_ofPred_eq, ZMod.card] at h
  refine ⟨n, mem_weightedConsecutiveDefiningSet.mpr ⟨h.1, fun S => ?_⟩⟩
  obtain ⟨s, t, hst, a, ha, hsum⟩ := h.2 S
  refine hasConsecutiveWeightedZeroSumSubseq_iff.mpr ⟨s, t, hst, fun _ => 1, ?_, ?_⟩
  · exact fun _ _ => ⟨fun hzero => hn.ne' (ZMod.one_eq_zero_iff.mp hzero), 1, by simp⟩
  · simp only [one_mul]
    exact (Finset.sum_congr rfl fun i hi => by
      rw [Set.mem_singleton_iff.mp (ha i hi), one_zsmul]).symm.trans hsum

private theorem hasConsecutiveWeightedZeroSumSubseq_of_primePower_reduction {n p r k : ℕ}
    (hn : 2 ≤ n) (hp : p.Prime) (hpn : p ∣ n) (hval : n.factorization p = r)
    {S : Fin k → ZMod n}
    (h : HasConsecutiveWeightedZeroSumSubseq (squareSet (p ^ r))
      (fun i => (ZMod.cast (S i) : ZMod (p ^ r)))) :
    HasConsecutiveWeightedZeroSumSubseq (squareSet n) S := by
  obtain ⟨J, hJ, hI, b, hb, hsum⟩ := h
  -- Reindex only the chosen block to apply the whole-sequence lifting lemma.
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  have sum_reindex {m : ℕ} (f : Fin k → ZMod m) :
      ∑ i, f (e i) = ∑ i ∈ J, f i :=
    (e.sum_comp (fun j => f j)).trans (Finset.sum_coe_sort J f)
  obtain ⟨a, ha, hsum'⟩ := squareWeightedZeroSum_of_primePower_reduction n p r _ hn hp hpn hval
    (fun i => S (e i)) ⟨fun i => b (e i), fun i => hb _ (e i).property,
      (sum_reindex _).trans hsum⟩
  -- Transport the lifted weights back to the original positions.
  let w (i : Fin k) : ZMod n := if h : i ∈ J then a (e.symm ⟨i, h⟩) else 0
  have hw (i : Fin (Fintype.card J)) : w (e i) = a i := by simp [w]
  refine ⟨J, hJ, hI, w, ?_, ?_⟩
  · intro i hi
    simpa [w, hi] using ha (e.symm ⟨i, hi⟩)
  · rw [← sum_reindex]
    simpa only [hw] using hsum'

/-- **Prime-power bound for the square-weighted consecutive constant.** Let $n \ge 2$, let $p$ be a
prime dividing $n$ and let $r = v_p(n)$ be the exponent of $p$ in $n$. For a natural number $m$,
write $S(m)$ for the set of nonzero squares in $\mathbb{Z}_m = \mathbb{Z}/m\mathbb{Z}$ and
$C_{S(m)}$ for the $S(m)$-weighted consecutive constant of $\mathbb{Z}_m$. Then
$C_{S(n)} \le C_{S(p^r)}$.

Source: Krishnendu Paul and Shameek Paul, *Square-Weighted Zero-Sum Constants*, Journal of Integer
Sequences 27 (2024), Article 24.6.6, Corollary 8. -/
public theorem weightedConsecutiveConstant_squareSet_le_primePower (n p r : ℕ)
    (hn : 2 ≤ n) (hp : p.Prime) (hpn : p ∣ n) (hval : n.factorization p = r) :
    weightedConsecutiveConstant n (squareSet n) ≤
      weightedConsecutiveConstant (p ^ r) (squareSet (p ^ r)) := by
  have hr : 0 < r := hval ▸ hp.factorization_pos_of_dvd (by omega) hpn
  have hq : 1 < p ^ r := one_lt_pow₀ hp.one_lt hr.ne'
  have hmin := Nat.sInf_mem (weightedConsecutiveDefiningSet_squareSet_nonempty hq)
  obtain ⟨hk, hforce⟩ := mem_weightedConsecutiveDefiningSet.mp hmin
  apply Nat.sInf_le
  exact mem_weightedConsecutiveDefiningSet.mpr
    ⟨hk, fun S => hasConsecutiveWeightedZeroSumSubseq_of_primePower_reduction
      hn hp hpn hval (hforce (fun i => ZMod.cast (S i)))⟩

end MetaMathlibExt
