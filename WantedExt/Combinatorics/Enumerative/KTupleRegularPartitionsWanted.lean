/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.Data.Int.Interval
public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct
import Mathlib

namespace MetaMathlibExt

@[expose] public section

/-- The number of `ℓ`-regular partitions of `n`: partitions none of whose parts is
divisible by `ℓ`.
Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia, and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Introduction (definition of ℓ-regular partitions).
-/
public def lRegularPartitionCount (ℓ n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition n)).filter fun p => ∀ a ∈ p.parts, ¬ ℓ ∣ a).card

/-- `T_{ℓ,k}(n)`, the number of `k`-tuples `(λ₁, …, λ_k)` of `ℓ`-regular partitions of
`n₁, …, n_k` with `n₁ + ⋯ + n_k = n`, defined by peeling off the first component: the
empty tuple counts once at `n = 0`, and a `(k+1)`-tuple of total `n` is an `ℓ`-regular
partition of `i` followed by a `k`-tuple of total `n - i`, over `0 ≤ i ≤ n`.
Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia, and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Introduction (definition of `T_{ℓ,k}`).
-/
public def kTupleRegularPartitionCount (ℓ : ℕ) : ℕ → ℕ → ℕ
  | 0, n => if n = 0 then 1 else 0
  | k + 1, n => ∑ i ∈ Finset.range (n + 1),
      lRegularPartitionCount ℓ i * kTupleRegularPartitionCount ℓ k (n - i)

/-- The empty tuple: `T_{ℓ,0}(n)` is `1` at `n = 0` and `0` otherwise.
Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia, and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Introduction (definition of `T_{ℓ,k}`).
-/
public theorem kTupleRegularPartitionCount_zero (ℓ n : ℕ) :
    kTupleRegularPartitionCount ℓ 0 n = if n = 0 then 1 else 0 := rfl

/-- The convolution recurrence `T_{ℓ,k+1}(n) = ∑_{i=0}^{n} r_ℓ(i) · T_{ℓ,k}(n-i)`, with `r_ℓ` the `ℓ`-regular partition count.
Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia, and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Introduction (definition of `T_{ℓ,k}`).
-/
public theorem kTupleRegularPartitionCount_succ (ℓ k n : ℕ) :
    kTupleRegularPartitionCount ℓ (k + 1) n = ∑ i ∈ Finset.range (n + 1),
      lRegularPartitionCount ℓ i * kTupleRegularPartitionCount ℓ k (n - i) := rfl

/-- The paper's abbreviation `T_ℓ(n) = T_{ℓ,3}(n)`.
Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia, and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Introduction (definition of `T_ℓ`).
-/
public def tripleRegularPartitionCount (ℓ n : ℕ) : ℕ :=
  kTupleRegularPartitionCount ℓ 3 n

/-- Zero has exactly one `ℓ`-regular partition, the empty one.
Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia, and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Introduction (definition of ℓ-regular partitions).
-/
public theorem lRegularPartitionCount_zero (ℓ : ℕ) : lRegularPartitionCount ℓ 0 = 1 := by
  simp [lRegularPartitionCount]

/-- Every `T_{ℓ,k}(0)` is `1`: the only tuple of total `0` is the tuple of empty partitions.
Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia, and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Introduction (definition of `T_{ℓ,k}`).
-/
public theorem kTupleRegularPartitionCount_at_zero (ℓ k : ℕ) :
    kTupleRegularPartitionCount ℓ k 0 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [kTupleRegularPartitionCount, lRegularPartitionCount_zero, ih]

/--
`boundedBilateralSeries exponent weight` represents a bilateral integer-indexed
series coefficientwise.  Degree `n` sums indices in `[-n-1,n+1]` whose integer
exponent equals `n`; this bound contains every solution for the quadratic exponents
used in Lemmas 1, 3, and 5.  The generic helper is not intended for other exponents.
Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia, and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Encoding for Lemmas 1, 3, and 5.
-/
public def boundedBilateralSeries (exponent weight : ℤ → ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n =>
    ∑ m ∈ Finset.Icc (-(n : ℤ) - 1) ((n : ℤ) + 1),
      if exponent m = (n : ℤ) then weight m else 0

/--
The characteristic coefficient equation for `boundedBilateralSeries`: coefficient
`n` is exactly the stated finite filtered sum over its symmetric integer interval.
The interval-bound adequacy is specific to the quadratic uses documented above.
Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia, and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Encoding for Lemmas 1, 3, and 5.
-/
public theorem coeff_boundedBilateralSeries (exponent weight : ℤ → ℤ) (n : ℕ) :
    PowerSeries.coeff n (boundedBilateralSeries exponent weight) =
      ∑ m ∈ Finset.Icc (-(n : ℤ) - 1) ((n : ℤ) + 1),
        if exponent m = (n : ℤ) then weight m else 0 := by
  simp [boundedBilateralSeries]

/--
`positiveUnilateralSeries exponent weight` represents a sum indexed by `m ≥ 1`.
Coefficient `n` checks the finite interval `1,...,n`; this suffices for the square
exponents in Lemma 5 and Corollary 3.
Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia, and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Encoding for Lemma 5 and Corollary 3.
-/
public def positiveUnilateralSeries (exponent : ℕ → ℕ) (weight : ℕ → ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n =>
    ∑ m ∈ Finset.Icc 1 n, if exponent m = n then weight m else 0

/--
The characteristic coefficient equation for `positiveUnilateralSeries`: degree `n`
is the matching-index sum over the finite positive interval through `n`.
Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia, and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Encoding for Lemma 5 and Corollary 3.
-/
public theorem coeff_positiveUnilateralSeries (exponent : ℕ → ℕ) (weight : ℕ → ℤ) (n : ℕ) :
    PowerSeries.coeff n (positiveUnilateralSeries exponent weight) =
      ∑ m ∈ Finset.Icc 1 n, if exponent m = n then weight m else 0 := by
  simp [positiveUnilateralSeries]

/--
Theorem 1: if `t > 0` and `gcd(t,6)=1`, then for every natural `n` and
`N = 33` or `N = 57`, `T₂(9n + (Nt²-1)/8)` is congruent to zero modulo 24.
Here `T₂` is `tripleRegularPartitionCount 2`; natural division is used because the
hypotheses make `Nt²-1` divisible by 8, and no redundant divisibility hypothesis is
added.  Naturals encode `n ≥ 0`.
Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia, and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Theorem 1, equation T29n24.
-/
public theorem_wanted tripleTwo_mod_twentyFour (t n N : ℕ) (ht : 0 < t)
    (hcoprime : Nat.gcd t 6 = 1) (hN : N = 33 ∨ N = 57) :
    Nat.ModEq 24 (tripleRegularPartitionCount 2 (9 * n + (N * t ^ 2 - 1) / 8)) 0

/--
Corollary 1, stated as the conclusion of the Nath–Saikia–Sarma conjecture: for prime
`p ≥ 5` with Legendre symbol `(-2/p) = -1`, positive `t` coprime to 6 and divisible
by `p`, every natural `n` and `1 ≤ j ≤ p-1` gives the displayed `T₂` value congruent
to zero modulo 6.  Primality is a `Fact` because `legendreSym` requires that instance;
this is a typechecking representation, not an extra hypothesis.  Both displayed
fractions use natural division and are exact under the hypotheses.
Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia, and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Corollary 1 (Conjecture conj.nss).
-/
public theorem_wanted nathSaikiaSarma_conjecture (p t n j : ℕ) [Fact (Nat.Prime p)]
    (hp : 5 ≤ p) (hlegendre : legendreSym p (-2) = -1) (ht : 0 < t)
    (hcoprime : Nat.gcd t 6 = 1) (hpt : p ∣ t) (hj₁ : 1 ≤ j) (hjp : j ≤ p - 1) :
    Nat.ModEq 6
      (tripleRegularPartitionCount 2
        (9 * t ^ 2 * n + 9 * t ^ 2 * j / p + (57 * t ^ 2 - 1) / 8)) 0

/--
Theorem 2: for a prime `p` whose residue modulo 8 is 3, 5, or 7, naturals `n, α`
with `p ∤ n` give `T₂(p^(2α+1)n + (p^(2α+2)-1)/8) ≡ 0 (mod 8)`; if additionally
`3 ∤ n`, the same value is zero modulo 24.  The conclusion is a conjunction whose
second clause is an implication, directly matching “in addition.”  Natural division
is exact because the residue hypothesis makes `p` odd.
Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia, and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Theorem 2, equations thm.p357mod8 and mod24.
-/
public theorem_wanted tripleTwo_primePower_mod_eight_and_twentyFour (p n α : ℕ)
    (hp : Nat.Prime p) (hres : p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7) (hpn : ¬ p ∣ n) :
    let index := p ^ (2 * α + 1) * n + (p ^ (2 * α + 2) - 1) / 8
    Nat.ModEq 8 (tripleRegularPartitionCount 2 index) 0 ∧
      (¬ 3 ∣ n → Nat.ModEq 24 (tripleRegularPartitionCount 2 index) 0)

/--
Corollary 2: for prime `p ≡ 3,5,7 (mod 8)` with `p ≠ 3`, and naturals `n, α`
with `p ∤ n`, the value `T₂(9p^(2α+1)n + (9p^(2α+2)-1)/8)` is zero modulo 24.
Natural types encode nonnegativity, and the quotient is exact under the odd-residue
hypothesis; no extra divisibility premise is added.
Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia, and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Corollary 2, equation cor.9pmod24.
-/
public theorem_wanted tripleTwo_nine_primePower_mod_twentyFour (p n α : ℕ)
    (hp : Nat.Prime p) (hres : p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7)
    (hp3 : p ≠ 3) (hpn : ¬ p ∣ n) :
    Nat.ModEq 24
      (tripleRegularPartitionCount 2
        (9 * p ^ (2 * α + 1) * n + (9 * p ^ (2 * α + 2) - 1) / 8)) 0

/--
Lemma 3: the paper's quotient identity `f₁⁵/f₂² = Σ` is stated without division as
`f₁⁵ = f₂² * Σ`, where the bilateral coefficient at exponent `m(3m+1)/2` has weight
`6m+1`.  The integer interval encoding includes negative `m`; this clearing of the
denominator is the requested deviation.
Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia, and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Lemma 3, equation f15/f22.
-/
public theorem_wanted qEulerProduct_fifth_power_identity :
    qEulerProduct 1 ^ 5 = qEulerProduct 2 ^ 2 * boundedBilateralSeries
      (fun m => m * (3 * m + 1) / 2) (fun m => 6 * m + 1)

/--
Lemma 4: `(-q;-q)_∞ = f₂³/(f₁f₄)` is cleared of division and stated as
`(-q;-q)_∞ * f₁ * f₄ = f₂³`, with `(-q;-q)_∞ = ∏_{i≥1}(1-(-q)^i)` written as `f₁`
rescaled by `q ↦ -q`.  Clearing denominators is the sole deviation.
Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia, and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Lemma 4, equation f1-q.
-/
public theorem_wanted rescale_neg_one_qEulerProduct_identity :
    PowerSeries.rescale (-1) (qEulerProduct 1) * qEulerProduct 1 * qEulerProduct 4 =
      qEulerProduct 2 ^ 3

/--
Lemma 5: the quotient is cleared by stating `f₁² = f₂ * Σ_{m∈ℤ}(-1)^m q^{m²}`;
the same bilateral theta series equals `1 + 2Σ_{m≥1}(-1)^m q^{m²}`.  The conjunction
retains both equalities, and `natAbs` handles signs at negative indices.  Denominator
clearing and finite coefficient encodings are the documented deviations.
Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia, and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Lemma 5, equation f12/f2.
-/
public theorem_wanted qEulerProduct_square_theta_identity :
    let theta := boundedBilateralSeries (fun m => m ^ 2) (fun m => (-1 : ℤ) ^ m.natAbs)
    qEulerProduct 1 ^ 2 = qEulerProduct 2 * theta ∧
      theta = 1 + 2 * positiveUnilateralSeries (fun m => m ^ 2) (fun m => (-1 : ℤ) ^ m)

/--
Corollary 3: after clearing the paper's denominator, `f₂²` equals `f₄` times
`1 + 2Σ_{n≥1}(-1)^n q^{2n²}`.  `positiveUnilateralSeries` expresses `n ≥ 1`
coefficientwise.  Denominator clearing is the only algebraic deviation.
Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia, and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Corollary 3, equation f22/f4.
-/
public theorem_wanted qEulerProduct_two_square_identity :
    qEulerProduct 2 ^ 2 = qEulerProduct 4 *
      (1 + 2 * positiveUnilateralSeries (fun n => 2 * n ^ 2) (fun n => (-1 : ℤ) ^ n))

/--
Lemma 7: for prime `p`, positive `l,s,m`, and `s ≤ k`, the displayed powers of
`f_l` and `f_{lp^s}` are coefficientwise congruent modulo `p^(k-s+1)`.  The paper's
display uses but its sentence omits `m`; this formalization explicitly quantifies the
requested positive natural `m`.  `s ≤ k` expresses `k-s ≥ 0` and, with `0 < s`, gives the
paper's `k ≥ 1`.  It follows by iterating Lemma 6, which is
`qEulerProduct_pow_prime_pow_congruence`; that statement is itself only a `theorem_wanted` (a
`ProofWanted` marker with no proof term), so Lemma 7 cannot yet be derived as an ordinary
theorem and stays a wanted statement.
Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia, and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Lemma 7, equation cor.modp^k.
-/
public theorem_wanted qEulerProduct_iterated_primePower_congruence (p k l s m : ℕ)
    (hp : Nat.Prime p) (hl : 0 < l) (hs : 0 < s) (hm : 0 < m) (hsk : s ≤ k) (n : ℕ) :
    PowerSeries.coeff n (qEulerProduct l ^ (p ^ k * m)) ≡
      PowerSeries.coeff n (qEulerProduct (l * p ^ s) ^ (p ^ (k - s) * m))
        [ZMOD (p : ℤ) ^ (k - s + 1)]

/--
Lemma 8: `T₂(n)` is odd exactly when `n` is triangular, i.e. there is a natural
`m` with `n = m(m+1)/2`.  Oddness is written as remainder one modulo two.  The paper
says “for some `m`” without specifying a type; taking `m : ℕ` is equivalent because
the triangular values from integer indices duplicate those from naturals.
Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia, and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Lemma 8, equation mod2.
-/
public theorem_wanted tripleTwo_odd_iff_triangular (n : ℕ) :
    tripleRegularPartitionCount 2 n % 2 = 1 ↔ ∃ m : ℕ, n = m * (m + 1) / 2

/--
Theorem 3: for prime `p`, positive naturals `m,ℓ,s`, `s ≤ α`, and
`1 ≤ r ≤ p^s-1`, every natural `n` satisfies
`T_{ℓ,p^αm}(p^s n+r) ≡ 0 (mod p^(α-s+1))`.  Naturals encode all paper integers and
nonnegative `n`; `s ≤ α` prevents subtraction truncation and, with `0 < s`, gives the
paper's `α ≥ 1`.  No other hypothesis is added.
Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia, and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Theorem 3, equation thm.gen1.1.
-/
public theorem_wanted kTupleRegularPartition_primePower_congruent (p m ℓ α s r n : ℕ)
    (hp : Nat.Prime p) (hm : 0 < m) (hℓ : 0 < ℓ) (hs : 0 < s) (hsα : s ≤ α) (hr₁ : 1 ≤ r) (hrp : r ≤
        p ^ s - 1) :
    Nat.ModEq (p ^ (α - s + 1))
      (kTupleRegularPartitionCount ℓ (p ^ α * m) (p ^ s * n + r)) 0

end

end MetaMathlibExt
