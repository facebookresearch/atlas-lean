/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic.LinearCombination
import MathlibExt.Combinatorics.Enumerative.Partition.RamanujanPartitionCongruence

/-!
# Congruences for 3-regular tripartitions

The 3-regular tripartition count is divisible by 3 at sizes `3n + 1` and by 9 at sizes
`3n + 2`. It is also divisible by 3 on progressions indexed by primes congruent to 3 modulo 4.
Modulo 9 its generating series is the square of Jacobi's cube series.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

@[expose] public section

/-- **Regular tripartition counts.** For natural numbers $\ell$ and $n$, $T_\ell(n)$ is the number
of triples $(\lambda_1, \lambda_2, \lambda_3)$ of integer partitions with
$|\lambda_1| + |\lambda_2| + |\lambda_3| = n$ in which no part of any $\lambda_i$ is divisible by
$\ell$; these triples are the $\ell$-regular tripartitions of $n$.

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Section 1, definition of `T_ℓ(n)` (with
generating function `f_ℓ³ / f_1³`, Section 1, eq. (1)). -/
public def regularTripartitionCount (l n : ℕ) : ℕ :=
  ∑ x ∈ Finset.antidiagonal n, ∑ y ∈ Finset.antidiagonal x.2,
    (Nat.Partition.restricted x.1 (¬ l ∣ ·)).card *
      (Nat.Partition.restricted y.1 (¬ l ∣ ·)).card *
      (Nat.Partition.restricted y.2 (¬ l ∣ ·)).card

private theorem card_restricted_zero (p : ℕ → Prop) [DecidablePred p] :
    (Nat.Partition.restricted 0 p).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨default, ?_⟩
  ext x
  simp [Nat.Partition.restricted, Subsingleton.elim x default]

private theorem card_restricted_one (p : ℕ → Prop) [DecidablePred p] (h : p 1) :
    (Nat.Partition.restricted 1 p).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨default, ?_⟩
  ext x
  simp [Nat.Partition.restricted, Subsingleton.elim x default, h]

/-- **The regular tripartition count at zero.** For every natural number $\ell$, $T_\ell(0) = 1$,
where $T_\ell(n)$ is the number of $\ell$-regular tripartitions of $n$: the only tripartition of
$0$ is the triple of empty partitions.

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86 (definition of `T_ℓ(n)`). -/
public theorem regularTripartitionCount_zero (l : ℕ) : regularTripartitionCount l 0 = 1 := by
  simp [regularTripartitionCount, card_restricted_zero]

/-- **The number of $\ell$-regular tripartitions of $1$.** For every natural number $\ell \ne 1$,
the number $T_\ell(1)$ of $\ell$-regular tripartitions of $1$ is $3$: the single part $1$ lies in
one of the three components.

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86 (definition of `T_ℓ(n)`). -/
public theorem regularTripartitionCount_one (l : ℕ) (hl : l ≠ 1) :
    regularTripartitionCount l 1 = 3 := by
  have h1 : ¬ l ∣ 1 := by simpa using hl
  simp [regularTripartitionCount, Finset.Nat.antidiagonal_succ, card_restricted_zero,
    card_restricted_one (fun x => ¬ l ∣ x) h1]

namespace regularTripartitionCount_three_mod_three_nine

private theorem geom_cube (x : (ZMod 9)⟦X⟧) : (1 + x + x ^ 2) ^ 3 = (1 - x) ^ 6 := by
  have h : (9 : (ZMod 9)⟦X⟧) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (C (R := ZMod 9)) (show (9 : ZMod 9) = 0 by decide)
  linear_combination (x - x ^ 2 + 3 * x ^ 3 - x ^ 4 + x ^ 5) * h

-- Glaisher's product has one factor 1 + x + x² per part size. Cubing each
-- factor reduces the tripartition series to the sixth power of Euler's product.
private theorem count_mod_nine (n : ℕ) :
    (regularTripartitionCount 3 n : ℤ) ≡ coeff n (jacobiCubeSeries ^ 2) [ZMOD 9] := by
  let : TopologicalSpace (ZMod 9) := ⊥
  have : DiscreteTopology (ZMod 9) := ⟨rfl⟩
  let φ := PowerSeries.map (Int.castRingHom (ZMod 9))
  have cont : Continuous (φ : ℤ⟦X⟧ → (ZMod 9)⟦X⟧) :=
    continuous_pi fun d ↦ (continuous_of_discreteTopology (f := fun z : ℤ ↦ (z : ZMod 9))).comp
      (continuous_apply d)
  have euler := ((WithPiTopology.hasProd_one_sub_X_pow ℤ).pow 6).map φ cont
  simp only [Function.comp_def, φ, map_pow, map_sub, map_one, map_X] at euler
  have parts := (Nat.Partition.hasProd_powerSeriesMk_card_countRestricted (ZMod 9)
    (m := 3) (by decide)).pow 3
  simp only [pow_mul, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero,
    pow_one, geom_cube] at parts
  have h := congrArg (coeff n) (parts.unique euler)
  apply (ZMod.intCast_eq_intCast_iff _ _ 9).mp
  rw [Int.cast_natCast, ← pentagonalSeries_pow_three, ← pow_mul]
  simp only [← map_pow, coeff_map, Int.coe_castRingHom] at h
  rw [pow_succ', pow_two, coeff_mul] at h
  simpa only [Int.cast_natCast, regularTripartitionCount, Nat.cast_sum, Nat.cast_mul,
    Nat.Partition.card_restricted_eq_card_countRestricted _ (by decide : 0 < 3),
    coeff_mk, coeff_mul, Finset.mul_sum, mul_assoc] using h

-- Triangular numbers have residues 0 and 1 modulo 3. In the second case
-- the weight 2t + 1 contributes a factor of 3 to Jacobi's coefficient.
private theorem dvd_coeff_jacobi (k : ℕ) :
    (3 : ℤ) ^ (k % 3) ∣ coeff k jacobiCubeSeries := by
  by_cases hk : ∃ t : ℕ, (t + 1).choose 2 = k
  · obtain ⟨t, rfl⟩ := hk
    have residue (s : ℕ) : (s + 1).choose 2 % 3 = if s % 3 = 1 then 1 else 0 := by
      induction s with
      | zero => decide
      | succ s ih =>
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
        change (s + 1 + (s + 1).choose 2) % 3 = if (s + 1) % 3 = 1 then 1 else 0
        split_ifs at * <;> omega
    rw [coeff_jacobiCubeSeries_triangle, residue]
    split_ifs with ht
    · rw [pow_one]
      exact dvd_mul_of_dvd_right (by omega) _
    · simp
  · rw [coeff_jacobiCubeSeries_eq_zero (fun t ht ↦ hk ⟨t, ht⟩)]
    exact dvd_zero _

private theorem dvd_coeff_square (k : ℕ) :
    (3 : ℤ) ^ (k % 3) ∣ coeff k (jacobiCubeSeries ^ 2) := by
  rw [pow_two, coeff_mul]
  apply Finset.dvd_sum
  rintro ⟨i, j⟩ hij
  have h := Finset.mem_antidiagonal.mp hij
  apply dvd_trans (pow_dvd_pow (3 : ℤ) (show k % 3 ≤ i % 3 + j % 3 by omega))
  rw [pow_add]
  exact mul_dvd_mul (dvd_coeff_jacobi i) (dvd_coeff_jacobi j)

end regularTripartitionCount_three_mod_three_nine

open regularTripartitionCount_three_mod_three_nine in
/-- **Congruences modulo 3 and 9 for 3-regular tripartitions.** Let $T_3(m)$ be the number of
$3$-regular tripartitions of $m$. For every natural number $n$, $3 \mid T_3(3n + 1)$ and
$9 \mid T_3(3n + 2)$.

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Corollary 2 (congruences (53), (54)). -/
public theorem regularTripartitionCount_three_mod_three_nine (n : ℕ) :
    3 ∣ regularTripartitionCount 3 (3 * n + 1) ∧ 9 ∣ regularTripartitionCount 3 (3 * n + 2) := by
  have h₁ := Int.modEq_iff_dvd.mp (count_mod_nine (3 * n + 1))
  have h₂ := Int.modEq_iff_dvd.mp (count_mod_nine (3 * n + 2))
  have d₁ := dvd_coeff_square (3 * n + 1)
  have d₂ := dvd_coeff_square (3 * n + 2)
  simp at d₁ d₂
  omega

namespace regularTripartitionCount_three_prime_three_mod_four

-- Two triangular exponents contributing to the product give two odd squares.
private theorem coeff_square_eq_zero {k : ℕ}
    (hk : ¬ ∃ x y : ℕ, 8 * k + 2 = x ^ 2 + y ^ 2) :
    coeff k (jacobiCubeSeries ^ 2) = 0 := by
  rw [pow_two, coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨a, b⟩ hab
  have hab' : a + b = k := Finset.mem_antidiagonal.mp hab
  by_cases ha : ∃ s : ℕ, (s + 1).choose 2 = a
  · obtain ⟨s, rfl⟩ := ha
    suffices hb : ∀ t : ℕ, (t + 1).choose 2 ≠ b by
      simp [coeff_jacobiCubeSeries_eq_zero hb]
    rintro t rfl
    apply hk
    refine ⟨2 * s + 1, 2 * t + 1, ?_⟩
    nlinarith [two_mul_choose_two_succ s, two_mul_choose_two_succ t]
  · simp [coeff_jacobiCubeSeries_eq_zero (not_exists.mp ha)]

-- A prime congruent to 3 modulo 4 occurs to even order in every sum of two squares.
private theorem not_sum_sq {p α b : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3)
    (hb : ¬ p ∣ b) : ¬ ∃ x y : ℕ, p ^ (2 * α + 1) * b = x ^ 2 + y ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hb₀ : b ≠ 0 := fun h ↦ hb (h ▸ dvd_zero _)
  have hpow := pow_ne_zero (2 * α + 1) hp.ne_zero
  have hmem : p ∈ (p ^ (2 * α + 1) * b).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) _,
      mul_ne_zero hpow hb₀⟩
  intro h
  have hev := Nat.eq_sq_add_sq_iff.mp h p hmem hp4
  rw [Nat.padicValNat_def, Nat.multiplicity_mul hpow hb₀, Nat.multiplicity_prime_pow,
    multiplicity_eq_zero_of_not_dvd hb, add_zero] at hev
  obtain ⟨j, hj⟩ := hev
  omega

end regularTripartitionCount_three_prime_three_mod_four

open regularTripartitionCount_three_prime_three_mod_four in
/-- **A congruence modulo 3 for 3-regular tripartitions at primes $p \equiv 3 \pmod 4$.** Let
$T_3(m)$ be the number of $3$-regular tripartitions of $m$, and let $p$ be a prime with
$p \equiv 3 \pmod 4$. For all natural numbers $\alpha$ and $n$ and every integer $i$ with
$1 \le i \le p - 1$,
$$
T_3\Bigl(3 p^{2\alpha+1} (p n + i) + \frac{p^{2\alpha+2} - 1}{4}\Bigr) \equiv 0 \pmod 3,
$$
where the division by $4$ is exact.

Source: Mohammed L. Nadji and Moussa Ahmia, *Congruences for l-Regular Tripartitions for
l in {2,3}*, INTEGERS 24 (2024), Article A86, Theorem 5 (congruence (55)). -/
public theorem regularTripartitionCount_three_prime_three_mod_four
    (p α n i : ℕ) (hp : p.Prime) (hp4 : p % 4 = 3) (hi : 1 ≤ i) (hip : i < p) :
    3 ∣ regularTripartitionCount 3
      (3 * p ^ (2 * α + 1) * (p * n + i) + (p ^ (2 * α + 2) - 1) / 4) := by
  let k := 3 * p ^ (2 * α + 1) * (p * n + i) + (p ^ (2 * α + 2) - 1) / 4
  change 3 ∣ regularTripartitionCount 3 k
  have hsq : p ^ 2 ≡ 1 [MOD 4] := by
    simp [Nat.ModEq, Nat.pow_mod, hp4]
  have hmod : p ^ (2 * α + 2) ≡ 1 [MOD 4] := by
    simpa only [← pow_mul, Nat.mul_add, mul_one, one_pow] using hsq.pow (α + 1)
  have hexact : 4 * ((p ^ (2 * α + 2) - 1) / 4) + 1 = p ^ (2 * α + 2) := by
    change p ^ (2 * α + 2) % 4 = 1 at hmod
    omega
  have hindex : 4 * k + 1 = p ^ (2 * α + 1) * (12 * (p * n + i) + p) := by
    dsimp [k]
    rw [Nat.mul_add, add_assoc, hexact, pow_succ p (2 * α + 1)]
    ring
  by_cases hp3 : p = 3
  · have hdiv : 3 ∣ 4 * k + 1 := by
      rw [hindex, hp3]
      exact dvd_mul_of_dvd_left (dvd_pow_self 3 (by omega)) _
    have hk : k = 3 * (k / 3) + 2 := by omega
    have h := (regularTripartitionCount_three_mod_three_nine (k / 3)).2
    rw [← hk] at h
    exact dvd_trans (by decide : 3 ∣ 9) h
  · have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
    have hnd : ¬ p ∣ 24 := by
      rw [show 24 = 2 ^ 3 * 3 by decide, hp.dvd_mul]
      exact not_or_intro (fun h ↦ hp2 (hp.dvd_of_dvd_pow h))
        (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
    have hi' : ¬ p ∣ p * n + i := by
      rw [Nat.dvd_add_right (dvd_mul_right p n)]
      exact Nat.not_dvd_of_pos_of_lt hi hip
    have hb : ¬ p ∣ 24 * (p * n + i) + 2 * p := by
      rw [Nat.dvd_add_left (dvd_mul_left p 2), hp.dvd_mul]
      exact not_or_intro hnd hi'
    have hk : 8 * k + 2 = p ^ (2 * α + 1) * (24 * (p * n + i) + 2 * p) := by
      linear_combination 2 * hindex
    have hzero := coeff_square_eq_zero (k := k) (hk ▸ not_sum_sq hp hp4 hb)
    have h := Int.modEq_iff_dvd.mp
      (regularTripartitionCount_three_mod_three_nine.count_mod_nine k)
    rw [hzero] at h
    omega

end

end MetaMathlibExt
