/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import MathlibExt.Combinatorics.Enumerative.Partition.KTupleRegularPartitions
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Enumerative.Partition.KTupleRegularPartitionPrimePower

/-!
# The Nath–Saikia–Sarma congruence for 2-regular tripartitions

Let $p \ge 5$ be prime with $\left(\frac{-2}{p}\right) = -1$, and let $t > 0$ be coprime to $6$
with $p \mid t$. For $n \ge 0$ and $1 \le j \le p - 1$, the number of triples of partitions with
only odd parts and total size $9t^2 n + 9t^2 j/p + (57t^2 - 1)/8$ is divisible by $6$.
The index is $7$ modulo $9$, so it is not triangular and is $1$ modulo $3$. This gives the mod-$6$
conclusion directly, without the stronger mod-$24$ theorem used in the source.

## References

* Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia,
  and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, pp. 1–10,
  Corollary 1 (proving Conjecture 1), Theorem 3, and Lemma 8.
* Hemjyoti Nath, Manjil P. Saikia, and Abhishek Sarma, *Arithmetic Properties of k-Tuple ℓ-Regular
  Partitions*, Journal of Mathematical Analysis and Applications 551 (2025), no. 2, part 1,
  Article 129688, 25 pp. (original conjecture).
* For the two divisibility arguments, we use `tripleTwo_odd_iff_triangular` from
  `MathlibExt.Combinatorics.Enumerative.Partition.KTupleRegularPartitions` and
  `kTupleRegularPartition_primePower_congruent` from
  `MathlibExt.Combinatorics.Enumerative.Partition.KTupleRegularPartitionPrimePower`.
-/

namespace MetaMathlibExt

private theorem nathSaikiaSarma_index_mod_nine (p t n j : ℕ)
    (hcoprime : Nat.gcd t 6 = 1) (hpt : p ∣ t) :
    (9 * t ^ 2 * n + 9 * t ^ 2 * j / p + (57 * t ^ 2 - 1) / 8) % 9 = 7 := by
  have ht₂ : t % 2 = 1 := by
    by_contra h
    have hg : 2 ∣ Nat.gcd t 6 := Nat.dvd_gcd (by omega) (by decide)
    omega
  have ht₃ : t % 3 ≠ 0 := by
    intro h
    have hg : 3 ∣ Nat.gcd t 6 := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h) (by decide)
    omega
  have htSq₈ : t ^ 2 % 8 = 1 := by
    have hr : t % 8 = 1 ∨ t % 8 = 3 ∨ t % 8 = 5 ∨ t % 8 = 7 := by omega
    rw [Nat.pow_mod]
    rcases hr with h | h | h | h <;> simp [h]
  have htSq₃ : t ^ 2 % 3 = 1 := by
    have hr : t % 3 = 1 ∨ t % 3 = 2 := by omega
    rw [Nat.pow_mod]
    rcases hr with h | h <;> simp [h]
  have h₈ : 8 ∣ 57 * t ^ 2 - 1 := by omega
  have hquot := Nat.mul_div_cancel' h₈
  have h₉ : 9 ∣ 9 * t ^ 2 * j / p := by
    have h : p ∣ t ^ 2 * j := dvd_mul_of_dvd_left (dvd_pow hpt (by decide)) j
    rw [mul_assoc, Nat.mul_div_assoc 9 h]
    exact dvd_mul_right _ _
  have hbase : (9 * t ^ 2 * n) % 9 = 0 := by rw [mul_assoc, Nat.mul_mod_right]
  omega

-- The mod-6 proof does not need the prime bound, Legendre condition, or bounds on j.
set_option linter.unusedVariables false in
/--
**The Nath–Saikia–Sarma conjecture.** Let $T_2(n)$ be the number of triples of 2-regular
partitions (partitions with no even part) whose sizes add up to $n$. Let $p \ge 5$ be a prime
with Legendre symbol $\left(\frac{-2}{p}\right) = -1$, and let $t$ be a positive integer with
$\gcd(t, 6) = 1$ and $p \mid t$. Then for every natural number $n$ and every $j$ with
$1 \le j \le p - 1$,
$$T_2\left(9t^2 n + \frac{9t^2 j}{p} + \frac{57t^2 - 1}{8}\right) \equiv 0 \pmod{6}.$$
Both fractions are integers under these hypotheses.

Source: Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia,
and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Corollary 1
(Conjecture conj.nss).
-/
public theorem nathSaikiaSarma_conjecture (p t n j : ℕ) [Fact (Nat.Prime p)]
    (hp : 5 ≤ p) (hlegendre : legendreSym p (-2) = -1) (ht : 0 < t)
    (hcoprime : Nat.gcd t 6 = 1) (hpt : p ∣ t) (hj₁ : 1 ≤ j) (hjp : j ≤ p - 1) :
    Nat.ModEq 6
      (tripleRegularPartitionCount 2
        (9 * t ^ 2 * n + 9 * t ^ 2 * j / p + (57 * t ^ 2 - 1) / 8)) 0 := by
  let i := 9 * t ^ 2 * n + 9 * t ^ 2 * j / p + (57 * t ^ 2 - 1) / 8
  have hi : i % 9 = 7 := nathSaikiaSarma_index_mod_nine p t n j hcoprime hpt
  have h₂ : Nat.ModEq 2 (tripleRegularPartitionCount 2 i) 0 := by
    change tripleRegularPartitionCount 2 i % 2 = 0
    by_contra h
    obtain ⟨m, hm⟩ := (tripleTwo_odd_iff_triangular i).mp (by omega)
    have he := Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.even_mul_succ_self m))
    have hsquare : (2 * m + 1) ^ 2 = 8 * i + 1 := calc
      _ = 4 * (m * (m + 1)) + 1 := by ring
      _ = _ := by omega
    have h₃ : 3 ∣ (2 * m + 1) ^ 2 := by omega
    have h₉ : 9 ∣ (2 * m + 1) ^ 2 :=
      pow_dvd_pow_of_dvd (Nat.prime_three.dvd_of_dvd_pow h₃) 2
    omega
  have h₃ : Nat.ModEq 3 (tripleRegularPartitionCount 2 i) 0 := by
    have hi₃ : 3 * (i / 3) + 1 = i := by omega
    rw [tripleRegularPartitionCount_eq_kTupleRegularPartitionCount, ← hi₃]
    simpa using kTupleRegularPartition_primePower_congruent 3 1 2 1 1 1 (i / 3)
      Nat.prime_three (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact (Nat.modEq_and_modEq_iff_modEq_mul (by decide : Nat.Coprime 2 3)).mp ⟨h₂, h₃⟩

end MetaMathlibExt
