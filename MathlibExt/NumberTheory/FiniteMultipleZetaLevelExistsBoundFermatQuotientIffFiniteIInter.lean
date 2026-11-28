/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Criterion for a uniform bound on the least non-Wieferich base

A single bound on the least base $N \ge 1$ with $p \nmid N$ and
$p^2 \nmid N^{p-1} - 1$ for every odd prime $p$ exists if and only if, for some
natural number $M \ge 3$, the intersection of the prime sets
$W(N) = \{p : N^{p-1} \equiv 1 \pmod{p^2}\}$ over $2 \le N \le M$ is finite.
For $N \ge 1$ the power is positive, so divisibility of the natural difference
encodes the congruence. For $p \nmid N$, Fermat's little theorem makes the
quotient integral, so non-divisibility by $p^2$ means that $p \nmid q_p(N)$.

The implication from finiteness uses $N = p + 1$ for primes at or below the cutoff;
the statement only requires a bound on a witness, not that the chosen witness
be the least one or be less than $p$.

## References

* Shin-ichiro Seki, *Regular Primes, Non-Wieferich Primes, and Finite Multiple Zeta Values of
  Level N*, INTEGERS 24 (2024), Article A22, pp. 1–14, Section 5, Lemma 3 (p. 11).
* Andrew Granville, *Some conjectures related to Fermat's Last Theorem*, in *Number Theory*
  (Banff, Alberta, 1988), ed. R. A. Mollin, Walter de Gruyter, 1990, pp. 177–192,
  Conjecture 9 (the uniform bound in Seki's Problem 3).
* The finite-exception argument parallels `exists_bound_bernoulli_iff_finite_iInter` in
  `MathlibExt.NumberTheory.FiniteMultipleZetaLevelExistsBoundBernoulliIffFiniteIInter`.
-/

namespace MetaMathlibExt

/-- **Criterion for a uniform bound on the least non-Wieferich base.** The following are
equivalent:
(a) there is a natural number $M$ such that for every odd prime $p$ there is an integer $N$ with
$1 \le N \le M$, $p \nmid N$ and $p^2 \nmid N^{p-1} - 1$;
(b) there is a natural number $M \ge 3$ such that only finitely many primes $p$ satisfy
$p^2 \mid N^{p-1} - 1$ for every integer $N$ with $2 \le N \le M$.

For $p \nmid N$ the condition $p^2 \nmid N^{p-1} - 1$ says that $p$ does not divide the Fermat
quotient $q_p(N) = (N^{p-1} - 1)/p$, so (a) bounds, uniformly in $p$, the least such base $N$;
(b) says that $\bigcap_{N=2}^{M} W(N)$ is finite, where $W(N)$ is the set of primes $p$ with
$N^{p-1} \equiv 1 \pmod{p^2}$.

Source: Seki, *Regular Primes, Non-Wieferich Primes, and Finite Multiple Zeta Values of
Level N*, INTEGERS 24 (2024), Article A22, Lemma 3 (`integers-2024-A22-lem-3`). -/
public theorem exists_bound_fermatQuotient_iff_finite_iInter :
    (∃ M : ℕ, ∀ p : ℕ, p.Prime → p ≠ 2 →
        ∃ N, 1 ≤ N ∧ N ≤ M ∧ ¬ p ∣ N ∧ ¬ p ^ 2 ∣ N ^ (p - 1) - 1) ↔
      ∃ M : ℕ, 3 ≤ M ∧
        {p : ℕ | p.Prime ∧ ∀ N ∈ Finset.Icc 2 M, p ^ 2 ∣ N ^ (p - 1) - 1}.Finite := by
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨max M 3, le_max_right _ _, Set.finite_empty.subset ?_⟩
    rintro p ⟨hp, hall⟩
    by_cases hp2 : p = 2
    · subst p
      exact (by decide : ¬ (2 : ℕ) ^ 2 ∣ 2 ^ (2 - 1) - 1)
        (hall 2 (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩))
    · obtain ⟨N, hN, hNM, -, hndvd⟩ := hM p hp hp2
      have hN1 : N ≠ 1 := by
        rintro rfl
        simp at hndvd
      exact hndvd (hall N (Finset.mem_Icc.mpr ⟨by omega, hNM.trans (le_max_left _ _)⟩))
  · rintro ⟨M, -, hfin⟩
    obtain ⟨B, hB⟩ := hfin.bddAbove
    refine ⟨max M B + 1, fun p hp _ => ?_⟩
    by_cases hsmall : p ≤ max M B
    · refine ⟨1 + p, by omega, by omega, ?_, ?_⟩
      · simpa using (Nat.not_dvd_of_pos_of_lt Nat.zero_lt_one hp.one_lt)
      · have hpow (k : ℕ) : (1 + p) ^ k ≡ 1 + k * p [MOD p ^ 2] := by
          induction k with
          | zero => simpa only [pow_zero, zero_mul, add_zero] using (Nat.ModEq.refl 1)
          | succ k ih =>
            calc
              (1 + p) ^ (k + 1) = (1 + p) ^ k * (1 + p) := pow_succ _ _
              _ ≡ (1 + k * p) * (1 + p) [MOD p ^ 2] := ih.mul (Nat.ModEq.refl _)
              _ = p ^ 2 * k + (1 + (k + 1) * p) := by ring
              _ ≡ 1 + (k + 1) * p [MOD p ^ 2] := Nat.ModEq.modulus_mul_add
        intro hdvd
        have h := Nat.modEq_of_dvd' (Nat.one_le_pow _ _ (by omega)) hdvd
        have hmul : p ^ 2 ∣ (p - 1) * p := Nat.left_modEq_add_iff.mp (h.trans (hpow _))
        rw [pow_two, Nat.mul_dvd_mul_iff_right hp.pos] at hmul
        have hp1 : 1 < p := hp.one_lt
        exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) hmul
    · have hexists : ¬ ∀ N ∈ Finset.Icc 2 M, p ^ 2 ∣ N ^ (p - 1) - 1 := by
        intro hall
        exact hsmall ((hB ⟨hp, hall⟩).trans (le_max_right _ _))
      push Not at hexists
      obtain ⟨N, hmem, hndvd⟩ := hexists
      obtain ⟨hN, hNM⟩ := Finset.mem_Icc.mp hmem
      exact ⟨N, by omega, by omega, Nat.not_dvd_of_pos_of_lt (by omega) (by omega), hndvd⟩

end MetaMathlibExt
