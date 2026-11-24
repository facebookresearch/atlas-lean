/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SelbergSieve
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Selberg's Λ² upper bound sieve

Selberg's sieve rests on one inequality: for real numbers `λ_d` with `λ_1 = 1`,
`1_{(n, P) = 1} ≤ (∑_{d ∣ (n, P)} λ_d)²` for every `n`. Summing over a finite set `A` and
expanding the square gives an upper bound for the number of elements of `A` free of the primes
dividing `P`, for every choice of the `λ_d`. With the optimal level-`R` weights of
`MathlibExt.SelbergSieve.levelWeights`, the main term becomes `X / G(R)`.

Source: D. R. Heath-Brown, *Lectures on sieves*, arXiv:math/0209360 (2002), Sections 1-2,
displays (1.6)-(1.8), (2.1) and (2.5).
-/

@[expose] public section

namespace MathlibExt.SelbergSieve

open Finset

/-- **Selberg's Λ² inequality, pointwise.** If `P ≠ 0` and `λ : ℕ → ℝ` satisfies `λ 1 = 1`, then
for every natural number `n` the indicator of `gcd(P, n) = 1` is at most
`(∑_{d ∣ P, d ∣ n} λ_d)²` (Heath-Brown, *Lectures on sieves*, arXiv:math/0209360, Section 2:
the computation after (2.1) and the line "if `(n, Π(P, z)) = 1` then ... `= λ_1² = 1`"). -/
theorem indicator_coprime_le_sq_sum (P : ℕ) (hP : P ≠ 0) (lam : ℕ → ℝ) (h1 : lam 1 = 1)
    (n : ℕ) :
    (if Nat.Coprime P n then (1 : ℝ) else 0) ≤
      (∑ d ∈ P.divisors, if d ∣ n then lam d else 0) ^ 2 := by
  split_ifs with hcop
  · have hsum : (∑ d ∈ P.divisors, if d ∣ n then lam d else 0) = lam 1 := by
      rw [Finset.sum_eq_single 1]
      · simp
      · intro d hd hd1
        refine ite_eq_right_iff.mpr fun hdn => ?_
        exact absurd (Nat.eq_one_of_dvd_coprimes hcop (Nat.dvd_of_mem_divisors hd) hdn) hd1
      · intro h
        exact absurd (Nat.mem_divisors.mpr ⟨one_dvd P, hP⟩) h
    rw [hsum, h1]
    norm_num
  · exact sq_nonneg _

/-- **Selberg's Λ² upper bound sieve, finite form.** Let `A` be a finite set of natural numbers,
`P ≠ 0`, and `λ : ℕ → ℝ` with `λ 1 = 1`. Then the number of `n ∈ A` coprime to `P` is at most
`∑_{d, e ∣ P} λ_d λ_e · #{n ∈ A : lcm(d, e) ∣ n}`. This holds for every choice of the `λ_d`;
Selberg's method then minimises the right-hand side (Heath-Brown, *Lectures on sieves*,
arXiv:math/0209360, (1.6)-(1.7) with the Λ² weights `μ⁺(d) = ∑_{[d₁, d₂] = d} λ_{d₁} λ_{d₂}` of
(2.1)). -/
theorem card_filter_coprime_le_sum_lambda_sq (A : Finset ℕ) (P : ℕ) (hP : P ≠ 0)
    (lam : ℕ → ℝ) (h1 : lam 1 = 1) :
    ((A.filter fun n => Nat.Coprime P n).card : ℝ) ≤
      ∑ d ∈ P.divisors, ∑ e ∈ P.divisors,
        lam d * lam e * ((A.filter fun n => Nat.lcm d e ∣ n).card : ℝ) := by
  calc ((A.filter fun n => Nat.Coprime P n).card : ℝ)
      = ∑ n ∈ A, (if Nat.Coprime P n then (1 : ℝ) else 0) := by
        rw [Finset.sum_boole]
    _ ≤ ∑ n ∈ A, (∑ d ∈ P.divisors, if d ∣ n then lam d else 0) ^ 2 :=
        Finset.sum_le_sum fun n _ => indicator_coprime_le_sq_sum P hP lam h1 n
    _ = ∑ n ∈ A, ∑ d ∈ P.divisors, ∑ e ∈ P.divisors,
          (if Nat.lcm d e ∣ n then lam d * lam e else 0) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
        have hlcm : Nat.lcm d e ∣ n ↔ d ∣ n ∧ e ∣ n := Nat.lcm_dvd_iff
        by_cases hd : d ∣ n <;> by_cases he : e ∣ n <;> simp [hd, he, hlcm]
    _ = ∑ d ∈ P.divisors, ∑ e ∈ P.divisors, ∑ n ∈ A,
          (if Nat.lcm d e ∣ n then lam d * lam e else 0) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun d _ => Finset.sum_comm
    _ = ∑ d ∈ P.divisors, ∑ e ∈ P.divisors,
          lam d * lam e * ((A.filter fun n => Nat.lcm d e ∣ n).card : ℝ) := by
        refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **Selberg's upper bound with the optimal level weights.** For a bounding sieve `s` with
approximation `X` to its total mass and level `R ≥ 1`, the Λ² sieve built from the level-`R`
Selberg weights gives `S ≤ X / G(R) + ∑_{d ∣ P} |μ⁺(d)| |r_d|`, where `S` is the sifted sum,
`G(R) = ∑_{l ∣ P, l ≤ R} g(l)` is the level sum and `r_d` are the remainders. This is
Heath-Brown, *Lectures on sieves*, arXiv:math/0209360, (2.5), with the support condition
`λ_d = 0` for `d > R` in place of (2.4)'s `λ_d = 0` for `d ≥ ξ`. -/
theorem siftedSum_le_totalMass_div_levelSum_add_errSum (s : BoundingSieve) (R : ℕ)
    (hR : 1 ≤ R) :
    s.siftedSum ≤ s.totalMass / levelSum s R +
      s.errSum (BoundingSieve.lambdaSquared (levelWeights s R)) := by
  have h := s.siftedSum_le_mainSum_errSum_of_upperMoebius _
    (BoundingSieve.upperMoebius_lambdaSquared _ (levelWeights_one s R hR))
  rw [levelWeights_mainSum s R hR] at h
  simpa [div_eq_mul_inv] using h

end MathlibExt.SelbergSieve
