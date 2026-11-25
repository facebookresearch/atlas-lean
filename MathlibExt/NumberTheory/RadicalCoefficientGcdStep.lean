/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerBasis
import Mathlib.Tactic.Ring

/-!
# Divisibility of consecutive radical coefficient gcds

Remove a common factor from the coefficients of one power. Multiplication by `u + X`
and reduction modulo the monic polynomial `X ^ N - v` give integral coordinates again,
so multiplying back by the common factor yields the coordinates of the next power.
-/

namespace MetaMathlibExt

open Polynomial

/-- **The coefficient gcd of $(u + v^{1/N})^n$ divides that of $(u + v^{1/N})^{n+1}$.** Let
$N, u, v$ be natural numbers such that $x^N - v$ is irreducible over $\mathbb{Q}$, let
$\theta = v^{1/N}$ be the nonnegative real $N$-th root of $v$, and let $a_{n,i}$ (for natural $n$
and $0 \le i \le N - 1$) be integers with $(u + \theta)^n = \sum_{i=0}^{N-1} a_{n,i} \theta^i$
for every $n \ge 1$. Write $D_n$ for the nonnegative greatest common divisor of
$a_{n,0}, \dots, a_{n,N-1}$. Then $D_n \mid D_{n+1}$ for every $n \ge 1$.

This holds without the paper's standing assumptions $N \ge 4$ and $\gcd(u, v) = 1$.

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Lemma 4
(`jis-2025-25.2.2-lem-4`). -/
public theorem gcd_radical_expansion_coeffs_dvd_succ {N u v : ℕ}
    (hirr : Irreducible (Polynomial.X ^ N - Polynomial.C (v : ℚ))) (a : ℕ → Fin N → ℤ)
    (ha : ∀ n, 1 ≤ n → ((u : ℝ) + (v : ℝ) ^ (1 / (N : ℝ))) ^ n =
      ∑ i : Fin N, (a n i : ℝ) * ((v : ℝ) ^ (1 / (N : ℝ))) ^ (i : ℕ))
    (n : ℕ) (hn : 1 ≤ n) :
    Finset.univ.gcd (a n) ∣ Finset.univ.gcd (a (n + 1)) := by
  classical
  have hN : N ≠ 0 := by
    rintro rfl
    rw [pow_zero, ← C_1, ← C_sub] at hirr
    exact not_irreducible_C _ hirr
  let θ : ℝ := (v : ℝ) ^ (1 / (N : ℝ))
  have hθ : θ ^ N = v := by
    simpa only [θ, one_div] using Real.rpow_inv_natCast_pow (Nat.cast_nonneg v) hN
  let d := Finset.univ.gcd (a n)
  have hd (i : Fin N) : d ∣ a n i := Finset.gcd_dvd (Finset.mem_univ i)
  let b (i : Fin N) := (hd i).choose
  have hb (i : Fin N) : a n i = d * b i := (hd i).choose_spec
  let P : ℤ[X] := ∑ i : Fin N, C (b i) * X ^ (i : ℕ)
  have hP : (d : ℝ) * aeval θ P = ((u : ℝ) + θ) ^ n := by
    have he : aeval θ P = ∑ i : Fin N, (b i : ℝ) * θ ^ (i : ℕ) := by simp [P]
    have haₙ : ((u : ℝ) + θ) ^ n = ∑ i : Fin N, (a n i : ℝ) * θ ^ (i : ℕ) := ha n hn
    rw [he, Finset.mul_sum, haₙ]
    exact Finset.sum_congr rfl fun i _ ↦ by simp only [hb i, Int.cast_mul, mul_assoc]
  let Q : ℤ[X] := ((C (u : ℤ) + X) * P) %ₘ (X ^ N - C (v : ℤ))
  have hroot : aeval θ (X ^ N - C (v : ℤ)) = 0 := by simp [hθ]
  have hQ : aeval θ Q = ((u : ℝ) + θ) * aeval θ P := by
    change aeval θ (((C (u : ℤ) + X) * P) %ₘ (X ^ N - C (v : ℤ))) = _
    rw [aeval_modByMonic_eq_self_of_root hroot]
    simp
  have hdeg : Q.natDegree < N := by
    have hne : X ^ N - C (v : ℤ) ≠ 1 := fun h ↦ hN <| by
      simpa only [natDegree_X_pow_sub_C, natDegree_one] using congrArg natDegree h
    simpa only [Q, natDegree_X_pow_sub_C] using
      natDegree_modByMonic_lt ((C (u : ℤ) + X) * P) (monic_X_pow_sub_C _ hN) hne
  have hexp : ((u : ℝ) + θ) ^ (n + 1) =
      ∑ i : Fin N, ((d * Q.coeff i : ℤ) : ℝ) * θ ^ (i : ℕ) := by
    calc
      _ = ((u : ℝ) + θ) ^ n * ((u : ℝ) + θ) := pow_succ _ _
      _ = (d : ℝ) * aeval θ Q := by rw [← hP, hQ]; ring
      _ = _ := by
        rw [aeval_eq_sum_range' hdeg, ← Fin.sum_univ_eq_sum_range]
        simp [zsmul_eq_mul, Finset.mul_sum, mul_assoc]
  have hmin : X ^ N - C (v : ℚ) = minpoly ℚ θ :=
    minpoly.eq_of_irreducible_of_monic hirr (by simp [hθ]) (monic_X_pow_sub_C _ hN)
  have hli : LinearIndependent ℚ fun i : Fin N ↦ θ ^ (i : ℕ) := by
    have h := linearIndependent_pow (K := ℚ) θ
    rwa [← hmin, natDegree_X_pow_sub_C] at h
  apply Finset.dvd_gcd_iff.mpr
  intro i _
  refine ⟨Q.coeff i, ?_⟩
  have ha' : ((u : ℝ) + θ) ^ (n + 1) = ∑ j : Fin N, (a (n + 1) j : ℝ) * θ ^ (j : ℕ) :=
    ha (n + 1) (Nat.le_succ_of_le hn)
  have hzero := Fintype.linearIndependent_iff.1 hli
    (fun j ↦ (a (n + 1) j : ℚ) - ((d * Q.coeff j : ℤ) : ℚ)) (by
      simp only [Rat.smul_def, Rat.cast_sub, Rat.cast_intCast, sub_mul, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr (ha'.symm.trans hexp)) i
  exact_mod_cast sub_eq_zero.mp hzero

end MetaMathlibExt
