/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerBasis

/-!
# Integer coordinates of powers of `u + v^{1/N}`

Let `θ = v^{1/N}`, so that `θ ^ N = v`. Reducing `(u + X) ^ n` modulo the monic polynomial
`X ^ N - v` over `ℤ` leaves a polynomial of degree less than `N` with the same value at `θ`, so
`(u + θ) ^ n` is an integer combination of `1, θ, …, θ ^ (N - 1)`. When `X ^ N - v` is
irreducible over `ℚ`, it is the minimal polynomial of `θ`, so these powers are linearly
independent over `ℚ` and the integer coordinates are unique.

The proof uses only the irreducibility of `X ^ N - v`. The statement's other hypotheses (two
distinct prime divisors of `N`, positive `u` and `v`, coprime `u` and `v`) are kept as stated but
are not needed.
-/

namespace MetaMathlibExt

open Polynomial

set_option linter.unusedVariables false in
/-- **Unique integer coordinates of powers of $u + v^{1/N}$.** Let $N$ be a natural number with
at least two distinct prime divisors, let $u, v$ be coprime positive integers such that
$x^N - v$ is irreducible over $\mathbb{Q}$, and let $\theta = v^{1/N}$ be the positive real
$N$-th root of $v$. Then for every natural number $n$ there is exactly one tuple of integers
$(a_0, \dots, a_{N-1})$ with $(u + \theta)^n = \sum_{i=0}^{N-1} a_i \theta^i$.

Source: John Ferdinands and Timothy Ferdinands, *Greatest Common Divisors and Lucas's
Theorem*, Journal of Integer Sequences 28 (2025), Article 25.2.2, Lemma 3
(`jis-2025-25.2.2-lem-3`). -/
public theorem existsUnique_radical_expansion_coeffs {N u v : ℕ}
    (hN : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ N ∧ q ∣ N) (hu : 0 < u) (hv : 0 < v)
    (huv : u.Coprime v)
    (hirr : Irreducible (Polynomial.X ^ N - Polynomial.C (v : ℚ))) (n : ℕ) :
    ∃! a : Fin N → ℤ, ((u : ℝ) + (v : ℝ) ^ (1 / (N : ℝ))) ^ n =
      ∑ i : Fin N, (a i : ℝ) * ((v : ℝ) ^ (1 / (N : ℝ))) ^ (i : ℕ) := by
  set θ : ℝ := (v : ℝ) ^ (1 / (N : ℝ)) with hθ
  -- A constant polynomial is not irreducible, so `N ≠ 0`.
  have hN0 : N ≠ 0 := by
    rintro rfl
    rw [pow_zero, ← C_1, ← C_sub] at hirr
    exact not_irreducible_C _ hirr
  have hθN : θ ^ N = v := by
    rw [hθ, one_div]
    exact Real.rpow_inv_natCast_pow (Nat.cast_nonneg v) hN0
  -- Existence: reduce `(u + X) ^ n` modulo the monic polynomial `X ^ N - v` over `ℤ`.
  have hmonic : (X ^ N - C (v : ℤ)).Monic := monic_X_pow_sub_C _ hN0
  have hroot : aeval θ (X ^ N - C (v : ℤ)) = 0 := by simp [hθN]
  set r : ℤ[X] := (C (u : ℤ) + X) ^ n %ₘ (X ^ N - C (v : ℤ)) with hr
  have hrdeg : r.natDegree < N := by
    have hne : X ^ N - C (v : ℤ) ≠ 1 := fun h ↦ hN0 <| by
      simpa only [natDegree_X_pow_sub_C, natDegree_one] using congrArg natDegree h
    simpa only [natDegree_X_pow_sub_C] using natDegree_modByMonic_lt _ hmonic hne
  have hexp : ((u : ℝ) + θ) ^ n = ∑ i : Fin N, (r.coeff i : ℝ) * θ ^ (i : ℕ) := by
    have hval : aeval θ r = ((u : ℝ) + θ) ^ n := by
      rw [hr, aeval_modByMonic_eq_self_of_root hroot]
      simp
    rw [← hval, aeval_eq_sum_range' hrdeg, ← Fin.sum_univ_eq_sum_range]
    simp [zsmul_eq_mul]
  -- Uniqueness: `X ^ N - v` is the minimal polynomial of `θ` over `ℚ`.
  have hmin : X ^ N - C (v : ℚ) = minpoly ℚ θ :=
    minpoly.eq_of_irreducible_of_monic hirr (by simp [hθN]) (monic_X_pow_sub_C _ hN0)
  have hli : LinearIndependent ℚ fun i : Fin N ↦ θ ^ (i : ℕ) := by
    have h := linearIndependent_pow (K := ℚ) θ
    rwa [← hmin, natDegree_X_pow_sub_C] at h
  refine ⟨fun i ↦ r.coeff i, hexp, fun b hb ↦ funext fun i ↦ ?_⟩
  have hzero := Fintype.linearIndependent_iff.1 hli (fun i ↦ (b i : ℚ) - r.coeff i)
    (by simp [Rat.smul_def, sub_mul, Finset.sum_sub_distrib, ← hb, ← hexp]) i
  exact_mod_cast sub_eq_zero.1 hzero

end MetaMathlibExt
