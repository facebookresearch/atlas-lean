/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

/-! # Dominant root of a characteristic polynomial with positive recurrence parameters

Let $m \ge 2$ and let $a_1, \ldots, a_m$ be positive integers. The characteristic polynomial
$x^m - a_1 x^{m-1} - \cdots - a_m$ has leading coefficient $1$ and lower coefficients
$-a_1, \ldots, -a_m$. The theorem `MetaMathlibExt.exists_dominant_root_of_pos_coeff_charPoly`
shows that its unique positive real root $\rho$ is simple and greater than one. Every other
complex root has modulus strictly less than $\rho$.
-/

@[expose] public section

open Polynomial

namespace MetaMathlibExt

namespace exists_dominant_root_of_pos_coeff_charPoly

-- Factor the polynomial function over the reals through the auxiliary function
-- `x ↦ x - ∑ i, aᵢ / x ^ i`, which is strictly increasing on `(0, ∞)`.
private theorem factor_real {m : ℕ} (hm : 2 ≤ m) (a : Fin m → ℕ) (x : ℝ) (hx : 0 < x) :
    x ^ (m - 1) * (x - ∑ i : Fin m, (a i : ℝ) / x ^ (i : ℕ))
      = x ^ m - ∑ i : Fin m, (a i : ℝ) * x ^ (m - 1 - (i : ℕ)) := by
  rw [mul_sub, Finset.mul_sum]
  congr 1
  · rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m)]
  · apply Finset.sum_congr rfl
    intro i _
    have hi : (i : ℕ) ≤ m - 1 := by have := i.isLt; omega
    calc x ^ (m - 1) * ((a i : ℝ) / x ^ (i : ℕ))
        = (a i : ℝ) * (x ^ (m - 1) * (x ^ (i : ℕ))⁻¹) := by ring
      _ = (a i : ℝ) * x ^ (m - 1 - (i : ℕ)) := by rw [pow_sub₀ x hx.ne' hi]

-- The same factorisation for `aeval`.
private theorem factor_aeval {m : ℕ} (hm : 2 ≤ m) (a : Fin m → ℕ) (φ : ℤ[X])
    (hφ : φ = X ^ m - ∑ i : Fin m, C (a i : ℤ) * X ^ (m - 1 - (i : ℕ))) (x : ℝ)
    (hx : 0 < x) :
    x ^ (m - 1) * (x - ∑ i : Fin m, (a i : ℝ) / x ^ (i : ℕ)) = aeval x φ := by
  rw [factor_real hm a x hx, hφ]
  simp

-- The auxiliary function is strictly increasing on the positive reals: `x` increases
-- while every summand `aᵢ / x ^ i` decreases.
private theorem strictMono_aux {m : ℕ} (a : Fin m → ℕ) :
    StrictMonoOn (fun x : ℝ => x - ∑ i : Fin m, (a i : ℝ) / x ^ (i : ℕ)) (Set.Ioi 0) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ioi] at hx hy
  have hterm : ∀ i : Fin m, (a i : ℝ) / y ^ (i : ℕ) ≤ (a i : ℝ) / x ^ (i : ℕ) := by
    intro i
    apply div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ a i)
      (pow_pos hx _) (pow_le_pow_left₀ hx.le hxy.le _)
  have hsum : ∑ i : Fin m, (a i : ℝ) / y ^ (i : ℕ)
      ≤ ∑ i : Fin m, (a i : ℝ) / x ^ (i : ℕ) := Finset.sum_le_sum fun i _ => hterm i
  simp only
  linarith

-- The auxiliary function is negative at `1`, since the coefficients are at least `1`.
private theorem aux_neg_at_one {m : ℕ} (hm : 2 ≤ m) (a : Fin m → ℕ) (ha : ∀ i, 0 < a i) :
    (1 : ℝ) - ∑ i : Fin m, (a i : ℝ) / (1 : ℝ) ^ (i : ℕ) < 0 := by
  have hsum : (m : ℝ) ≤ ∑ i : Fin m, (a i : ℝ) := by
    have h : ∑ _i : Fin m, (1 : ℝ) ≤ ∑ i : Fin m, (a i : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact_mod_cast ha i
    simpa using h
  have h1 : ∑ i : Fin m, (a i : ℝ) / (1 : ℝ) ^ (i : ℕ) = ∑ i : Fin m, (a i : ℝ) := by
    simp
  rw [h1]
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  linarith

-- The auxiliary function is positive at `1 + ∑ i, aᵢ`, since every summand is at most `aᵢ`.
private theorem exists_aux_pos {m : ℕ} (hm : 2 ≤ m) (a : Fin m → ℕ) (ha : ∀ i, 0 < a i) :
    ∃ X : ℝ, 1 < X ∧ 0 < X - ∑ i : Fin m, (a i : ℝ) / X ^ (i : ℕ) := by
  have hSge : (2 : ℝ) ≤ ∑ i : Fin m, (a i : ℝ) := by
    have h : ∑ _i : Fin m, (1 : ℝ) ≤ ∑ i : Fin m, (a i : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact_mod_cast ha i
    have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hmle : (m : ℝ) ≤ ∑ i : Fin m, (a i : ℝ) := by simpa using h
    linarith
  refine ⟨(∑ i : Fin m, (a i : ℝ)) + 1, by linarith, ?_⟩
  have hX : (1 : ℝ) < (∑ i : Fin m, (a i : ℝ)) + 1 := by linarith
  have hterm : ∀ i : Fin m, (a i : ℝ) / ((∑ j : Fin m, (a j : ℝ)) + 1) ^ (i : ℕ)
      ≤ (a i : ℝ) := by
    intro i
    have h1 : (1 : ℝ) ≤ ((∑ j : Fin m, (a j : ℝ)) + 1) ^ (i : ℕ) := one_le_pow₀ hX.le
    calc (a i : ℝ) / ((∑ j : Fin m, (a j : ℝ)) + 1) ^ (i : ℕ)
        ≤ (a i : ℝ) / 1 := by
          apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num) h1
      _ = (a i : ℝ) := div_one _
  have hsum : ∑ i : Fin m, (a i : ℝ) / ((∑ j : Fin m, (a j : ℝ)) + 1) ^ (i : ℕ)
      ≤ ∑ i : Fin m, (a i : ℝ) := Finset.sum_le_sum fun i _ => hterm i
  linarith

-- The unique positive real root, greater than `1`, with its auxiliary-function
-- equation and its polynomial equation.
private theorem real_root (m : ℕ) (hm : 2 ≤ m) (a : Fin m → ℕ) (ha : ∀ i, 0 < a i)
    (φ : ℤ[X])
    (hφ : φ = X ^ m - ∑ i : Fin m, C (a i : ℤ) * X ^ (m - 1 - (i : ℕ))) :
    ∃ ρ : ℝ, 1 < ρ ∧ (∀ x : ℝ, 0 < x → aeval x φ = 0 → x = ρ) ∧
      (ρ - ∑ i : Fin m, (a i : ℝ) / ρ ^ (i : ℕ) = 0) ∧
      (ρ ^ m = ∑ i : Fin m, (a i : ℝ) * ρ ^ (m - 1 - (i : ℕ))) := by
  obtain ⟨X, hX1, hXg⟩ := exists_aux_pos hm a ha
  have hcont : ContinuousOn (fun x : ℝ => aeval x φ) (Set.Icc 1 X) :=
    (Polynomial.continuous_aeval φ).continuousOn
  have h1neg : aeval (1 : ℝ) φ < 0 := by
    have h := factor_aeval hm a φ hφ 1 one_pos
    have hg := aux_neg_at_one hm a ha
    rw [← h]
    simpa using hg
  have hXpos : 0 < aeval X φ := by
    have h := factor_aeval hm a φ hφ X (by linarith : (0 : ℝ) < X)
    have hpow : (0 : ℝ) < X ^ (m - 1) := pow_pos (by linarith) _
    rw [← h]
    exact mul_pos hpow hXg
  have hmem : (0 : ℝ) ∈ Set.Icc (aeval (1 : ℝ) φ) (aeval X φ) := ⟨le_of_lt h1neg, le_of_lt hXpos⟩
  obtain ⟨ρ, hρmem, hρeq⟩ := intermediate_value_Icc (by linarith : (1 : ℝ) ≤ X) hcont hmem
  obtain ⟨hρ1, hρX⟩ := Set.mem_Icc.mp hρmem
  have hρpos : (0 : ℝ) < ρ := by linarith
  have hρeq' : aeval ρ φ = 0 := hρeq
  have hρg : ρ - ∑ i : Fin m, (a i : ℝ) / ρ ^ (i : ℕ) = 0 := by
    have h := factor_aeval hm a φ hφ ρ hρpos
    rw [hρeq'] at h
    have hpow : ρ ^ (m - 1) ≠ 0 := pow_ne_zero _ hρpos.ne'
    exact (mul_eq_zero.mp h).resolve_left hpow
  have hρ1' : 1 < ρ := by
    by_contra hle
    have hle : ρ ≤ 1 := le_of_not_gt hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hltg : ρ - ∑ i : Fin m, (a i : ℝ) / ρ ^ (i : ℕ)
          < 1 - ∑ i : Fin m, (a i : ℝ) / (1 : ℝ) ^ (i : ℕ) :=
        strictMono_aux a (Set.mem_Ioi.mpr hρpos) (Set.mem_Ioi.mpr one_pos) hlt
      rw [hρg] at hltg
      have hg := aux_neg_at_one hm a ha
      linarith
    · rw [heq] at hρg
      have hg := aux_neg_at_one hm a ha
      linarith
  have hρeqm : ρ ^ m = ∑ i : Fin m, (a i : ℝ) * ρ ^ (m - 1 - (i : ℕ)) := by
    have h := factor_real hm a ρ hρpos
    rw [hρg, mul_zero] at h
    linarith
  refine ⟨ρ, hρ1', ?_, hρg, hρeqm⟩
  intro x hx hxroot
  have hxg : x - ∑ i : Fin m, (a i : ℝ) / x ^ (i : ℕ) = 0 := by
    have h := factor_aeval hm a φ hφ x hx
    rw [hxroot] at h
    have hpow : x ^ (m - 1) ≠ 0 := pow_ne_zero _ hx.ne'
    exact (mul_eq_zero.mp h).resolve_left hpow
  have hmono := strictMono_aux a
  exact hmono.injOn (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr hρpos)
    (show (x - ∑ i : Fin m, (a i : ℝ) / x ^ (i : ℕ))
      = (ρ - ∑ i : Fin m, (a i : ℝ) / ρ ^ (i : ℕ)) by rw [hxg, hρg])

-- The image of `φ` in `ℂ[X]`, in the same form.
private theorem map_eq (m : ℕ) (a : Fin m → ℕ) (φ : ℤ[X])
    (hφ : φ = X ^ m - ∑ i : Fin m, C (a i : ℤ) * X ^ (m - 1 - (i : ℕ))) :
    φ.map (Int.castRingHom ℂ) = X ^ m - ∑ i : Fin m, C ((a i : ℂ)) * X ^ (m - 1 - (i : ℕ)) := by
  rw [hφ, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]
  simp

-- The image polynomial has degree `m` and is nonzero, by its coefficients.
private theorem natDegree_eq (m : ℕ) (a : Fin m → ℕ) (φ : ℤ[X])
    (hφ : φ = X ^ m - ∑ i : Fin m, C (a i : ℤ) * X ^ (m - 1 - (i : ℕ))) :
    (φ.map (Int.castRingHom ℂ)).natDegree = m ∧ φ.map (Int.castRingHom ℂ) ≠ 0 := by
  have hqeq := map_eq m a φ hφ
  set q := φ.map (Int.castRingHom ℂ) with hqdef
  have hcoeff : q.coeff m = 1 := by
    rw [hqeq]
    have hsum : (∑ i : Fin m, C ((a i : ℂ)) * X ^ (m - 1 - (i : ℕ))).coeff m = 0 := by
      rw [Polynomial.finsetSum_coeff]
      apply Finset.sum_eq_zero
      intro i _
      rw [Polynomial.coeff_C_mul_X_pow]
      split_ifs with h
      · have := i.isLt; omega
      · rfl
    rw [Polynomial.coeff_sub, hsum, sub_zero]
    simp [Polynomial.coeff_X_pow]
  have hle : q.natDegree ≤ m := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro n hn
    rw [hqeq]
    have hsum : (∑ i : Fin m, C ((a i : ℂ)) * X ^ (m - 1 - (i : ℕ))).coeff n = 0 := by
      rw [Polynomial.finsetSum_coeff]
      apply Finset.sum_eq_zero
      intro i _
      rw [Polynomial.coeff_C_mul_X_pow]
      split_ifs with h
      · have := i.isLt; omega
      · rfl
    rw [Polynomial.coeff_sub, hsum, sub_zero, Polynomial.coeff_X_pow]
    split_ifs with h
    · omega
    · rfl
  have hge : m ≤ q.natDegree :=
    Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff]; norm_num)
  have hne : q ≠ 0 := by
    intro hzero
    rw [hzero] at hcoeff
    simp at hcoeff
  exact ⟨by omega, hne⟩

-- A complex root satisfies the defining equation.
private theorem root_eq (m : ℕ) (a : Fin m → ℕ) (φ : ℤ[X])
    (hφ : φ = X ^ m - ∑ i : Fin m, C (a i : ℤ) * X ^ (m - 1 - (i : ℕ))) (z : ℂ)
    (hz : eval z (φ.map (Int.castRingHom ℂ)) = 0) :
    z ^ m = ∑ i : Fin m, (a i : ℂ) * z ^ (m - 1 - (i : ℕ)) := by
  have hqeq := map_eq m a φ hφ
  rw [hqeq] at hz
  simp only [eval_sub, eval_finsetSum, eval_pow, eval_X, eval_mul, eval_C] at hz
  exact sub_eq_zero.mp hz

-- A complex root is nonzero: only the constant term survives at `0`.
private theorem root_ne_zero {m : ℕ} (hm : 2 ≤ m) (a : Fin m → ℕ) (ha : ∀ i, 0 < a i)
    (z : ℂ)
    (heq : z ^ m = ∑ i : Fin m, (a i : ℂ) * z ^ (m - 1 - (i : ℕ))) : z ≠ 0 := by
  intro hz0
  rw [hz0] at heq
  simp only [zero_pow (by omega : m ≠ 0)] at heq
  have hsum : ∑ i : Fin m, (a i : ℂ) * (0 : ℂ) ^ (m - 1 - (i : ℕ))
      = (a ⟨m - 1, by omega⟩ : ℂ) := by
    have h1 := Fintype.sum_eq_single (⟨m - 1, by omega⟩ : Fin m)
      (f := fun i : Fin m => (a i : ℂ) * (0 : ℂ) ^ (m - 1 - (i : ℕ))) (by
        intro i hi
        have hexp : m - 1 - (i : ℕ) ≠ 0 := by
          have hi' : (i : ℕ) ≠ m - 1 := by
            intro h
            apply hi
            ext
            exact h
          have := i.isLt; omega
        rw [zero_pow hexp, mul_zero])
    rw [h1]
    simp
  rw [hsum] at heq
  have hne : ((a ⟨m - 1, by omega⟩ : ℕ) : ℂ) ≠ 0 :=
    by exact_mod_cast (ha ⟨m - 1, by omega⟩).ne'
  exact hne heq.symm

-- The triangle inequality, together with monotonicity of the auxiliary function,
-- bounds the modulus of a complex root by `ρ`.
private theorem norm_le_of_root {m : ℕ} (hm : 2 ≤ m) (a : Fin m → ℕ) (ρ : ℝ)
    (hρpos : 0 < ρ) (hρg : ρ - ∑ i : Fin m, (a i : ℝ) / ρ ^ (i : ℕ) = 0)
    (hstrict : StrictMonoOn (fun x : ℝ => x - ∑ i : Fin m, (a i : ℝ) / x ^ (i : ℕ))
      (Set.Ioi 0))
    (z : ℂ) (hz : z ≠ 0)
    (heq : z ^ m = ∑ i : Fin m, (a i : ℂ) * z ^ (m - 1 - (i : ℕ))) :
    ‖z‖ ≤ ρ := by
  set r := ‖z‖ with hrdef
  have hrpos : 0 < r := norm_pos_iff.mpr hz
  have hnorm : r ^ m ≤ ∑ i : Fin m, (a i : ℝ) * r ^ (m - 1 - (i : ℕ)) := by
    have h1 : ‖z ^ m‖ ≤ ∑ i : Fin m, ‖(a i : ℂ) * z ^ (m - 1 - (i : ℕ))‖ := by
      rw [heq]
      exact norm_sum_le _ _
    rw [norm_pow] at h1
    refine h1.trans_eq ?_
    apply Finset.sum_congr rfl
    intro i _
    rw [norm_mul, norm_pow]
    have hcast : ‖(a i : ℂ)‖ = (a i : ℝ) := by simp
    rw [hcast]
  have hfact := factor_real hm a r hrpos
  have hgle : r - ∑ i : Fin m, (a i : ℝ) / r ^ (i : ℕ) ≤ 0 := by
    have hpow : (0 : ℝ) < r ^ (m - 1) := pow_pos hrpos _
    have hle0 : r ^ (m - 1) * (r - ∑ i : Fin m, (a i : ℝ) / r ^ (i : ℕ))
        ≤ r ^ (m - 1) * 0 := by
      rw [mul_zero, hfact]
      linarith [hnorm]
    exact le_of_mul_le_mul_left hle0 hpow
  by_contra hlt
  have hlt : ρ < r := lt_of_not_ge hlt
  have hltg : ρ - ∑ i : Fin m, (a i : ℝ) / ρ ^ (i : ℕ)
      < r - ∑ i : Fin m, (a i : ℝ) / r ^ (i : ℕ) :=
    hstrict (Set.mem_Ioi.mpr hρpos) (Set.mem_Ioi.mpr hrpos) hlt
  rw [hρg] at hltg
  linarith

-- The rescaling weights sum to `1`, by the polynomial equation at `ρ`.
private theorem sum_b_eq_one {m : ℕ} (a : Fin m → ℕ) (ρ : ℝ)
    (hρpos : 0 < ρ)
    (hρeq : ρ ^ m = ∑ i : Fin m, (a i : ℝ) * ρ ^ (m - 1 - (i : ℕ))) :
    ∑ i : Fin m, (a i : ℝ) / ρ ^ ((i : ℕ) + 1) = 1 := by
  have hρne : ρ ≠ 0 := hρpos.ne'
  have hdiv := congrArg (· / ρ ^ m) hρeq
  rw [Finset.sum_div] at hdiv
  have hterm : ∀ i : Fin m, (a i : ℝ) * ρ ^ (m - 1 - (i : ℕ)) / ρ ^ m
      = (a i : ℝ) / ρ ^ ((i : ℕ) + 1) := by
    intro i
    have hk : (m - 1 - (i : ℕ)) + ((i : ℕ) + 1) = m := by have := i.isLt; omega
    have hpow : ρ ^ m = ρ ^ (m - 1 - (i : ℕ)) * ρ ^ ((i : ℕ) + 1) := by
      rw [← pow_add, hk]
    have hρk : (ρ : ℝ) ^ (m - 1 - (i : ℕ)) ≠ 0 := pow_ne_zero _ hρne
    rw [hpow, mul_comm ((a i : ℝ)) (ρ ^ (m - 1 - (i : ℕ))),
      mul_div_mul_left _ _ hρk]
  calc ∑ i : Fin m, (a i : ℝ) / ρ ^ ((i : ℕ) + 1)
      = ∑ i : Fin m, (a i : ℝ) * ρ ^ (m - 1 - (i : ℕ)) / ρ ^ m :=
        Finset.sum_congr rfl fun i _ => (hterm i).symm
    _ = ρ ^ m / ρ ^ m := hdiv.symm
    _ = 1 := div_self (pow_ne_zero _ hρne)

-- Dividing the root equation by `ρ ^ m` rescales a root `z` to `z / ρ`.
private theorem scaled_eq (m : ℕ) (a : Fin m → ℕ) (ρ : ℝ) (hρ : 1 < ρ) (z : ℂ)
    (heq : z ^ m = ∑ i : Fin m, (a i : ℂ) * z ^ (m - 1 - (i : ℕ))) :
    (z / (ρ : ℂ)) ^ m =
      ∑ i : Fin m, (((a i : ℝ) / ρ ^ ((i : ℕ) + 1) : ℝ) : ℂ)
        * (z / (ρ : ℂ)) ^ (m - 1 - (i : ℕ)) := by
  have hρC : ((ρ : ℂ)) ≠ 0 := by exact_mod_cast (ne_of_gt (by linarith : (0 : ℝ) < ρ))
  have hdiv := congrArg (· / ((ρ : ℂ) ^ m)) heq
  rw [Finset.sum_div, ← div_pow] at hdiv
  have hterm : ∀ i : Fin m,
      ((a i : ℂ) * z ^ (m - 1 - (i : ℕ))) / (ρ : ℂ) ^ m
        = (((a i : ℝ) / ρ ^ ((i : ℕ) + 1) : ℝ) : ℂ) * (z / (ρ : ℂ)) ^ (m - 1 - (i : ℕ)) := by
    intro i
    have hk : (m - 1 - (i : ℕ)) + ((i : ℕ) + 1) = m := by have := i.isLt; omega
    have hρk : ((ρ : ℂ) ^ (m - 1 - (i : ℕ))) ≠ 0 := pow_ne_zero _ hρC
    have hρi : ((ρ : ℂ) ^ ((i : ℕ) + 1)) ≠ 0 := pow_ne_zero _ hρC
    have hpow : (ρ : ℂ) ^ m = (ρ : ℂ) ^ (m - 1 - (i : ℕ)) * (ρ : ℂ) ^ ((i : ℕ) + 1) := by
      rw [← pow_add, hk]
    rw [div_pow, hpow]
    have hbcast : (((a i : ℝ) / ρ ^ ((i : ℕ) + 1) : ℝ) : ℂ)
        = (a i : ℂ) / (ρ : ℂ) ^ ((i : ℕ) + 1) := by push_cast; ring
    rw [hbcast, div_mul_div_comm,
      mul_comm ((ρ : ℂ) ^ ((i : ℕ) + 1)) ((ρ : ℂ) ^ (m - 1 - (i : ℕ)))]
  rw [hdiv]
  exact Finset.sum_congr rfl fun i _ => hterm i

-- If a point of modulus `1` satisfies the rescaled equation, it is `1`: taking
-- real parts forces the conjugate to have real part `1`.
private theorem eq_of_norm_eq {m : ℕ} (hm : 2 ≤ m) (b : Fin m → ℝ) (hb : ∀ i, 0 < b i)
    (hsum : ∑ i : Fin m, b i = 1) (w : ℂ) (hw : ‖w‖ = 1)
    (heq : w ^ m = ∑ i : Fin m, ((b i : ℝ) : ℂ) * w ^ (m - 1 - (i : ℕ))) :
    w = 1 := by
  set v := starRingEnd ℂ w with hvdef
  have hconj : w * (starRingEnd ℂ w) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw]
    norm_num
  have hwc : (starRingEnd ℂ w) * w = 1 := by rw [mul_comm]; exact hconj
  have hone : (1 : ℂ) = ∑ i : Fin m, ((b i : ℝ) : ℂ) * v ^ ((i : ℕ) + 1) := by
    have h1 : (1 : ℂ) = (starRingEnd ℂ w) ^ m * w ^ m := by
      rw [← mul_pow, hwc, one_pow]
    rw [h1, heq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hsplit : (starRingEnd ℂ w) ^ m
        = (starRingEnd ℂ w) ^ (m - 1 - (i : ℕ)) * (starRingEnd ℂ w) ^ ((i : ℕ) + 1) := by
      rw [← pow_add]
      congr 1
      have := i.isLt; omega
    rw [hsplit]
    have hpow : (starRingEnd ℂ w) ^ (m - 1 - (i : ℕ)) * w ^ (m - 1 - (i : ℕ)) = 1 := by
      rw [← mul_pow, hwc, one_pow]
    calc (starRingEnd ℂ w) ^ (m - 1 - (i : ℕ)) * (starRingEnd ℂ w) ^ ((i : ℕ) + 1)
          * (((b i : ℝ) : ℂ) * w ^ (m - 1 - (i : ℕ)))
        = ((b i : ℝ) : ℂ) * ((starRingEnd ℂ w) ^ (m - 1 - (i : ℕ)) * w ^ (m - 1 - (i : ℕ)))
          * (starRingEnd ℂ w) ^ ((i : ℕ) + 1) := by ring
      _ = ((b i : ℝ) : ℂ) * v ^ ((i : ℕ) + 1) := by rw [hpow]; simp [hvdef]
  have hre : (1 : ℝ) = ∑ i : Fin m, (b i) * (v ^ ((i : ℕ) + 1)).re := by
    have h := congrArg Complex.re hone
    simpa using h
  have hnormv : ‖v‖ = 1 := by rw [hvdef]; simp [hw]
  have hre_le : ∀ i : Fin m, (v ^ ((i : ℕ) + 1)).re ≤ 1 := by
    intro i
    calc (v ^ ((i : ℕ) + 1)).re ≤ |(v ^ ((i : ℕ) + 1)).re| := le_abs_self _
      _ ≤ ‖v ^ ((i : ℕ) + 1)‖ := Complex.abs_re_le_norm _
      _ = 1 := by rw [norm_pow, hnormv, one_pow]
  have hvre : v.re = 1 := by
    by_contra hne
    have hle0 : v.re ≤ 1 := by
      have h0 := hre_le ⟨0, by omega⟩
      simpa using h0
    have hlt1 : v.re < 1 := lt_of_le_of_ne hle0 hne
    have hterm_le : ∀ i : Fin m, (b i) * (v ^ ((i : ℕ) + 1)).re ≤ b i := by
      intro i
      exact mul_le_of_le_one_right (hb i).le (hre_le i)
    have hterm_lt : (b ⟨0, by omega⟩) * (v ^ ((⟨0, by omega⟩ : Fin m).val + 1)).re
        < b ⟨0, by omega⟩ := by
      have h0 : (v ^ ((⟨0, by omega⟩ : Fin m).val + 1)).re = v.re := by simp
      rw [h0]
      exact mul_lt_of_lt_one_right (hb _) hlt1
    have hlt : ∑ i : Fin m, (b i) * (v ^ ((i : ℕ) + 1)).re < ∑ i : Fin m, b i :=
      Finset.sum_lt_sum (fun i _ => hterm_le i) ⟨⟨0, by omega⟩, Finset.mem_univ _, hterm_lt⟩
    rw [hsum] at hlt
    linarith [hre]
  have hv_im : v.im = 0 := by
    have hns : Complex.normSq v = 1 := by
      rw [Complex.normSq_eq_norm_sq, hnormv]; norm_num
    rw [Complex.normSq_apply, hvre] at hns
    have hsq : v.im ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp hsq
  have hv1 : v = 1 := by
    apply Complex.ext
    · exact hvre
    · rw [hv_im]; simp
  have hw1 : w = 1 := by
    have h := congrArg (starRingEnd ℂ) hv1
    simp only [hvdef, starRingEnd_apply, star_star, star_one] at h
    exact h
  exact hw1

-- Every complex root has modulus at most `ρ`, with equality only at `ρ` itself.
private theorem classify_root {m : ℕ} (hm : 2 ≤ m) (a : Fin m → ℕ) (ha : ∀ i, 0 < a i)
    (φ : ℤ[X])
    (hφ : φ = X ^ m - ∑ i : Fin m, C (a i : ℤ) * X ^ (m - 1 - (i : ℕ))) (ρ : ℝ)
    (hρ1 : 1 < ρ) (hρg : ρ - ∑ i : Fin m, (a i : ℝ) / ρ ^ (i : ℕ) = 0)
    (hρeq : ρ ^ m = ∑ i : Fin m, (a i : ℝ) * ρ ^ (m - 1 - (i : ℕ))) (z : ℂ)
    (hzroot : eval z (φ.map (Int.castRingHom ℂ)) = 0) :
    ‖z‖ ≤ ρ ∧ (‖z‖ = ρ → z = (ρ : ℂ)) := by
  have hρpos : 0 < ρ := by linarith
  have heq := root_eq m a φ hφ z hzroot
  have hz0 := root_ne_zero hm a ha z heq
  have hle := norm_le_of_root hm a ρ hρpos hρg (strictMono_aux a) z hz0 heq
  refine ⟨hle, fun hnorm => ?_⟩
  have hρC : ((ρ : ℂ)) ≠ 0 := by exact_mod_cast (ne_of_gt hρpos)
  have hw_norm : ‖z / (ρ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρpos, hnorm]
    exact div_self hρpos.ne'
  have hscaled := scaled_eq m a ρ hρ1 z heq
  have hsum := sum_b_eq_one a ρ hρpos hρeq
  have hb : ∀ i : Fin m, 0 < (a i : ℝ) / ρ ^ ((i : ℕ) + 1) := by
    intro i
    exact div_pos (by exact_mod_cast ha i) (pow_pos hρpos _)
  have hw1 := eq_of_norm_eq hm (fun i => (a i : ℝ) / ρ ^ ((i : ℕ) + 1)) hb hsum
    (z / (ρ : ℂ)) hw_norm hscaled
  have hz' : z = (z / (ρ : ℂ)) * (ρ : ℂ) := (div_mul_cancel₀ z hρC).symm
  rw [hw1] at hz'
  simpa using hz'

-- The derivative of `φ`, in the same form.
private theorem derivative_eq (m : ℕ) (a : Fin m → ℕ) (φ : ℤ[X])
    (hφ : φ = X ^ m - ∑ i : Fin m, C (a i : ℤ) * X ^ (m - 1 - (i : ℕ))) :
    derivative φ = C (m : ℤ) * X ^ (m - 1)
      - ∑ i : Fin m, C ((a i : ℤ) * ((m - 1 - (i : ℕ) : ℕ) : ℤ))
        * X ^ ((m - 1 - (i : ℕ)) - 1) := by
  rw [hφ]
  simp only [Polynomial.derivative_sub, Polynomial.derivative_X_pow,
    Polynomial.derivative_sum, Polynomial.derivative_C_mul_X_pow]

-- The derivative of the image polynomial, in the same form.
private theorem derivative_map_eq (m : ℕ) (a : Fin m → ℕ) (φ : ℤ[X])
    (hφ : φ = X ^ m - ∑ i : Fin m, C (a i : ℤ) * X ^ (m - 1 - (i : ℕ))) :
    derivative (φ.map (Int.castRingHom ℂ)) = C (m : ℂ) * X ^ (m - 1)
      - ∑ i : Fin m, C ((a i : ℂ) * ((m - 1 - (i : ℕ) : ℕ) : ℂ))
        * X ^ ((m - 1 - (i : ℕ)) - 1) := by
  rw [Polynomial.derivative_map, derivative_eq m a φ hφ, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_sum]
  congr 1
  simp

-- The derivative at `ρ` is positive: multiplying by `ρ` and using the equation at
-- `ρ` rewrites it as a sum of positive terms.
private theorem derivative_pos {m : ℕ} (hm : 2 ≤ m) (a : Fin m → ℕ) (ha : ∀ i, 0 < a i)
    (φ : ℤ[X])
    (hφ : φ = X ^ m - ∑ i : Fin m, C (a i : ℤ) * X ^ (m - 1 - (i : ℕ))) (ρ : ℝ)
    (hρpos : 0 < ρ)
    (hρeq : ρ ^ m = ∑ i : Fin m, (a i : ℝ) * ρ ^ (m - 1 - (i : ℕ))) :
    0 < aeval ρ (derivative φ) := by
  have hDexpr : aeval ρ (derivative φ)
      = (m : ℝ) * ρ ^ (m - 1)
        - ∑ i : Fin m, ((a i : ℝ) * ((m - 1 - (i : ℕ) : ℕ) : ℝ))
          * ρ ^ ((m - 1 - (i : ℕ)) - 1) := by
    rw [derivative_eq m a φ hφ]
    simp
  rw [hDexpr]
  set D := (m : ℝ) * ρ ^ (m - 1)
      - ∑ i : Fin m, ((a i : ℝ) * ((m - 1 - (i : ℕ) : ℕ) : ℝ))
        * ρ ^ ((m - 1 - (i : ℕ)) - 1) with hDdef
  have hterm : ∀ i : Fin m,
      ρ * (((a i : ℝ) * ((m - 1 - (i : ℕ) : ℕ) : ℝ)) * ρ ^ ((m - 1 - (i : ℕ)) - 1))
        = ((a i : ℝ) * ((m - 1 - (i : ℕ) : ℕ) : ℝ)) * ρ ^ (m - 1 - (i : ℕ)) := by
    intro i
    by_cases h0 : m - 1 - (i : ℕ) = 0
    · have hcast : ((m - 1 - (i : ℕ) : ℕ) : ℝ) = 0 := by rw [h0]; norm_num
      simp [hcast]
    · have hge : 1 ≤ m - 1 - (i : ℕ) := by omega
      have hexp : (m - 1 - (i : ℕ)) - 1 + 1 = m - 1 - (i : ℕ) := by omega
      calc ρ * (((a i : ℝ) * ((m - 1 - (i : ℕ) : ℕ) : ℝ)) * ρ ^ ((m - 1 - (i : ℕ)) - 1))
          = ((a i : ℝ) * ((m - 1 - (i : ℕ) : ℕ) : ℝ)) * (ρ * ρ ^ ((m - 1 - (i : ℕ)) - 1)) := by
            ring
        _ = ((a i : ℝ) * ((m - 1 - (i : ℕ) : ℕ) : ℝ)) * ρ ^ (m - 1 - (i : ℕ)) := by
            rw [← pow_succ', hexp]
  have hρD : ρ * D
      = ∑ i : Fin m, ((a i : ℝ) * (((i : ℕ) + 1 : ℕ) : ℝ)) * ρ ^ (m - 1 - (i : ℕ)) := by
    rw [hDdef, mul_sub, Finset.mul_sum]
    have h1 : ρ * ((m : ℝ) * ρ ^ (m - 1)) = (m : ℝ) * ρ ^ m := by
      have hm1 : m - 1 + 1 = m := by omega
      calc ρ * ((m : ℝ) * ρ ^ (m - 1)) = (m : ℝ) * (ρ * ρ ^ (m - 1)) := by ring
        _ = (m : ℝ) * ρ ^ ((m - 1) + 1) := by rw [← pow_succ']
        _ = (m : ℝ) * ρ ^ m := by rw [hm1]
    rw [h1, hρeq, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hterm i]
    have hcoeff : (m : ℝ) - ((m - 1 - (i : ℕ) : ℕ) : ℝ) = ((i : ℝ) + 1) := by
      have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ m)]
        norm_num
      rw [Nat.cast_sub (show (i : ℕ) ≤ m - 1 by have := i.isLt; omega), hm1]
      ring
    calc (m : ℝ) * ((a i : ℝ) * ρ ^ (m - 1 - (i : ℕ)))
          - ((a i : ℝ) * ((m - 1 - (i : ℕ) : ℕ) : ℝ)) * ρ ^ (m - 1 - (i : ℕ))
        = ((a i : ℝ) * ρ ^ (m - 1 - (i : ℕ))) * ((m : ℝ) - ((m - 1 - (i : ℕ) : ℕ) : ℝ)) := by
          ring
      _ = ((a i : ℝ) * ρ ^ (m - 1 - (i : ℕ))) * ((i : ℝ) + 1) := by rw [hcoeff]
      _ = ((a i : ℝ) * (((i : ℕ) + 1 : ℕ) : ℝ)) * ρ ^ (m - 1 - (i : ℕ)) := by
          push_cast
          ring
  have hsumpos : 0
      < ∑ i : Fin m, ((a i : ℝ) * (((i : ℕ) + 1 : ℕ) : ℝ)) * ρ ^ (m - 1 - (i : ℕ)) := by
    apply Finset.sum_pos
    · intro i _
      apply mul_pos
      · apply mul_pos
        · exact_mod_cast ha i
        · positivity
      · exact pow_pos hρpos _
    · have h0 : (0 : ℕ) < m := by omega
      have hne : Nonempty (Fin m) := ⟨⟨0, h0⟩⟩
      exact Finset.univ_nonempty_iff.mpr hne
  have hρDpos : 0 < ρ * D := by rw [hρD]; exact hsumpos
  exact pos_of_mul_pos_right hρDpos hρpos.le

-- Hence `ρ` is not a root of the derivative: it is a simple root.
private theorem derivative_eval_ne {m : ℕ} (hm : 2 ≤ m) (a : Fin m → ℕ)
    (ha : ∀ i, 0 < a i) (φ : ℤ[X])
    (hφ : φ = X ^ m - ∑ i : Fin m, C (a i : ℤ) * X ^ (m - 1 - (i : ℕ))) (ρ : ℝ)
    (hρpos : 0 < ρ)
    (hρeq : ρ ^ m = ∑ i : Fin m, (a i : ℝ) * ρ ^ (m - 1 - (i : ℕ))) :
    eval (ρ : ℂ) (derivative (φ.map (Int.castRingHom ℂ))) ≠ 0 := by
  have hcast : eval (ρ : ℂ) (derivative (φ.map (Int.castRingHom ℂ)))
      = ((aeval ρ (derivative φ) : ℝ) : ℂ) := by
    rw [derivative_map_eq m a φ hφ, derivative_eq m a φ hφ]
    simp [eval_finsetSum]
  rw [hcast]
  have hD := derivative_pos hm a ha φ hφ ρ hρpos hρeq
  exact_mod_cast hD.ne'

end exists_dominant_root_of_pos_coeff_charPoly

/-- **Dominant root of $x^m - a_1 x^{m-1} - \cdots - a_m$ with positive coefficients.** Let
$m \ge 2$ and let $a_1, \dots, a_m$ be positive integers. Then the polynomial
$\varphi(x) = x^m - a_1 x^{m-1} - \cdots - a_m$ has exactly one positive real root $\lambda$,
this root satisfies $\lambda > 1$, and the complex roots of $\varphi$, counted with
multiplicity, are $\lambda$ (a simple root) together with $m - 1$ roots of modulus less than
$\lambda$.

Source: Tingting Du, *On the Reciprocal Sums and Products of m th-order Linear Recursive
Sequences*, Journal of Integer Sequences 27 (2024), Article 24.2.3, Lemma 4
(`jis-2024-24.2.3-lem-4`). -/
theorem exists_dominant_root_of_pos_coeff_charPoly
    (m : ℕ) (hm : 2 ≤ m) (a : Fin m → ℕ) (ha : ∀ i, 0 < a i) (φ : ℤ[X])
    (hφ : φ = X ^ m - ∑ i : Fin m, C (a i : ℤ) * X ^ (m - 1 - (i : ℕ))) :
    ∃ ρ : ℝ, 1 < ρ ∧ (∀ x : ℝ, 0 < x → aeval x φ = 0 → x = ρ) ∧
      ∃ s : Multiset ℂ, (φ.map (Int.castRingHom ℂ)).roots = (ρ : ℂ) ::ₘ s ∧
        ∀ z ∈ s, ‖z‖ < ρ := by
  obtain ⟨ρ, hρ1, huniq, hρg, hρeq⟩ :=
    exists_dominant_root_of_pos_coeff_charPoly.real_root m hm a ha φ hφ
  have hρpos : 0 < ρ := by linarith
  obtain ⟨hdeg, hqne⟩ :=
    exists_dominant_root_of_pos_coeff_charPoly.natDegree_eq m a φ hφ
  set q := φ.map (Int.castRingHom ℂ) with hqdef
  have hρroot : q.IsRoot (ρ : ℂ) := by
    have hC : (ρ : ℂ) ^ m = ∑ i : Fin m, (a i : ℂ) * (ρ : ℂ) ^ (m - 1 - (i : ℕ)) := by
      exact_mod_cast hρeq
    have hqeq := exists_dominant_root_of_pos_coeff_charPoly.map_eq m a φ hφ
    change eval (ρ : ℂ) q = 0
    rw [hqdef, hqeq]
    simp only [eval_sub, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C]
    rw [hC, sub_self]
  have hρmem : (ρ : ℂ) ∈ q.roots := (Polynomial.mem_roots hqne).mpr hρroot
  have hcount : q.roots.count (ρ : ℂ) = 1 := by
    rw [Polynomial.count_roots]
    have hmult_pos : 0 < Polynomial.rootMultiplicity (ρ : ℂ) q :=
      (Polynomial.rootMultiplicity_pos hqne).mpr hρroot
    have hnot : ¬ 1 < Polynomial.rootMultiplicity (ρ : ℂ) q := by
      intro hlt
      rw [Polynomial.one_lt_rootMultiplicity_iff_isRoot hqne] at hlt
      exact exists_dominant_root_of_pos_coeff_charPoly.derivative_eval_ne hm a ha φ hφ ρ
        hρpos hρeq hlt.2
    omega
  refine ⟨ρ, hρ1, huniq, q.roots.erase (ρ : ℂ), (Multiset.cons_erase hρmem).symm, ?_⟩
  intro z hz
  have hzmem : z ∈ q.roots := Multiset.mem_of_mem_erase hz
  have hzroot : eval z q = 0 := (Polynomial.mem_roots hqne).mp hzmem
  have hclassify := exists_dominant_root_of_pos_coeff_charPoly.classify_root hm a ha φ hφ ρ
    hρ1 hρg hρeq z hzroot
  have hne : z ≠ (ρ : ℂ) := by
    intro hzz
    subst hzz
    have hpos : 0 < (q.roots.erase (ρ : ℂ)).count (ρ : ℂ) := Multiset.count_pos.mpr hz
    rw [Multiset.count_erase_self, hcount] at hpos
    simp at hpos
  rcases eq_or_lt_of_le hclassify.1 with h | h
  · exact absurd (hclassify.2 h) hne
  · exact h

end MetaMathlibExt
