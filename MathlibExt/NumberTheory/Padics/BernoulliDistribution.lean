/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.NumberTheory.Padics.PadicNumbers
import MathlibExt.Algebra.BigOperators.AffineEmod
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The Bernoulli distributions on `ℤ_[p]` and the Mazur measure

A `p`-adic distribution on `ℤ_[p]` is a finitely additive `ℚ_[p]`-valued function on compact open
sets. Every compact open set is a finite disjoint union of balls `a + p ^ N ℤ_[p]`, so a
distribution is determined by its values on balls, subject to the distribution relation
`μ(a + p ^ N ℤ_[p]) = ∑_{b < p} μ(a + b p ^ N + p ^ (N + 1) ℤ_[p])`. This file encodes
distributions by these ball values: `μ N a` stands for `μ(a + p ^ N ℤ_[p])`, `0 ≤ a < p ^ N`.

The `k`-th Bernoulli distribution is `μ_k(a + p ^ N ℤ_[p]) = p ^ (N (k - 1)) B_k(a / p ^ N)`,
where `B_k` is the `k`-th Bernoulli polynomial. For an integer `α` prime to `p`, its
regularisation is `μ_{k,α}(U) = μ_k(U) - α ^ (-k) μ_k(α U)`; `μ_{1,α}` is the Mazur measure.

## Main definitions

* `MetaMathlibExt.IsPadicDistribution`: the distribution relation for a family of ball values.
* `MetaMathlibExt.IsBoundedPadicDistribution`: a distribution with bounded values on balls
  (a `p`-adic measure).
* `MetaMathlibExt.bernoulliDist`: the Bernoulli distribution `μ_k`.
* `MetaMathlibExt.regBernoulliDist`: the regularised Bernoulli distribution `μ_{k,α}`.

## Main statements

* `Polynomial.pow_mul_sum_bernoulli_eval_add_div`: the multiplication formula
  `m ^ n ∑_{b < m} B_n(x + b / m) = m B_n(m x)`.
* `MetaMathlibExt.bernoulliDist_isPadicDistribution`: `μ_k` is a distribution.
* `MetaMathlibExt.regBernoulliDist_one_isBoundedPadicDistribution`: the Mazur distribution
  `μ_{1,α}` is a measure, with values of norm at most `1`.
* `MetaMathlibExt.norm_regBernoulliDist_sub_mul_regBernoulliDist_one_le`: Kummer-type congruence
  `d μ_{k,α}(a + p ^ N ℤ_[p]) ≡ d k a ^ (k - 1) μ_{1,α}(a + p ^ N ℤ_[p]) (mod p ^ N)`, where
  `d` clears the denominators of `B_k`.
* `MetaMathlibExt.sum_regBernoulliDist_units_eq`:
  `μ_{k,α}(ℤ_[p]ˣ) = (1 - α ^ (-k)) (1 - p ^ (k - 1)) B_k`.
-/

@[expose] public section

namespace MetaMathlibExt

/-- A `p`-adic distribution on `ℤ_[p]`, encoded by its values on balls: `μ N a` is
`μ(a + p ^ N ℤ_[p])` (only `a < p ^ N` matters). The family is a distribution exactly when
`μ(a + p ^ N ℤ_[p]) = ∑_{b=0}^{p-1} μ(a + b p ^ N + p ^ (N + 1) ℤ_[p])` for every `N` and
`a < p ^ N`. -/
def IsPadicDistribution (p : ℕ) [Fact p.Prime] (μ : ℕ → ℕ → ℚ_[p]) : Prop :=
  ∀ N a, a < p ^ N → μ N a = ∑ b ∈ Finset.range p, μ (N + 1) (a + b * p ^ N)

/-- A `p`-adic measure on `ℤ_[p]`, encoded by its values on balls: a `p`-adic distribution whose
values `μ(a + p ^ N ℤ_[p])`, `0 ≤ a < p ^ N`, are bounded in norm. -/
def IsBoundedPadicDistribution (p : ℕ) [Fact p.Prime] (μ : ℕ → ℕ → ℚ_[p]) : Prop :=
  IsPadicDistribution p μ ∧ ∃ B : ℝ, ∀ N a, a < p ^ N → ‖μ N a‖ ≤ B

/-- The `k`-th Bernoulli distribution `μ_k` on `ℤ_[p]`, given by its values on balls:
`bernoulliDist p k N a = μ_k(a + p ^ N ℤ_[p]) = p ^ (N (k - 1)) B_k(a / p ^ N)`, where `B_k` is
the `k`-th Bernoulli polynomial (`Polynomial.bernoulli k`, with `B_1(x) = x - 1/2`). The value is
computed in `ℚ` and cast to `ℚ_[p]`. -/
noncomputable def bernoulliDist (p : ℕ) [Fact p.Prime] (k N a : ℕ) : ℚ_[p] :=
  (((p : ℚ) ^ ((N : ℤ) * ((k : ℤ) - 1)) *
      (Polynomial.bernoulli k).eval ((a : ℚ) / (p : ℚ) ^ N) : ℚ) : ℚ_[p])

/-- The regularised Bernoulli distribution `μ_{k,α}(U) = μ_k(U) - α ^ (-k) μ_k(α U)`, given by its
values on balls: `μ_{k,α}(a + p ^ N ℤ_[p]) = μ_k(a + p ^ N ℤ_[p]) - α ^ (-k) μ_k(r + p ^ N ℤ_[p])`,
where `r ∈ [0, p ^ N)` is congruent to `α a` modulo `p ^ N`. For `k = 1` this is the Mazur
distribution. The statements about it assume `α` prime to `p`. -/
noncomputable def regBernoulliDist (p : ℕ) [Fact p.Prime] (k : ℕ) (α : ℤ) (N a : ℕ) : ℚ_[p] :=
  bernoulliDist p k N a -
    (α : ℚ_[p]) ^ (-(k : ℤ)) * bernoulliDist p k N ((α * a) % (p : ℤ) ^ N).toNat

private lemma sum_rescale_exp_mul_eq_exp_sub_one (p : ℕ) (hp : (p : ℚ) ≠ 0) :
    (∑ b ∈ Finset.range p, PowerSeries.rescale ((b : ℚ) / p) (PowerSeries.exp ℚ)) *
      (PowerSeries.rescale (1 / (p : ℚ)) (PowerSeries.exp ℚ) - 1) = PowerSeries.exp ℚ - 1 := by
  have hx : ∀ b : ℕ, PowerSeries.rescale ((b : ℚ) / p) (PowerSeries.exp ℚ) =
      (PowerSeries.rescale (1 / (p : ℚ)) (PowerSeries.exp ℚ)) ^ b := by
    intro b
    rw [← map_pow, PowerSeries.exp_pow_eq_rescale_exp, PowerSeries.rescale_rescale,
      mul_one_div]
  simp_rw [hx]
  rw [geom_sum_mul, ← hx, div_self hp, PowerSeries.rescale_one]
  rfl

/-- The multiplication formula over `ℚ` in the form used below:
`∑_{b < p} B_n(x + b / p) = p ^ (1 - n) B_n(p x)`. -/
private lemma sum_bernoulli_eval_add_div_aux (p : ℕ) (hp : (p : ℚ) ≠ 0) (x : ℚ) (n : ℕ) :
    ∑ b ∈ Finset.range p, (Polynomial.bernoulli n).eval (x + b / p) =
      p * (1 / (p : ℚ)) ^ n * (Polynomial.bernoulli n).eval (p * x) := by
  set E := PowerSeries.exp ℚ with hE
  let F : ℚ → PowerSeries ℚ := fun y =>
    PowerSeries.mk fun n => Polynomial.aeval y ((1 / n.factorial : ℚ) • Polynomial.bernoulli n)
  have h1 : ∀ y, F y * (E - 1) = PowerSeries.X * PowerSeries.rescale y E := fun y =>
    Polynomial.bernoulli_generating_function y
  set G := PowerSeries.rescale (1 / (p : ℚ)) (F (p * x)) with hG
  have hG1 : G * (PowerSeries.rescale (1 / (p : ℚ)) E - 1) =
      PowerSeries.C (1 / (p : ℚ)) * PowerSeries.X * PowerSeries.rescale x E := by
    have := congrArg (PowerSeries.rescale (1 / (p : ℚ))) (h1 (p * x))
    rw [map_mul, map_sub, map_one, map_mul, PowerSeries.rescale_X,
      PowerSeries.rescale_rescale] at this
    rw [hG, this]
    congr 2
    field_simp
  have hS : (∑ b ∈ Finset.range p, F (x + b / p)) * (E - 1) =
      PowerSeries.X * PowerSeries.rescale x E *
        ∑ b ∈ Finset.range p, PowerSeries.rescale ((b : ℚ) / p) E := by
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [h1, ← PowerSeries.exp_mul_exp_eq_exp_add, mul_assoc]
  have hE1 : E - 1 ≠ 0 := by
    intro h
    have := congrArg (PowerSeries.coeff 1) h
    simp [hE, PowerSeries.coeff_exp] at this
  have key : ∑ b ∈ Finset.range p, F (x + b / p) = PowerSeries.C (p : ℚ) * G := by
    apply mul_right_cancel₀ hE1
    have geom := sum_rescale_exp_mul_eq_exp_sub_one p hp
    rw [← hE] at geom
    have hc : PowerSeries.C (p : ℚ) * PowerSeries.C (1 / (p : ℚ)) = 1 := by
      rw [← map_mul, mul_one_div_cancel hp, map_one]
    rw [hS]
    linear_combination (PowerSeries.C (p : ℚ) * G) * geom -
      (PowerSeries.C (p : ℚ) * ∑ b ∈ Finset.range p, PowerSeries.rescale ((b : ℚ) / p) E) * hG1 -
      (PowerSeries.X * PowerSeries.rescale x E *
        ∑ b ∈ Finset.range p, PowerSeries.rescale ((b : ℚ) / p) E) * hc
  have := congrArg (PowerSeries.coeff n) key
  simp only [map_sum, F, hG, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_rescale, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
    Algebra.algebraMap_self, Polynomial.map_id, Polynomial.eval_smul, smul_eq_mul] at this
  have hf : (n.factorial : ℚ) ≠ 0 := by positivity
  rw [← Finset.mul_sum] at this
  apply mul_left_cancel₀ (one_div_ne_zero hf)
  linear_combination this

end MetaMathlibExt

namespace Polynomial

/-- **Multiplication formula for Bernoulli polynomials** (Raabe):
`m ^ n ∑_{b < m} B_n(x + b / m) = m B_n(m x)`, i.e.
`∑_{b < m} B_n(x + b / m) = m ^ (1 - n) B_n(m x)` for `m ≠ 0`. -/
theorem pow_mul_sum_bernoulli_eval_add_div (m n : ℕ) (x : ℚ) :
    (m : ℚ) ^ n * ∑ b ∈ Finset.range m, (bernoulli n).eval (x + b / m) =
      m * (bernoulli n).eval (m * x) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  have h : (m : ℚ) ^ n * (1 / (m : ℚ)) ^ n = 1 := by
    rw [← mul_pow, mul_one_div_cancel hm', one_pow]
  rw [MetaMathlibExt.sum_bernoulli_eval_add_div_aux m hm' x n]
  linear_combination (m : ℚ) * (bernoulli n).eval (m * x) * h

end Polynomial

namespace MetaMathlibExt

/-- The Bernoulli ball values `μ_k(a + p ^ N ℤ_[p]) = p ^ (N (k - 1)) B_k(a / p ^ N)` satisfy the
distribution relation, so `μ_k` is a `p`-adic distribution on `ℤ_[p]`. -/
theorem bernoulliDist_isPadicDistribution (p : ℕ) [Fact p.Prime] (k : ℕ) :
    IsPadicDistribution p (bernoulliDist p k) := by
  intro N a _
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  unfold bernoulliDist
  rw [← Rat.cast_sum]
  congr 1
  have harg : ∀ b : ℕ, (((a + b * p ^ N : ℕ) : ℚ) / (p : ℚ) ^ (N + 1)) =
      (a : ℚ) / (p : ℚ) ^ (N + 1) + b / p := by
    intro b
    push_cast
    field_simp
    ring
  simp_rw [harg]
  rw [← Finset.mul_sum, sum_bernoulli_eval_add_div_aux p hp]
  have hx : (p : ℚ) * ((a : ℚ) / (p : ℚ) ^ (N + 1)) = (a : ℚ) / (p : ℚ) ^ N := by
    field_simp
    ring
  rw [hx]
  have hz : ((N + 1 : ℕ) : ℤ) * ((k : ℤ) - 1) = (N : ℤ) * ((k : ℤ) - 1) + ((k : ℤ) - 1) := by
    push_cast; ring
  rw [hz, zpow_add₀ hp, zpow_sub₀ hp, zpow_natCast, zpow_one, one_div, inv_pow]
  field_simp

/-- An integer prime to a prime `p` is not divisible by `p`. -/
private lemma prime_not_dvd_of_isCoprime (p : ℕ) [Fact p.Prime] (α : ℤ)
    (hα : IsCoprime α (p : ℤ)) : ¬ (p : ℤ) ∣ α := by
  intro h
  have hu := hα.isUnit_of_dvd' h dvd_rfl
  rw [Int.isUnit_iff] at hu
  have := (Fact.out : p.Prime).one_lt
  omega

/-- Closed form of the Mazur distribution:
`μ_{1,α}(a + p ^ N ℤ_[p]) = (2 ⌊α a / p ^ N⌋ + 1 - α) / (2 α)`. -/
theorem regBernoulliDist_one_eq (p : ℕ) [Fact p.Prime] {α : ℤ} (hα0 : α ≠ 0) (N a : ℕ) :
    regBernoulliDist p 1 α N a =
      ((2 * (α * a / (p : ℤ) ^ N) + 1 - α : ℤ) : ℚ_[p]) / (2 * (α : ℚ_[p])) := by
  have hp : (p : ℤ) ^ N ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hnn : 0 ≤ α * a % (p : ℤ) ^ N := Int.emod_nonneg _ hp
  have hcast : ((((α * a) % (p : ℤ) ^ N).toNat : ℕ) : ℚ) =
      (((α * a) % (p : ℤ) ^ N : ℤ) : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hnn
  have hdef := Int.emod_add_mul_ediv (α * a) ((p : ℤ) ^ N)
  unfold regBernoulliDist bernoulliDist
  rw [hcast, Polynomial.bernoulli_one]
  have hpQ : (p : ℚ) ^ N ≠ 0 := by exact_mod_cast hp
  have hαQ : (α : ℚ_[p]) ≠ 0 := by exact_mod_cast hα0
  set r := α * a % (p : ℤ) ^ N with hr
  set m := α * a / (p : ℤ) ^ N with hm
  have hrQ : (r : ℚ) = α * a - (p : ℚ) ^ N * m := by
    have : ((r + (p : ℤ) ^ N * m : ℤ) : ℚ) = ((α * a : ℤ) : ℚ) := by rw [hdef]
    push_cast at this; linarith
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Nat.cast_one, sub_self,
    mul_zero, zpow_zero, one_mul, hrQ]
  rw [zpow_neg_one]
  have hinvα : ((α : ℚ_[p]))⁻¹ = (((α : ℚ)⁻¹ : ℚ) : ℚ_[p]) := by push_cast; rfl
  have hrhs : ((2 * m + 1 - α : ℤ) : ℚ_[p]) / (2 * (α : ℚ_[p])) =
      ((((2 * m + 1 - α : ℤ) : ℚ) / (2 * (α : ℚ)) : ℚ) : ℚ_[p]) := by push_cast; rfl
  rw [hinvα, hrhs, ← Rat.cast_mul, ← Rat.cast_sub]
  congr 1
  have hαq : (α : ℚ) ≠ 0 := by exact_mod_cast hα0
  push_cast
  field_simp
  ring

/-- For `α` prime to `p`, the Mazur distribution `μ_{1,α}` satisfies the distribution
relation. -/
theorem regBernoulliDist_one_isPadicDistribution (p : ℕ) [Fact p.Prime] {α : ℤ}
    (hα : IsCoprime α (p : ℤ)) : IsPadicDistribution p (regBernoulliDist p 1 α) := by
  have hα0 : α ≠ 0 := by
    rintro rfl
    exact prime_not_dvd_of_isCoprime p 0 hα (dvd_zero _)
  intro N a _
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hq : 0 < (p : ℤ) ^ N := pow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) N
  simp_rw [regBernoulliDist_one_eq p hα0]
  rw [← Finset.sum_div, ← Int.cast_sum]
  congr 2
  set m := α * a / (p : ℤ) ^ N with hm
  have hb : ∀ b : ℕ, α * ((a + b * p ^ N : ℕ) : ℤ) / (p : ℤ) ^ (N + 1) = (m + α * b) / p := by
    intro b
    push_cast
    rw [pow_succ, ← Int.ediv_ediv_of_nonneg hq.le]
    congr 1
    rw [show α * ((a : ℤ) + b * (p : ℤ) ^ N) = α * a + (α * b) * (p : ℤ) ^ N by ring,
      Int.add_mul_ediv_right _ _ hq.ne']
  simp_rw [hb]
  set S := ∑ b ∈ Finset.range p, (m + α * b) / p with hS
  set T := ∑ b ∈ Finset.range p, (b : ℤ) with hTdef
  have hT : T * 2 = p * (p - 1) := by
    have h := Finset.sum_range_id_mul_two p
    have h1 := (Fact.out : p.Prime).one_le
    have h2 : ((∑ i ∈ Finset.range p, i : ℕ) : ℤ) * 2 = (p : ℤ) * ((p - 1 : ℕ) : ℤ) := by
      exact_mod_cast h
    rw [Nat.cast_sum, Nat.cast_sub h1] at h2
    simpa using h2
  have hPS : (p : ℤ) * S = p * m + α * T - T := by
    rw [hS, Finset.mul_sum]
    have : ∀ b ∈ Finset.range p, (p : ℤ) * ((m + α * b) / p) =
        (m + α * b) - (m + α * b) % p := by
      intro b _
      have := Int.emod_add_mul_ediv (m + α * b) p
      linarith
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib,
      Finset.sum_range_add_mul_emod hα m (fun x => x),
      Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [hTdef]
  have hsplit : ∑ b ∈ Finset.range p, (2 * ((m + α * b) / p) + 1 - α) =
      2 * S + p * (1 - α) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
    ring
  rw [hsplit]
  apply mul_left_cancel₀ hp0
  linear_combination -2 * hPS - (α - 1) * hT

/-- For `α` prime to `p`, every ball value of the Mazur distribution has norm at most `1`. -/
theorem norm_regBernoulliDist_one_le (p : ℕ) [Fact p.Prime] {α : ℤ}
    (hα : IsCoprime α (p : ℤ)) (N a : ℕ) : ‖regBernoulliDist p 1 α N a‖ ≤ 1 := by
  have hα0 : α ≠ 0 := by
    rintro rfl
    exact prime_not_dvd_of_isCoprime p 0 hα (dvd_zero _)
  rw [regBernoulliDist_one_eq p hα0]
  have hnd := prime_not_dvd_of_isCoprime p α hα
  have hαn : ‖(α : ℚ_[p])‖ = 1 :=
    le_antisymm (Padic.norm_int_le_one α)
      (not_lt.mp (mt Padic.norm_intCast_lt_one_iff.mp hnd))
  have hαQ : (α : ℚ_[p]) ≠ 0 := by exact_mod_cast hα0
  set m := α * a / (p : ℤ) ^ N
  by_cases hp2 : p = 2
  · subst hp2
    have hodd : α % 2 = 1 := by
      have : ¬ (2 : ℤ) ∣ α := by exact_mod_cast hnd
      omega
    obtain ⟨k, hk⟩ : ∃ k : ℤ, 1 - α = 2 * k := ⟨(1 - α) / 2, by omega⟩
    have e : ((2 * m + 1 - α : ℤ) : ℚ_[2]) / (2 * (α : ℚ_[2])) =
        ((m + k : ℤ) : ℚ_[2]) / α := by
      rw [show 2 * m + 1 - α = 2 * (m + k) by linarith]
      push_cast
      field_simp
    rw [e, norm_div, hαn, div_one]
    exact Padic.norm_int_le_one _
  · have h2 : ‖((2 : ℤ) : ℚ_[p])‖ = 1 := by
      refine le_antisymm (Padic.norm_int_le_one 2)
        (not_lt.mp (mt Padic.norm_intCast_lt_one_iff.mp ?_))
      intro h
      have h' : p ∣ 2 := by exact_mod_cast h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h')
    rw [norm_div, norm_mul, hαn]
    push_cast at h2
    rw [h2, mul_one, div_one]
    exact Padic.norm_int_le_one _

/-- For an integer `α` prime to `p`, the Mazur distribution `μ_{1,α}` is a `p`-adic measure. -/
theorem regBernoulliDist_one_isBoundedPadicDistribution (p : ℕ) [Fact p.Prime] {α : ℤ}
    (hα : IsCoprime α (p : ℤ)) : IsBoundedPadicDistribution p (regBernoulliDist p 1 α) :=
  ⟨regBernoulliDist_one_isPadicDistribution p hα, 1,
    fun N a _ => norm_regBernoulliDist_one_le p hα N a⟩

private lemma norm_le_of_pow_mul_eq_prime_pow_mul (p : ℕ) [Fact p.Prime] (α : ℤ)
    (hα : IsCoprime α (p : ℤ)) (k N : ℕ) (X : ℚ_[p]) (M : ℤ)
    (h : (α : ℚ_[p]) ^ k * X = (p : ℚ_[p]) ^ N * (M : ℚ_[p])) :
    ‖X‖ ≤ (p : ℝ) ^ (-(N : ℤ)) := by
  have hp := prime_not_dvd_of_isCoprime p α hα
  have hn : ‖(α : ℚ_[p])‖ = 1 :=
    le_antisymm (Padic.norm_int_le_one α)
      (not_lt.mp fun hlt => hp (Padic.norm_intCast_lt_one_iff.mp hlt))
  have h2 := congrArg norm h
  rw [norm_mul, norm_mul, norm_pow, hn, one_pow, one_mul, Padic.norm_p_pow] at h2
  rw [h2]
  have := Padic.norm_int_le_one (p := p) M
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  exact mul_le_of_le_one_right (zpow_pos hp0 _).le this

private lemma mul_pow_bernoulli_eval_div_expand (m : ℕ) (d : ℚ) (e : ℕ → ℤ)
    (he : ∀ j < m + 2, (e j : ℚ) = d * (Polynomial.bernoulli (m + 1)).coeff j)
    (P t : ℚ) (hP : P ≠ 0) :
    d * (P ^ m * (Polynomial.bernoulli (m + 1)).eval (t / P)) =
      P * ∑ j ∈ Finset.range m, (e j : ℚ) * t ^ j * P ^ (m - 1 - j) + (e m : ℚ) * t ^ m +
        d * t ^ (m + 1) / P := by
  have hdeg : (Polynomial.bernoulli (m + 1)).natDegree < m + 2 := by
    have : (Polynomial.bernoulli (m + 1)).natDegree ≤ m + 1 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro i hi
      rw [Polynomial.coeff_bernoulli, ite_eq_right (by omega)]
    omega
  have hc1 : (Polynomial.bernoulli (m + 1)).coeff (m + 1) = 1 := by
    simp [Polynomial.coeff_bernoulli]
  rw [Polynomial.eval_eq_sum_range' hdeg, Finset.sum_range_succ, Finset.sum_range_succ, hc1]
  have hsum : d * (P ^ m * ∑ j ∈ Finset.range m,
      (Polynomial.bernoulli (m + 1)).coeff j * (t / P) ^ j) =
      P * ∑ j ∈ Finset.range m, (e j : ℚ) * t ^ j * P ^ (m - 1 - j) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    have hm : P ^ m = P ^ j * P * P ^ (m - 1 - j) := by
      rw [← pow_succ, ← pow_add]; congr 1; omega
    rw [he j (by omega), hm, div_pow]
    field_simp
  have h2 : d * (P ^ m * ((Polynomial.bernoulli (m + 1)).coeff m * (t / P) ^ m)) =
      d * (Polynomial.bernoulli (m + 1)).coeff m * t ^ m := by
    rw [div_pow]; field_simp
  have h3 : d * (P ^ m * (1 * (t / P) ^ (m + 1))) = d * t ^ (m + 1) / P := by
    rw [div_pow, pow_succ P m]; field_simp
  rw [he m (by omega)]
  linear_combination hsum + h2 + h3

private lemma regBernoulliDist_congruence_algebra (m : ℕ)
    (α a y q P d E Sa Sy u v : ℚ) (hP : P ≠ 0) (hα : α ≠ 0)
    (hy : α * a = y + P * q) (hu : (y + P * q) ^ m - y ^ m = P * q * u)
    (hv : (y + P * q) ^ (m + 1) - y ^ m * (P * q) * ((m : ℚ) + 1) - y ^ (m + 1) =
      (P * q) ^ 2 * v)
    (hE : d * ((m : ℚ) + 1) = -2 * E) :
    α ^ (m + 1) * ((P * Sa + E * a ^ m + d * a ^ (m + 1) / P) -
        (α ^ (m + 1))⁻¹ * (P * Sy + E * y ^ m + d * y ^ (m + 1) / P) -
        d * ((m : ℚ) + 1) * a ^ m * ((a / P - 2⁻¹) - α⁻¹ * (y / P - 2⁻¹))) =
      P * (α ^ (m + 1) * Sa - Sy + E * q * u + d * q ^ 2 * v -
        d * ((m : ℚ) + 1) * q ^ 2 * u) := by
  have step : α ^ (m + 1) * ((P * Sa + E * a ^ m + d * a ^ (m + 1) / P) -
        (α ^ (m + 1))⁻¹ * (P * Sy + E * y ^ m + d * y ^ (m + 1) / P) -
        d * ((m : ℚ) + 1) * a ^ m * ((a / P - 2⁻¹) - α⁻¹ * (y / P - 2⁻¹))) =
      P * (α ^ (m + 1) * Sa - Sy) + E * (α * (α * a) ^ m - y ^ m) +
        d * ((α * a) ^ (m + 1) - y ^ (m + 1)) / P -
        d * ((m : ℚ) + 1) * ((α * a) ^ (m + 1) / P - α * (α * a) ^ m / 2 -
          (α * a) ^ m * y / P + (α * a) ^ m / 2) := by
    field_simp
    ring
  rw [step, hy]
  field_simp
  linear_combination (P * α * (y + P * q) ^ m - P * (y + P * q) ^ m) * hE +
    (2 * P * E - 2 * d * P * q * ((m : ℚ) + 1)) * hu + 2 * d * hv

/-- **Kummer-type congruence for the regularised Bernoulli distributions.** Let `d` be a natural
number clearing the denominators of the coefficients of the Bernoulli polynomial `B_k`, `k ≥ 1`
(for instance their least common multiple). For `α` prime to `p`,
`d μ_{k,α}(a + p ^ N ℤ_[p]) ≡ d k a ^ (k - 1) μ_{1,α}(a + p ^ N ℤ_[p]) (mod p ^ N)`, i.e. the
difference has norm at most `p ^ (-N)`. -/
theorem norm_regBernoulliDist_sub_mul_regBernoulliDist_one_le (p : ℕ) [Fact p.Prime] {α : ℤ}
    (hα : IsCoprime α (p : ℤ)) {k : ℕ} (hk : 1 ≤ k) {d : ℕ}
    (hd : ∀ j ≤ k, ((Polynomial.bernoulli k).coeff j).den ∣ d) (N a : ℕ) :
    ‖(d : ℚ_[p]) * regBernoulliDist p k α N a -
        (d : ℚ_[p]) * (k : ℚ_[p]) * (a : ℚ_[p]) ^ (k - 1) * regBernoulliDist p 1 α N a‖ ≤
      (p : ℝ) ^ (-(N : ℤ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hPz : ((p : ℤ) ^ N) ≠ 0 := by
    have := (Fact.out : p.Prime).pos
    positivity
  have hy : α * a = (α * a) % (p : ℤ) ^ N + (p : ℤ) ^ N * ((α * a) / (p : ℤ) ^ N) :=
    by rw [mul_comm ((p : ℤ) ^ N)]; exact (Int.emod_add_ediv_mul _ _).symm
  have hy0 : 0 ≤ (α * a) % (p : ℤ) ^ N := Int.emod_nonneg _ hPz
  set y : ℤ := (α * a) % (p : ℤ) ^ N with hy_def
  set q : ℤ := (α * a) / (p : ℤ) ^ N with hq_def
  set c : ℕ → ℚ := fun j => (Polynomial.bernoulli (m + 1)).coeff j with hc
  set e : ℕ → ℤ := fun j => (c j).num * ((d / (c j).den : ℕ) : ℤ) with he_def
  have hden : ∀ j < m + 2, (c j).den ∣ d := fun j hj => hd j (by omega)
  have he : ∀ j < m + 2, (e j : ℚ) = (d : ℚ) * c j := by
    intro j hj
    simp only [he_def, Int.cast_mul, Int.cast_natCast]
    rw [Nat.cast_div (hden j hj) (by positivity), ← Rat.mul_den_eq_num]
    field_simp
  have hE : (d : ℚ) * ((m : ℚ) + 1) = -2 * (e m : ℚ) := by
    rw [he m (by omega)]
    simp [hc, Polynomial.coeff_bernoulli]
    ring
  set P : ℤ := (p : ℤ) ^ N with hP_def
  obtain ⟨u, hu⟩ := sub_dvd_pow_sub_pow (y + P * q) y m
  rw [add_sub_cancel_left] at hu
  obtain ⟨v, hv⟩ := sq_dvd_add_pow_sub_sub (P * q) y (m + 1)
  push_cast [Nat.add_sub_cancel] at hv
  set Sa : ℤ := ∑ j ∈ Finset.range m, e j * (a : ℤ) ^ j * P ^ (m - 1 - j) with hSa
  set Sy : ℤ := ∑ j ∈ Finset.range m, e j * y ^ j * P ^ (m - 1 - j) with hSy
  refine norm_le_of_pow_mul_eq_prime_pow_mul p α hα (m + 1) N _
    (α ^ (m + 1) * Sa - Sy + e m * q * u + d * q ^ 2 * v - d * ((m : ℤ) + 1) * q ^ 2 * u) ?_
  have hyN : (((α * a % (p : ℤ) ^ N).toNat : ℕ) : ℚ) = (y : ℚ) := by
    rw [← hy_def]; exact_mod_cast Int.toNat_of_nonneg hy0
  have hPq : ((p : ℚ) ^ N) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hαq : (α : ℚ) ≠ 0 := by
    have : α ≠ 0 := by
      rintro rfl
      exact prime_not_dvd_of_isCoprime p 0 hα (dvd_zero _)
    exact_mod_cast this
  have hz : ∀ k : ℕ, (p : ℚ) ^ ((N : ℤ) * (((k + 1 : ℕ) : ℤ) - 1)) = ((p : ℚ) ^ N) ^ k := by
    intro k
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul]
    congr 1
    push_cast
    ring
  have hyq : (α : ℚ) * (a : ℚ) = (y : ℚ) + (p : ℚ) ^ N * (q : ℚ) := by
    rw [hP_def] at hy; exact_mod_cast hy
  have huq : ((y : ℚ) + (p : ℚ) ^ N * q) ^ m - (y : ℚ) ^ m = (p : ℚ) ^ N * q * u := by
    rw [hP_def] at hu; exact_mod_cast hu
  have hvq : ((y : ℚ) + (p : ℚ) ^ N * q) ^ (m + 1) - (y : ℚ) ^ m * ((p : ℚ) ^ N * q) *
      ((m : ℚ) + 1) - (y : ℚ) ^ (m + 1) = ((p : ℚ) ^ N * q) ^ 2 * v := by
    rw [hP_def] at hv
    have hv' : ((y + (p : ℤ) ^ N * q) ^ (m + 1) - y ^ m * ((p : ℤ) ^ N * q) * ((m : ℤ) + 1) -
        y ^ (m + 1) : ℤ) = ((p : ℤ) ^ N * q) ^ 2 * v := by
      linear_combination hv
    exact_mod_cast hv'
  have hA := mul_pow_bernoulli_eval_div_expand m d e he ((p : ℚ) ^ N) a hPq
  have hB := mul_pow_bernoulli_eval_div_expand m d e he ((p : ℚ) ^ N) y hPq
  have hAlg := regBernoulliDist_congruence_algebra m α a y q ((p : ℚ) ^ N) d (e m)
    (∑ j ∈ Finset.range m, (e j : ℚ) * (a : ℚ) ^ j * ((p : ℚ) ^ N) ^ (m - 1 - j))
    (∑ j ∈ Finset.range m, (e j : ℚ) * (y : ℚ) ^ j * ((p : ℚ) ^ N) ^ (m - 1 - j))
    u v hPq hαq hyq huq hvq hE
  have hQ : (α : ℚ) ^ (m + 1) * ((d : ℚ) * (((p : ℚ) ^ N) ^ m *
      (Polynomial.bernoulli (m + 1)).eval ((a : ℚ) / (p : ℚ) ^ N) -
      ((α : ℚ) ^ (m + 1))⁻¹ * (((p : ℚ) ^ N) ^ m *
      (Polynomial.bernoulli (m + 1)).eval ((y : ℚ) / (p : ℚ) ^ N))) -
      (d : ℚ) * ((m : ℚ) + 1) * (a : ℚ) ^ m * (((a : ℚ) / (p : ℚ) ^ N - 2⁻¹) -
        (α : ℚ)⁻¹ * ((y : ℚ) / (p : ℚ) ^ N - 2⁻¹))) =
      (p : ℚ) ^ N * (((α ^ (m + 1) * Sa - Sy + e m * q * u + d * q ^ 2 * v -
        d * ((m : ℤ) + 1) * q ^ 2 * u : ℤ)) : ℚ) := by
    rw [mul_sub (d : ℚ), ← mul_assoc (d : ℚ) ((α : ℚ) ^ (m + 1))⁻¹,
      mul_comm (d : ℚ) ((α : ℚ) ^ (m + 1))⁻¹, mul_assoc, hA, hB]
    rw [hAlg, hSa, hSy, hP_def]
    push_cast
    ring
  simp only [regBernoulliDist, bernoulliDist]
  rw [hyN, hz m, Nat.add_sub_cancel, show (1 : ℕ) = 0 + 1 from rfl, hz 0]
  simp only [pow_zero, one_mul, zero_add, Polynomial.bernoulli_one, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, zpow_neg, zpow_natCast, pow_one]
  have hQp := congrArg (fun r : ℚ => (r : ℚ_[p])) hQ
  push_cast at hQp ⊢
  linear_combination hQp

/-- The level-`1` values of `μ_k` on the balls `a + p ℤ_[p]`, `1 ≤ a ≤ p - 1`, sum to
`(1 - p ^ (k - 1)) B_k`. -/
private lemma sum_bernoulliDist_units_eq (p : ℕ) [Fact p.Prime] (k : ℕ) :
    ∑ a ∈ Finset.Icc 1 (p - 1), bernoulliDist p k 1 a =
      (1 - (p : ℚ_[p]) ^ ((k : ℤ) - 1)) * (bernoulli k : ℚ_[p]) := by
  have hp := (Fact.out : p.Prime)
  have hp1 := hp.pos
  have hrel := bernoulliDist_isPadicDistribution p k 0 0 (by simp)
  simp only [pow_zero, mul_one, zero_add] at hrel
  have hr : Finset.range p = insert 0 (Finset.Icc 1 (p - 1)) := by
    ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [hr, Finset.sum_insert (by simp)] at hrel
  have h00 : bernoulliDist p k 0 0 = (bernoulli k : ℚ_[p]) := by
    simp [bernoulliDist, Polynomial.bernoulli_eval_zero]
  have h10 : bernoulliDist p k 1 0 = (p : ℚ_[p]) ^ ((k : ℤ) - 1) * (bernoulli k : ℚ_[p]) := by
    simp [bernoulliDist, Polynomial.bernoulli_eval_zero]
  rw [h00, h10] at hrel
  linear_combination -hrel

/-- For an integer `α` prime to `p`, `μ_{k,α}(ℤ_[p]ˣ) = (1 - α ^ (-k)) (1 - p ^ (k - 1)) B_k`.
Here `ℤ_[p]ˣ` is the disjoint union of the balls `a + p ℤ_[p]`, `1 ≤ a ≤ p - 1`, and `B_k` is the
`k`-th Bernoulli number (with `B_1 = -1/2`). -/
theorem sum_regBernoulliDist_units_eq (p : ℕ) [Fact p.Prime] {α : ℤ}
    (hα : IsCoprime α (p : ℤ)) (k : ℕ) :
    ∑ a ∈ Finset.Icc 1 (p - 1), regBernoulliDist p k α 1 a =
      (1 - (α : ℚ_[p]) ^ (-(k : ℤ))) * (1 - (p : ℚ_[p]) ^ ((k : ℤ) - 1)) *
        (bernoulli k : ℚ_[p]) := by
  have hperm : ∑ a ∈ Finset.Icc 1 (p - 1), bernoulliDist p k 1 ((α * a) % (p : ℤ) ^ 1).toNat =
      ∑ a ∈ Finset.Icc 1 (p - 1), bernoulliDist p k 1 a := by
    simpa only [pow_one, Int.toNat_natCast] using
      Finset.sum_Icc_mul_emod hα fun x : ℤ => bernoulliDist p k 1 x.toNat
  simp only [regBernoulliDist, Finset.sum_sub_distrib, ← Finset.mul_sum, hperm,
    sum_bernoulliDist_units_eq p k]
  ring

end MetaMathlibExt
