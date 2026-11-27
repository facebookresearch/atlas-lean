/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import MathlibExt.NumberTheory.PrimeCounting.ResidueClassPsi
import MathlibExt.NumberTheory.PrimeCounting.WeakPNTArithmeticProgression

/-!
# Mean values for multiplicative weights selecting one odd prime class modulo four

For completely multiplicative weights between zero and one that select a single odd prime
class modulo four, `exists_tendsto_sum_of_prime_mod_four` relates the leading constants
in the ordinary and reciprocal sums. Both the Landau–Ramanujan and the Jones–Zvonkin
counting arguments use this estimate. The elementary proof adapts the argument in
`MathlibExt.NumberTheory.PrimeCounting.LandauRamanujan` at revision `81015ce9`.
-/

namespace MetaMathlibExt

open Asymptotics Filter Finset Nat Chebyshev ArithmeticFunction
open scoped Topology

namespace exists_tendsto_sum_of_prime_mod_four

private structure Weight where
  f : ℕ →*₀ ℝ
  nonneg : ∀ n, 0 ≤ f n
  le_one : ∀ n, f n ≤ 1
  residue : ZMod 4
  unit : IsUnit residue
  prime : ∀ p : ℕ, p.Prime → p ≠ 2 → f p = if (p : ZMod 4) = residue then 1 else 0

namespace Weight

variable (w : Weight)

private lemma weight_log_eq {n : ℕ} (hn : 1 ≤ n) :
    w.f n * Real.log n
      = ∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d * w.f d * w.f (n / d) := by
  have hn0 : n ≠ 0 := by omega
  have hterm : ∀ d ∈ n.divisors,
      ArithmeticFunction.vonMangoldt d * w.f d * w.f (n / d)
        = ArithmeticFunction.vonMangoldt d * w.f n := by
    intro d hd
    have hdiv : d ∣ n := (Nat.mem_divisors.mp hd).1
    have hdeq : d * (n / d) = n := Nat.mul_div_cancel' hdiv
    have hmul : w.f d * w.f (n / d) = w.f n := by
      rw [← map_mul w.f, hdeq]
    calc ArithmeticFunction.vonMangoldt d * w.f d * w.f (n / d)
        = ArithmeticFunction.vonMangoldt d * (w.f d * w.f (n / d)) := by ring
      _ = ArithmeticFunction.vonMangoldt d * w.f n := by rw [hmul]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul,
    ArithmeticFunction.vonMangoldt_sum, mul_comm]

private lemma weight_log_div_eq {n : ℕ} (hn : 1 ≤ n) :
    w.f n * Real.log n / (n : ℝ)
      = ∑ d ∈ n.divisors, (ArithmeticFunction.vonMangoldt d * w.f d / (d : ℝ)) *
        (w.f (n / d) / ((n / d : ℕ) : ℝ)) := by
  have hn0 : n ≠ 0 := by omega
  rw [w.weight_log_eq hn, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have hdiv : d ∣ n := (Nat.mem_divisors.mp hd).1
  have hdeq : d * (n / d) = n := Nat.mul_div_cancel' hdiv
  have hcast : (d : ℝ) * (((n / d : ℕ)) : ℝ) = (n : ℝ) := by
    have h := congrArg (Nat.cast (R := ℝ)) hdeq
    rwa [Nat.cast_mul] at h
  have e : (ArithmeticFunction.vonMangoldt d * w.f d / (d : ℝ)) *
      (w.f (n / d) / (((n / d : ℕ)) : ℝ))
      = (ArithmeticFunction.vonMangoldt d * w.f d * w.f (n / d)) /
        ((d : ℝ) * (((n / d : ℕ)) : ℝ)) := by
    ring
  rw [e, hcast]

private lemma sum_swap (F G : ℕ → ℝ) (hF : F 0 = 0) (hG : G 0 = 0)
    (x : ℝ) :
    ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ∑ d ∈ n.divisors, F d * G (n / d)
    = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, G m * ∑ d ∈ Finset.Ioc 0 ⌊x / (m : ℝ)⌋₊, F d := by
  classical
  let F' : ArithmeticFunction ℝ := ⟨F, hF⟩
  let G' : ArithmeticFunction ℝ := ⟨G, hG⟩
  have hFG : ∀ n : ℕ, (F' * G') n = ∑ d ∈ n.divisors, F d * G (n / d) := by
    intro n
    calc (F' * G') n = ∑ x ∈ n.divisorsAntidiagonal, F x.1 * G x.2 := by
          rw [ArithmeticFunction.mul_apply]
          apply Finset.sum_congr rfl
          intro x _
          rfl
      _ = ∑ d ∈ n.divisors, F d * G (n / d) :=
          Nat.sum_divisorsAntidiagonal (fun a b => F a * G b)
  have hGF : ∀ n : ℕ, (G' * F') n = ∑ d ∈ n.divisors, F d * G (n / d) := by
    intro n
    have hcomm : G' * F' = F' * G' := mul_comm _ _
    rw [hcomm]
    exact hFG n
  calc ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ∑ d ∈ n.divisors, F d * G (n / d)
      = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (G' * F') n := by
        apply Finset.sum_congr rfl
        intro n _
        exact (hGF n).symm
    _ = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, G' n * ∑ m ∈ Finset.Ioc 0 (⌊x⌋₊ / n), F' m :=
        ArithmeticFunction.sum_Ioc_mul_eq_sum_sum G' F' ⌊x⌋₊
    _ = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, G m * ∑ d ∈ Finset.Ioc 0 ⌊x / (m : ℝ)⌋₊, F d := by
        apply Finset.sum_congr rfl
        intro m _
        rw [← Nat.floor_div_natCast]
        rfl

/-- `N(x)`: sum of the weights up to `x`. -/
private noncomputable def mass (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, w.f n

/-- `A(x)`: reciprocal sum of `w.f` over `n ≤ x`. -/
private noncomputable def recip (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, w.f n / (n : ℝ)

/-- `ψ_g(y)`: von Mangoldt sum restricted by `w.f`. -/
private noncomputable def psi (y : ℝ) : ℝ :=
  ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊, ArithmeticFunction.vonMangoldt d * w.f d

/-- `M(y)`: reciprocal Mertens sum restricted by `w.f`. -/
private noncomputable def mertensSum (y : ℝ) : ℝ :=
  ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊, ArithmeticFunction.vonMangoldt d * w.f d / (d : ℝ)

/-- `J(x)`: log-weighted reciprocal sum. -/
private noncomputable def logRecip (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (w.f n / (n : ℝ)) * Real.log (x / (n : ℝ))

private lemma logMass_eq (x : ℝ) :
    ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, w.f n * Real.log (n : ℝ)
    = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, w.f m * w.psi (x / (m : ℝ)) := by
  have hF : (fun d : ℕ => ArithmeticFunction.vonMangoldt d * w.f d) 0 = 0 := by
    simp
  have hterm : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊, w.f n * Real.log (n : ℝ)
      = ∑ d ∈ n.divisors, (ArithmeticFunction.vonMangoldt d * w.f d) * w.f (n / d) := by
    intro n _
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      exact w.weight_log_eq hn1
  calc ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, w.f n * Real.log (n : ℝ)
      = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        ∑ d ∈ n.divisors, (ArithmeticFunction.vonMangoldt d * w.f d) * w.f (n / d) :=
        Finset.sum_congr rfl hterm
    _ = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, w.f m *
        ∑ d ∈ Finset.Ioc 0 ⌊x / (m : ℝ)⌋₊, ArithmeticFunction.vonMangoldt d * w.f d :=
        sum_swap _ _ hF (map_zero w.f) x
    _ = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, w.f m * w.psi (x / (m : ℝ)) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [Weight.psi]

private lemma log_recip_eq (x : ℝ) :
    ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, w.f n * Real.log (n : ℝ) / (n : ℝ)
    = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (w.f m / (m : ℝ)) * w.mertensSum (x / (m : ℝ)) := by
  have hF : (fun d : ℕ => ArithmeticFunction.vonMangoldt d * w.f d / (d : ℝ)) 0 = 0 := by
    simp
  have hG : (fun m : ℕ => w.f m / (m : ℝ)) 0 = 0 := by
    simp
  have hterm : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊, w.f n * Real.log (n : ℝ) / (n : ℝ)
      = ∑ d ∈ n.divisors, (ArithmeticFunction.vonMangoldt d * w.f d / (d : ℝ)) *
        (w.f (n / d) / (((n / d : ℕ)) : ℝ)) := by
    intro n _
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      exact w.weight_log_div_eq hn1
  calc ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, w.f n * Real.log (n : ℝ) / (n : ℝ)
      = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ∑ d ∈ n.divisors,
        (ArithmeticFunction.vonMangoldt d * w.f d / (d : ℝ)) *
        (w.f (n / d) / (((n / d : ℕ)) : ℝ)) :=
        Finset.sum_congr rfl hterm
    _ = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (w.f m / (m : ℝ)) *
        ∑ d ∈ Finset.Ioc 0 ⌊x / (m : ℝ)⌋₊,
          ArithmeticFunction.vonMangoldt d * w.f d / (d : ℝ) :=
        sum_swap (fun d : ℕ => ArithmeticFunction.vonMangoldt d * w.f d / (d : ℝ))
          (fun m : ℕ => w.f m / (m : ℝ)) hF hG x
    _ = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (w.f m / (m : ℝ)) * w.mertensSum (x / (m : ℝ)) := by
        apply Finset.sum_congr rfl
        intro m _
        rw [Weight.mertensSum]

private lemma recip_nonneg (x : ℝ) : 0 ≤ w.recip x := by
  apply Finset.sum_nonneg
  intro n _
  exact div_nonneg (w.nonneg n) (Nat.cast_nonneg n)

private lemma psi_nonneg (y : ℝ) : 0 ≤ w.psi y := by
  apply Finset.sum_nonneg
  intro d _
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (w.nonneg d)

private lemma recip_mono : Monotone w.recip := by
  intro x y hxy
  simp only [Weight.recip]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Ioc_subset_Ioc le_rfl (Nat.floor_mono hxy)
  · intro n _ _
    exact div_nonneg (w.nonneg n) (Nat.cast_nonneg n)

private lemma recip_ge_one {x : ℝ} (hx : 1 ≤ x) : 1 ≤ w.recip x := by
  have h1 : 1 ∈ Finset.Ioc 0 ⌊x⌋₊ := by
    rw [Finset.mem_Ioc]
    exact ⟨by omega, (Nat.one_le_floor_iff x).mpr hx⟩
  have h := Finset.single_le_sum
    (fun n _ => div_nonneg (w.nonneg n) (Nat.cast_nonneg n)) h1
  simpa [Weight.recip] using h

private lemma psi_le_psi (y : ℝ) : w.psi y ≤ Chebyshev.psi y := by
  simp only [Weight.psi, Chebyshev.psi]
  apply Finset.sum_le_sum
  intro d _
  calc ArithmeticFunction.vonMangoldt d * w.f d
      ≤ ArithmeticFunction.vonMangoldt d * 1 :=
        mul_le_mul_of_nonneg_left (w.le_one d)
          ArithmeticFunction.vonMangoldt_nonneg
    _ = ArithmeticFunction.vonMangoldt d := mul_one _

private lemma psi_le_mul_self {y : ℝ} (hy : 0 ≤ y) :
    w.psi y ≤ (Real.log 4 + 4) * y :=
  le_trans (w.psi_le_psi y) (Chebyshev.psi_le_const_mul_self hy)

private lemma resid_diff_le (d : ℕ) :
    |vonMangoldt d * w.f d - vonMangoldt.residueClass w.residue d| ≤
      (if d = 2 then Real.log 2 else 0) + (if d.Prime then 0 else vonMangoldt d) := by
  have ha := mul_nonneg (vonMangoldt_nonneg (n := d)) (w.nonneg d)
  have hb := mul_le_of_le_one_right (vonMangoldt_nonneg (n := d)) (w.le_one d)
  have hc := vonMangoldt.residueClass_nonneg w.residue d
  have hd := vonMangoldt.residueClass_le w.residue d
  have hbound : |vonMangoldt d * w.f d - vonMangoldt.residueClass w.residue d| ≤
      vonMangoldt d := abs_le.mpr ⟨by linarith, by linarith⟩
  by_cases h2 : d = 2
  · subst d
    simpa [Nat.prime_two, vonMangoldt_apply_prime Nat.prime_two] using hbound
  by_cases hp : d.Prime
  · rw [w.prime d hp h2]
    unfold vonMangoldt.residueClass
    by_cases h : (d : ZMod 4) = w.residue <;> simp [Set.indicator, h, hp, h2]
  · simpa [hp, h2] using hbound

/-- For `t ≥ 1`, `log t` is at most four times `t ^ (1/4 : ℝ)`. -/
private lemma log_le_four_rpow (t : ℝ) (ht : 1 ≤ t) :
    Real.log t ≤ 4 * t ^ (1/4 : ℝ) := by
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have h1 : Real.log (t ^ (1/4 : ℝ)) ≤ t ^ (1/4 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos htpos (1/4 : ℝ))
    linarith
  have h2 : Real.log t = 4 * Real.log (t ^ (1/4 : ℝ)) := by
    have hlog := Real.log_rpow htpos (1/4 : ℝ)
    linarith
  linarith

/-- For `t ≥ 1`, `2 * √t * log t` is at most `8 * t ^ (3/4 : ℝ)`. -/
private lemma two_sqrt_mul_log_le (t : ℝ) (ht : 1 ≤ t) :
    2 * Real.sqrt t * Real.log t ≤ 8 * t ^ (3/4 : ℝ) := by
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have hlog := log_le_four_rpow t ht
  have h2nn : (0 : ℝ) ≤ 2 * t ^ (1/2 : ℝ) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg htpos.le _)
  have hmul := mul_le_mul_of_nonneg_left hlog h2nn
  have e_add : t ^ (1/2 : ℝ) * t ^ (1/4 : ℝ) = t ^ (3/4 : ℝ) := by
    rw [← Real.rpow_add htpos]
    congr 1
    norm_num
  rw [Real.sqrt_eq_rpow]
  calc 2 * t ^ (1/2 : ℝ) * Real.log t
      ≤ 2 * t ^ (1/2 : ℝ) * (4 * t ^ (1/4 : ℝ)) := hmul
    _ = 8 * t ^ (3/4 : ℝ) := by rw [← e_add]; ring

/-- Pointwise bound for the non-prime Abel integrand. -/
private lemma psi_sub_theta_div_le (t : ℝ) (ht : 1 ≤ t) :
    (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2 ≤ 8 * t ^ (-5/4 : ℝ) := by
  have hnn : 0 ≤ Chebyshev.psi t - Chebyshev.theta t := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
    exact Finset.sum_nonneg fun n _ => ArithmeticFunction.vonMangoldt_nonneg
  have hle := Chebyshev.psi_sub_theta_le ht
  have hnum := two_sqrt_mul_log_le t ht
  calc (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2
      ≤ (8 * t ^ (3/4 : ℝ)) / t ^ 2 :=
        div_le_div_of_nonneg_right (le_trans hle hnum) (sq_nonneg t)
    _ = 8 * t ^ (-5/4 : ℝ) := by
      rw [← Real.rpow_natCast t 2, mul_div_assoc,
        ← Real.rpow_sub (lt_of_lt_of_le zero_lt_one ht)]
      congr 1
      norm_num

/-- Monotonicity of `ψ - θ` (a sum of nonnegative terms over a growing set). -/
private lemma psi_sub_theta_mono :
    Monotone (fun t => Chebyshev.psi t - Chebyshev.theta t) := by
  intro a b hab
  dsimp only
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime,
    Chebyshev.psi_sub_theta_eq_sum_not_prime]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨Finset.Ioc_subset_Ioc le_rfl (Nat.floor_mono hab) hn.1, hn.2⟩
  · intro n _ _
    exact ArithmeticFunction.vonMangoldt_nonneg

/-- The reciprocal sum of `Λ` over non-primes is uniformly bounded. -/
private lemma sum_not_prime_le :
    ∃ C : ℝ, ∀ y : ℝ, 1 ≤ y →
      ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
        (if n.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt n / (n : ℝ))
        ≤ C := by
  refine ⟨40, fun y hy => ?_⟩
  set c : ℕ → ℝ := fun n =>
    if n.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt n with hc
  have hcn : ∀ n : ℕ, c n =
      (if n.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt n) :=
    fun n => rfl
  have hc0 : c 0 = 0 := by
    rw [hcn, ite_eq_right Nat.not_prime_zero,
      ArithmeticFunction.vonMangoldt_apply, ite_eq_right not_isPrimePow_zero]
  have hpart : ∀ t : ℝ, ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k
      = Chebyshev.psi t - Chebyshev.theta t := by
    intro t
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons, hc0, zero_add,
      Chebyshev.psi_sub_theta_eq_sum_not_prime, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hcn]
    by_cases h : n.Prime
    · rw [ite_eq_left h, ite_eq_right (show ¬¬n.Prime from fun hn => hn h)]
    · rw [ite_eq_right h, ite_eq_left h]
  have hdiff : ∀ t ∈ Set.Icc (1 : ℝ) y,
      DifferentiableAt ℝ (fun t : ℝ => t⁻¹) t := by
    intro t ht
    rw [Set.mem_Icc] at ht
    exact (hasDerivAt_inv
      (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))).differentiableAt
  have hint : MeasureTheory.IntegrableOn (deriv fun t : ℝ => t⁻¹)
      (Set.Icc 1 y) MeasureTheory.volume := by
    rw [deriv_inv']
    apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀ (continuous_pow 2).continuousOn
    intro t ht
    rw [Set.mem_Icc] at ht
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))
  have hA := sum_mul_eq_sub_integral_mul₀ (f := fun t : ℝ => t⁻¹) c hc0 y hdiff hint
  beta_reduce at hA
  simp only [hpart] at hA
  have hLHS : (∑ k ∈ Finset.Icc 0 ⌊y⌋₊, (k : ℝ)⁻¹ * c k)
      = ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
        (if n.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt n / (n : ℝ)) := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons]
    simp only [Nat.cast_zero, inv_zero, zero_mul, zero_add]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hcn, div_eq_mul_inv]
    by_cases h : n.Prime
    · rw [ite_eq_left h, ite_eq_left h, mul_zero]
    · rw [ite_eq_right h, ite_eq_right h, mul_comm]
  have hderiv : ∀ t ∈ Set.Ioc (1 : ℝ) y,
      deriv (fun t : ℝ => t⁻¹) t * (Chebyshev.psi t - Chebyshev.theta t)
      = -((Chebyshev.psi t - Chebyshev.theta t) / t ^ 2) := by
    intro t _
    rw [deriv_inv, neg_mul, inv_mul_eq_div]
  have hint2 : (∫ t in Set.Ioc (1 : ℝ) y,
      deriv (fun t : ℝ => t⁻¹) t * (Chebyshev.psi t - Chebyshev.theta t))
      = - ∫ t in Set.Ioc (1 : ℝ) y,
        (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2 := by
    rw [← MeasureTheory.integral_neg]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    rw [Set.mem_Ioc] at ht
    exact hderiv t ht
  rw [hLHS, hint2, sub_neg_eq_add] at hA
  have hB : y⁻¹ * (Chebyshev.psi y - Chebyshev.theta y) ≤ 8 := by
    have hle := Chebyshev.psi_sub_theta_le hy
    have hnum := two_sqrt_mul_log_le y hy
    have hypos : (0 : ℝ) < y := lt_of_lt_of_le zero_lt_one hy
    have hle1 : y ^ (3/4 : ℝ) ≤ y := by
      calc y ^ (3/4 : ℝ) ≤ y ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hy (by norm_num)
        _ = y := Real.rpow_one y
    have hle2 : y ^ (3/4 : ℝ) / y ≤ 1 := (div_le_one hypos).mpr hle1
    calc y⁻¹ * (Chebyshev.psi y - Chebyshev.theta y)
        ≤ y⁻¹ * (8 * y ^ (3/4 : ℝ)) :=
          mul_le_mul_of_nonneg_left (le_trans hle hnum) (inv_nonneg.mpr hypos.le)
      _ = 8 * (y ^ (3/4 : ℝ) / y) := by ring
      _ ≤ 8 * 1 :=
          mul_le_mul_of_nonneg_left hle2 (by norm_num)
      _ = 8 := mul_one 8
  have h_int : MeasureTheory.IntegrableOn
      (fun t => (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2)
      (Set.Ioc 1 y) MeasureTheory.volume := by
    have hfin : MeasureTheory.volume (Set.Ioc (1 : ℝ) y) < ⊤ := by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top
    refine MeasureTheory.IntegrableOn.of_bound hfin ?_ 8 ?_
    · exact ((psi_sub_theta_mono.measurable.div
        (measurable_id.pow_const 2)).aestronglyMeasurable)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      rw [Set.mem_Ioc] at ht
      have ht1 : 1 ≤ t := le_of_lt ht.1
      have hnn : 0 ≤ (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2 := by
        apply div_nonneg _ (sq_nonneg t)
        rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
        exact Finset.sum_nonneg fun n _ => ArithmeticFunction.vonMangoldt_nonneg
      have hle := psi_sub_theta_div_le t ht1
      have h54 : t ^ (-5/4 : ℝ) ≤ 1 := by
        calc t ^ (-5/4 : ℝ) ≤ t ^ (0 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
          _ = 1 := Real.rpow_zero t
      calc ‖(Chebyshev.psi t - Chebyshev.theta t) / t ^ 2‖
          = (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2 := by
            rw [Real.norm_eq_abs, abs_of_nonneg hnn]
        _ ≤ 8 * t ^ (-5/4 : ℝ) := hle
        _ ≤ 8 := by
            calc 8 * t ^ (-5/4 : ℝ) ≤ 8 * 1 :=
                  mul_le_mul_of_nonneg_left h54 (by norm_num)
              _ = 8 := mul_one 8
  have h_major : MeasureTheory.IntegrableOn (fun t => 8 * t ^ (-5/4 : ℝ))
      (Set.Ioc 1 y) MeasureTheory.volume :=
    ((integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).mono_set
      Set.Ioc_subset_Ioi_self).const_mul 8
  have hIval : (∫ t in Set.Ioc (1 : ℝ) y,
      (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2)
      ≤ ∫ t in Set.Ioc (1 : ℝ) y, 8 * t ^ (-5/4 : ℝ) :=
    MeasureTheory.setIntegral_mono_on h_int h_major measurableSet_Ioc
      (fun t ht => psi_sub_theta_div_le t (le_of_lt (Set.mem_Ioc.mp ht).1))
  have hIoi_val : (∫ t in Set.Ioi (1 : ℝ), 8 * t ^ (-5/4 : ℝ)) = 32 := by
    have e : (-5/4 : ℝ) + 1 = -1/4 := by norm_num
    have hval : (∫ t in Set.Ioi (1 : ℝ), t ^ (-5/4 : ℝ)) = 4 := by
      rw [integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one, e]
      simp only [Real.one_rpow]
      norm_num
    calc (∫ t in Set.Ioi (1 : ℝ), 8 * t ^ (-5/4 : ℝ))
        = 8 * ∫ t in Set.Ioi (1 : ℝ), t ^ (-5/4 : ℝ) := by
          simp only [← smul_eq_mul]
          exact MeasureTheory.integral_const_mul _ _
      _ = 32 := by rw [hval]; norm_num
  have hImono : (∫ t in Set.Ioc (1 : ℝ) y, 8 * t ^ (-5/4 : ℝ)) ≤ 32 := by
    calc (∫ t in Set.Ioc (1 : ℝ) y, 8 * t ^ (-5/4 : ℝ))
        ≤ ∫ t in Set.Ioi (1 : ℝ), 8 * t ^ (-5/4 : ℝ) := by
          have hIoi_int : MeasureTheory.IntegrableOn
              (fun t : ℝ => 8 * t ^ (-5/4 : ℝ))
              (Set.Ioi (1 : ℝ)) MeasureTheory.volume :=
            (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul 8
          apply MeasureTheory.setIntegral_mono_set hIoi_int _ _
          · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
              with t ht
            exact mul_nonneg (by norm_num)
              (Real.rpow_nonneg
                (le_trans zero_le_one (le_of_lt (Set.mem_Ioi.mp ht))) _)
          · exact MeasureTheory.ae_of_all _ fun t ht =>
              Set.Ioc_subset_Ioi_self ht
      _ = 32 := hIoi_val
  have hfinal : y⁻¹ * (Chebyshev.psi y - Chebyshev.theta y) +
      (∫ t in Set.Ioc (1 : ℝ) y, (Chebyshev.psi t - Chebyshev.theta t) / t ^ 2)
      ≤ 40 := by
    calc _ ≤ 8 + ∫ t in Set.Ioc (1 : ℝ) y, 8 * t ^ (-5/4 : ℝ) :=
          add_le_add hB hIval
      _ ≤ 8 + 32 := add_le_add (le_refl 8) hImono
      _ = 40 := by norm_num
  rw [hA]
  exact hfinal

/-- Mertens bound for the `w.f`-restricted reciprocal sum. -/
private lemma mertens :
    ∃ C : ℝ, ∀ y : ℝ, 1 ≤ y → |w.mertensSum y - 1 / 2 * Real.log y| ≤ C := by
  have hne : NeZero 4 := ⟨by norm_num⟩
  obtain ⟨C₁, hC₁⟩ := Chebyshev.exists_abs_sum_residueClass_div_sub_log_le
    (q := 4) w.residue w.unit
  obtain ⟨C₂, hC₂⟩ := sum_not_prime_le
  have hφ : Nat.totient 4 = 2 := by decide
  refine ⟨C₁ + (Real.log 2 / 2 + C₂), fun y hy => ?_⟩
  have hmain : ∀ d ∈ Finset.Ioc 0 ⌊y⌋₊,
      |(ArithmeticFunction.vonMangoldt d * w.f d -
        ArithmeticFunction.vonMangoldt.residueClass w.residue d) / (d : ℝ)|
      ≤ (if d = 2 then Real.log 2 / 2 else 0) +
        (if d.Prime then (0 : ℝ)
          else ArithmeticFunction.vonMangoldt d / (d : ℝ)) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Ioc.mp hd).1
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
    have h := w.resid_diff_le d
    have hdiv : |(ArithmeticFunction.vonMangoldt d * w.f d -
          ArithmeticFunction.vonMangoldt.residueClass w.residue d) / (d : ℝ)|
        = |ArithmeticFunction.vonMangoldt d * w.f d -
          ArithmeticFunction.vonMangoldt.residueClass w.residue d| / (d : ℝ) := by
      rw [abs_div, abs_of_nonneg hdpos.le]
    have e : ((if d = 2 then Real.log 2 else 0) +
          (if d.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt d)) / (d : ℝ)
        = (if d = 2 then Real.log 2 / 2 else 0) +
          (if d.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt d / (d : ℝ)) := by
      by_cases h : d.Prime
      · rw [ite_eq_left h, ite_eq_left h]
        by_cases h2 : d = 2
        · subst h2
          rw [ite_eq_left rfl, ite_eq_left rfl]
          ring
        · rw [ite_eq_right h2, ite_eq_right h2, zero_add, zero_div]
      · rw [ite_eq_right h, ite_eq_right h]
        by_cases h2 : d = 2
        · subst h2
          rw [ite_eq_left rfl, ite_eq_left rfl]
          ring
        · rw [ite_eq_right h2, ite_eq_right h2, zero_add, zero_add]
    rw [hdiv]
    exact le_trans (div_le_div_of_nonneg_right h hdpos.le) (le_of_eq e)
  have hsum : ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊,
      |(ArithmeticFunction.vonMangoldt d * w.f d -
        ArithmeticFunction.vonMangoldt.residueClass w.residue d) / (d : ℝ)|
      ≤ Real.log 2 / 2 + C₂ := by
    calc _ ≤ ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊,
          ((if d = 2 then Real.log 2 / 2 else 0) +
           (if d.Prime then (0 : ℝ)
             else ArithmeticFunction.vonMangoldt d / (d : ℝ))) :=
          Finset.sum_le_sum fun d hd => hmain d hd
      _ = (∑ d ∈ Finset.Ioc 0 ⌊y⌋₊, (if d = 2 then Real.log 2 / 2 else 0)) +
          (∑ d ∈ Finset.Ioc 0 ⌊y⌋₊,
            (if d.Prime then (0 : ℝ)
              else ArithmeticFunction.vonMangoldt d / (d : ℝ))) :=
          Finset.sum_add_distrib
      _ ≤ Real.log 2 / 2 + C₂ := by
          apply add_le_add _ (hC₂ y hy)
          simp only [Finset.sum_ite_eq']
          split_ifs with hmem
          · exact le_refl _
          · exact div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)
  have hrfl : w.mertensSum y =
      ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊,
        ArithmeticFunction.vonMangoldt d * w.f d / (d : ℝ) := rfl
  have hdiff_sum : (∑ d ∈ Finset.Ioc 0 ⌊y⌋₊,
        ArithmeticFunction.vonMangoldt d * w.f d / (d : ℝ)) -
      (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
        ArithmeticFunction.vonMangoldt.residueClass w.residue n / (n : ℝ))
      = ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊,
        (ArithmeticFunction.vonMangoldt d * w.f d -
          ArithmeticFunction.vonMangoldt.residueClass w.residue d) / (d : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    rw [sub_div]
  have hM : |w.mertensSum y - (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
      ArithmeticFunction.vonMangoldt.residueClass w.residue n / (n : ℝ))|
      ≤ Real.log 2 / 2 + C₂ := by
    rw [hrfl, hdiff_sum]
    exact le_trans (Finset.abs_sum_le_sum_abs _ _) hsum
  have hN5a : |(∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
      ArithmeticFunction.vonMangoldt.residueClass w.residue n / (n : ℝ)) -
      1 / 2 * Real.log y| ≤ C₁ := by
    have h := hC₁ y hy
    rw [hφ, Nat.cast_two] at h
    rwa [show Real.log y / 2 = 1 / 2 * Real.log y from by ring] at h
  calc |w.mertensSum y - 1 / 2 * Real.log y|
      = |(w.mertensSum y - (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
          ArithmeticFunction.vonMangoldt.residueClass w.residue n / (n : ℝ))) +
        ((∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
          ArithmeticFunction.vonMangoldt.residueClass w.residue n / (n : ℝ)) -
          1 / 2 * Real.log y)| := by
        congr 1
        ring
    _ ≤ |w.mertensSum y - (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
          ArithmeticFunction.vonMangoldt.residueClass w.residue n / (n : ℝ))| +
        |(∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
          ArithmeticFunction.vonMangoldt.residueClass w.residue n / (n : ℝ)) -
          1 / 2 * Real.log y| := abs_add_le _ _
    _ ≤ (Real.log 2 / 2 + C₂) + C₁ := add_le_add hM hN5a
    _ = C₁ + (Real.log 2 / 2 + C₂) := by ring

/-- The difference between `w.psi` and the residue-class psi is at most
`log 2 + (ψ - θ)`. -/
private lemma psi_diff_le (y : ℝ) :
    |w.psi y - Chebyshev.psiResidueClass w.residue y|
      ≤ Real.log 2 + (Chebyshev.psi y - Chebyshev.theta y) := by
  have e : w.psi y - Chebyshev.psiResidueClass w.residue y
      = ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt d * w.f d -
        ArithmeticFunction.vonMangoldt.residueClass w.residue d) := by
    unfold Weight.psi Chebyshev.psiResidueClass
    rw [← Finset.sum_sub_distrib]
  have hnp : ∀ z : ℝ, ∑ d ∈ Finset.Ioc 0 ⌊z⌋₊,
        (if d.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt d)
      = Chebyshev.psi z - Chebyshev.theta z := by
    intro z
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases h : d.Prime
    · rw [ite_eq_left h, ite_eq_right (show ¬¬d.Prime from fun hn => hn h)]
    · rw [ite_eq_right h, ite_eq_left h]
  have h2part : ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊, (if d = 2 then Real.log 2 else 0)
      ≤ Real.log 2 := by
    simp only [Finset.sum_ite_eq']
    split_ifs with hmem
    · exact le_refl _
    · exact Real.log_nonneg (by norm_num)
  rw [e]
  calc |∑ d ∈ Finset.Ioc 0 ⌊y⌋₊, (ArithmeticFunction.vonMangoldt d * w.f d -
        ArithmeticFunction.vonMangoldt.residueClass w.residue d)|
      ≤ ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊, |ArithmeticFunction.vonMangoldt d * w.f d -
        ArithmeticFunction.vonMangoldt.residueClass w.residue d| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Ioc 0 ⌊y⌋₊, ((if d = 2 then Real.log 2 else 0) +
        (if d.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt d)) :=
        Finset.sum_le_sum fun d _ => w.resid_diff_le d
    _ = (∑ d ∈ Finset.Ioc 0 ⌊y⌋₊, (if d = 2 then Real.log 2 else 0)) +
        (∑ d ∈ Finset.Ioc 0 ⌊y⌋₊,
          (if d.Prime then (0 : ℝ) else ArithmeticFunction.vonMangoldt d)) :=
        Finset.sum_add_distrib
    _ ≤ Real.log 2 + (Chebyshev.psi y - Chebyshev.theta y) :=
        add_le_add h2part (le_of_eq (hnp y))

/-- The normalized error between `w.psi` and the residue-class psi tends to zero. -/
private lemma psi_err_tendsto :
    Filter.Tendsto (fun y => (w.psi y -
      Chebyshev.psiResidueClass w.residue y) / y)
      Filter.atTop (nhds 0) := by
  have hbound : ∀ᶠ y in Filter.atTop,
      ‖(w.psi y - Chebyshev.psiResidueClass w.residue y) / y‖
        ≤ Real.log 2 / y + 8 * y ^ (-1/4 : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with y hy
    have hypos : (0 : ℝ) < y := lt_of_lt_of_le zero_lt_one hy
    have h1 := w.psi_diff_le y
    have h2 := Chebyshev.psi_sub_theta_le hy
    have h3 := two_sqrt_mul_log_le y hy
    have e1 : y ^ (3/4 : ℝ) / y = y ^ (-1/4 : ℝ) := by
      have h3 : (3/4 : ℝ) - 1 = -1/4 := by norm_num
      rw [← h3, Real.rpow_sub hypos, Real.rpow_one]
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hypos.le]
    calc |w.psi y - Chebyshev.psiResidueClass w.residue y| / y
        ≤ (Real.log 2 + 8 * y ^ (3/4 : ℝ)) / y := by
          apply div_le_div_of_nonneg_right _ hypos.le
          linarith [h1, h2, h3]
      _ = Real.log 2 / y + 8 * y ^ (-1/4 : ℝ) := by
          rw [add_div, mul_div_assoc, e1]
  have hg : Filter.Tendsto (fun y : ℝ => Real.log 2 / y + 8 * y ^ (-1/4 : ℝ))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun y : ℝ => Real.log 2 / y) Filter.atTop (nhds 0) := by
      simpa [div_eq_mul_inv, mul_zero] using
        (tendsto_inv_atTop_zero.const_mul (Real.log 2))
    have h2 : Filter.Tendsto (fun y : ℝ => 8 * y ^ (-1/4 : ℝ))
        Filter.atTop (nhds 0) := by
      have h := (tendsto_rpow_neg_atTop
        (show (0 : ℝ) < 1 / 4 by norm_num)).const_mul 8
      have e : ((-1/4 : ℝ)) = -((1/4 : ℝ)) := by norm_num
      rw [e]
      simpa using h
    simpa using h1.add h2
  exact squeeze_zero_norm' hbound hg

/-- `w.psi y / y` tends to `1 / 2`. -/
private lemma psi_tendsto :
    Filter.Tendsto (fun y => w.psi y / y) Filter.atTop (nhds (1 / 2 : ℝ)) := by
  have hne : NeZero 4 := ⟨by norm_num⟩
  have hPNT := Chebyshev.tendsto_psiResidueClass_div_self w.residue w.unit
  have hφ : Nat.totient 4 = 2 := by decide
  have eφ : ((Nat.totient 4 : ℝ))⁻¹ = 1 / 2 := by
    rw [hφ]
    norm_num
  rw [eφ] at hPNT
  have heq : (fun y => w.psi y / y) =ᶠ[Filter.atTop]
      (fun y => (w.psi y - Chebyshev.psiResidueClass w.residue y) / y +
        Chebyshev.psiResidueClass w.residue y / y) := by
    filter_upwards with y
    rw [sub_div]
    ring
  have hlim := w.psi_err_tendsto.add hPNT
  rw [show (0 : ℝ) + 1 / 2 = 1 / 2 from by ring] at hlim
  exact Filter.Tendsto.congr' heq.symm hlim

/-- `J` is close to `(2/3) A log`: the Mertens error propagates. -/
private lemma logRecip_near :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |w.logRecip x - 2 / 3 * w.recip x * Real.log x| ≤ 2 / 3 * C * w.recip x := by
  obtain ⟨C, hC⟩ := w.mertens
  refine ⟨C, fun x hx => ?_⟩
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hm : ∀ m ∈ Finset.Ioc 0 ⌊x⌋₊,
      |w.mertensSum (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ))| ≤ C := by
    intro m hmem
    have hm1 : 1 ≤ m := (Finset.mem_Ioc.mp hmem).1
    have hmx : (m : ℝ) ≤ x := by
      have h1 : m ≤ ⌊x⌋₊ := (Finset.mem_Ioc.mp hmem).2
      exact le_trans (by exact_mod_cast h1) (Nat.floor_le (by linarith : (0 : ℝ) ≤ x))
    have hpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hge : 1 ≤ x / (m : ℝ) := by
      rw [le_div_iff₀ hpos]
      simpa using hmx
    exact hC _ hge
  have hR : |∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (w.f m / (m : ℝ)) *
      (w.mertensSum (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ)))| ≤ C * w.recip x := by
    calc _ ≤ ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊,
          |(w.f m / (m : ℝ)) *
            (w.mertensSum (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ)))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊,
          (w.f m / (m : ℝ)) * C := by
          apply Finset.sum_le_sum
          intro m hmem
          calc |(w.f m / (m : ℝ)) *
              (w.mertensSum (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ)))|
              = (w.f m / (m : ℝ)) *
                |w.mertensSum (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ))| := by
                rw [abs_mul, abs_of_nonneg
                  (div_nonneg (w.nonneg m) (Nat.cast_nonneg m))]
            _ ≤ (w.f m / (m : ℝ)) * C :=
                mul_le_mul_of_nonneg_left (hm m hmem)
                  (div_nonneg (w.nonneg m) (Nat.cast_nonneg m))
      _ = C * w.recip x := by
          have hrfl : w.recip x = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, w.f m / (m : ℝ) := rfl
          rw [← Finset.sum_mul, ← hrfl]
          ring
  have hsplit : (∑ m ∈ Finset.Ioc 0 ⌊x⌋₊,
      (w.f m / (m : ℝ)) * w.mertensSum (x / (m : ℝ)))
      = 1 / 2 * w.logRecip x + ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (w.f m / (m : ℝ)) *
        (w.mertensSum (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ))) := by
    have hJ2 : (∑ m ∈ Finset.Ioc 0 ⌊x⌋₊,
        (w.f m / (m : ℝ)) * (1 / 2 * Real.log (x / (m : ℝ)))) = 1 / 2 * w.logRecip x := by
      have hJ : w.logRecip x =
          ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (w.f m / (m : ℝ)) * Real.log (x / (m : ℝ)) := rfl
      rw [hJ, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring
    calc (∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (w.f m / (m : ℝ)) * w.mertensSum (x / (m : ℝ)))
        = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, ((w.f m / (m : ℝ)) *
          (1 / 2 * Real.log (x / (m : ℝ))) + (w.f m / (m : ℝ)) *
          (w.mertensSum (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ)))) :=
          Finset.sum_congr rfl fun m _ => by ring
      _ = (∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (w.f m / (m : ℝ)) *
          (1 / 2 * Real.log (x / (m : ℝ)))) +
          ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (w.f m / (m : ℝ)) *
          (w.mertensSum (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ))) :=
          Finset.sum_add_distrib
      _ = 1 / 2 * w.logRecip x + ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (w.f m / (m : ℝ)) *
          (w.mertensSum (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ))) := by
          rw [hJ2]
  have hAJ : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, w.f n * Real.log (n : ℝ) / (n : ℝ))
      = w.recip x * Real.log x - w.logRecip x := by
    have hJ : w.logRecip x = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        (w.f n / (n : ℝ)) * Real.log (x / (n : ℝ)) := rfl
    have hA : w.recip x = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, w.f n / (n : ℝ) := rfl
    rw [hJ, hA, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hmem
    by_cases hn : n = 0
    · subst hn
      simp
    · have hnpos : (0 : ℝ) < (n : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt hnpos)]
      ring
  have hRe : (w.recip x * Real.log x - w.logRecip x) - 1 / 2 * w.logRecip x
      = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (w.f m / (m : ℝ)) *
        (w.mertensSum (x / (m : ℝ)) - 1 / 2 * Real.log (x / (m : ℝ))) := by
    have h1 := w.log_recip_eq x
    rw [hAJ] at h1
    rw [h1, hsplit]
    ring
  rw [← hRe] at hR
  have hRw : w.logRecip x - 2 / 3 * w.recip x * Real.log x
      = -((2 / 3) * ((w.recip x * Real.log x - w.logRecip x) - 1 / 2 * w.logRecip x)) := by
    ring
  rw [hRw, abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3)]
  calc 2 / 3 * |(w.recip x * Real.log x - w.logRecip x) - 1 / 2 * w.logRecip x|
      ≤ 2 / 3 * (C * w.recip x) :=
        mul_le_mul_of_nonneg_left hR (by norm_num)
    _ = 2 / 3 * C * w.recip x := by ring

/-- Increment bounds for `J`: splitting the sum at `⌊x⌋₊`. -/
private lemma logRecip_increment {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    w.recip x * Real.log (y / x) ≤ w.logRecip y - w.logRecip x ∧
      w.logRecip y - w.logRecip x ≤ w.recip y * Real.log (y / x) := by
  have hy : 1 ≤ y := le_trans hx hxy
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hypos : (0 : ℝ) < y := lt_of_lt_of_le zero_lt_one hy
  have hle : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_mono hxy
  have hJx : w.logRecip x = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
      (w.f n / (n : ℝ)) * Real.log (x / (n : ℝ)) := rfl
  have hJy : w.logRecip y = ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
      (w.f n / (n : ℝ)) * Real.log (y / (n : ℝ)) := rfl
  have hAx : w.recip x = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, w.f n / (n : ℝ) := rfl
  have hAy : w.recip y = ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, w.f n / (n : ℝ) := rfl
  have hsplitJ : (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
      (w.f n / (n : ℝ)) * Real.log (y / (n : ℝ)))
      = (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (w.f n / (n : ℝ)) * Real.log (y / (n : ℝ))) +
        ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
          (w.f n / (n : ℝ)) * Real.log (y / (n : ℝ)) :=
    (Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hle).symm
  have hsplitA : (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, w.f n / (n : ℝ))
      = (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, w.f n / (n : ℝ)) +
        ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, w.f n / (n : ℝ) :=
    (Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hle).symm
  have hlogyx : Real.log (y / x) = Real.log y - Real.log x :=
    Real.log_div (ne_of_gt hypos) (ne_of_gt hxpos)
  have hmain : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊,
      (w.f n / (n : ℝ)) * Real.log (y / (n : ℝ)) -
        (w.f n / (n : ℝ)) * Real.log (x / (n : ℝ))
      = (w.f n / (n : ℝ)) * Real.log (y / x) := by
    intro n hmem
    have hn1 : 1 ≤ n := (Finset.mem_Ioc.mp hmem).1
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    rw [Real.log_div (ne_of_gt hypos) (ne_of_gt hnpos),
      Real.log_div (ne_of_gt hxpos) (ne_of_gt hnpos), hlogyx]
    ring
  have hRnn : 0 ≤ ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
      (w.f n / (n : ℝ)) * Real.log (y / (n : ℝ)) := by
    apply Finset.sum_nonneg
    intro n hmem
    have hn1 : 1 ≤ n := by
      have h1 : ⌊x⌋₊ < n := (Finset.mem_Ioc.mp hmem).1
      have h2 : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx
      omega
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hny : (n : ℝ) ≤ y := by
      have h1 : n ≤ ⌊y⌋₊ := (Finset.mem_Ioc.mp hmem).2
      exact le_trans (by exact_mod_cast h1) (Nat.floor_le (by linarith : (0 : ℝ) ≤ y))
    have hlog : 0 ≤ Real.log (y / (n : ℝ)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hnpos]
      simpa using hny
    exact mul_nonneg (div_nonneg (w.nonneg n) (Nat.cast_nonneg n)) hlog
  have hRle : (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
      (w.f n / (n : ℝ)) * Real.log (y / (n : ℝ)))
      ≤ (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, w.f n / (n : ℝ)) * Real.log (y / x) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro n hmem
    have hn1 : 1 ≤ n := by
      have h1 : ⌊x⌋₊ < n := (Finset.mem_Ioc.mp hmem).1
      have h2 : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx
      omega
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hnx : x < (n : ℝ) := by
      have h1 : ⌊x⌋₊ < n := (Finset.mem_Ioc.mp hmem).1
      have hN : ⌊x⌋₊ + 1 ≤ n := h1
      have h2 : (⌊x⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hN
      have h3 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
      linarith
    have hny : (n : ℝ) ≤ y := by
      have h1 : n ≤ ⌊y⌋₊ := (Finset.mem_Ioc.mp hmem).2
      exact le_trans (by exact_mod_cast h1) (Nat.floor_le (by linarith : (0 : ℝ) ≤ y))
    have hfrac : y / (n : ℝ) ≤ y / x :=
      (div_le_div_iff_of_pos_left hypos hnpos hxpos).mpr hnx.le
    have hlog : Real.log (y / (n : ℝ)) ≤ Real.log (y / x) :=
      Real.log_le_log (div_pos hypos hnpos) hfrac
    exact mul_le_mul_of_nonneg_left hlog
      (div_nonneg (w.nonneg n) (Nat.cast_nonneg n))
  have hdiff : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
      (w.f n / (n : ℝ)) * Real.log (y / (n : ℝ))) -
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (w.f n / (n : ℝ)) * Real.log (x / (n : ℝ)))
      = w.recip x * Real.log (y / x) := by
    rw [← Finset.sum_sub_distrib]
    have hcongr : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        ((w.f n / (n : ℝ)) * Real.log (y / (n : ℝ)) -
          (w.f n / (n : ℝ)) * Real.log (x / (n : ℝ))))
        = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (w.f n / (n : ℝ)) * Real.log (y / x) :=
      Finset.sum_congr rfl fun n hmem => hmain n hmem
    rw [hcongr, ← Finset.sum_mul, hAx]
  have hR_eq : w.recip y - w.recip x
      = ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, w.f n / (n : ℝ) := by
    rw [hAy, hAx, hsplitA, add_sub_cancel_left]
  have hJyJx : w.logRecip y - w.logRecip x = w.recip x * Real.log (y / x) +
      ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
        (w.f n / (n : ℝ)) * Real.log (y / (n : ℝ)) := by
    rw [hJy, hJx, hsplitJ]
    linear_combination hdiff
  rw [hJyJx]
  constructor
  · exact le_add_of_nonneg_right hRnn
  · have hRR : (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
        (w.f n / (n : ℝ)) * Real.log (y / (n : ℝ)))
        ≤ (w.recip y - w.recip x) * Real.log (y / x) := by
      rw [hR_eq]
      calc (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
            (w.f n / (n : ℝ)) * Real.log (y / (n : ℝ)))
          ≤ (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, w.f n / (n : ℝ)) * Real.log (y / x) :=
            hRle
        _ = (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, w.f n / (n : ℝ)) * Real.log (y / x) :=
            rfl
    calc w.recip x * Real.log (y / x) +
        (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊,
          (w.f n / (n : ℝ)) * Real.log (y / (n : ℝ)))
        ≤ w.recip x * Real.log (y / x) + (w.recip y - w.recip x) * Real.log (y / x) :=
          add_le_add (le_refl _) hRR
      _ = w.recip y * Real.log (y / x) := by ring

/-- For `|t| ≤ 1/2`, `|log (1 + t) - t| ≤ 2 t²`. -/
private lemma log_one_add_le (t : ℝ) (ht : |t| ≤ 1 / 2) :
    |Real.log (1 + t) - t| ≤ 2 * t ^ 2 := by
  have h1 : |(-t)| < 1 := by
    rw [abs_neg]
    linarith
  have h := Real.abs_log_sub_add_sum_range_le h1 1
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, div_one, pow_one,
    sub_neg_eq_add] at h
  have h2 : |-t + Real.log (1 + t)| = |Real.log (1 + t) - t| := by
    congr 1
    ring
  rw [h2] at h
  have ht2 : |-t| ^ 2 = t ^ 2 := by rw [abs_neg, sq_abs]
  have hden : (1 : ℝ) / 2 ≤ 1 - |-t| := by
    rw [abs_neg]
    have := abs_nonneg t
    linarith
  have hpos : (0 : ℝ) < 1 - |-t| := by linarith
  have hle : t ^ 2 / (1 - |-t|) ≤ t ^ 2 / (1 / 2) := by
    rw [div_eq_mul_one_div, div_eq_mul_one_div]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg t)
    simpa using one_div_le_one_div_of_le (by norm_num) hden
  have hexp : |-t| ^ (1 + 1) = t ^ 2 := ht2
  rw [hexp] at h
  calc |Real.log (1 + t) - t| ≤ t ^ 2 / (1 - |-t|) := h
    _ ≤ t ^ 2 / (1 / 2) := hle
    _ = 2 * t ^ 2 := by ring

/-- From a uniform increment bound, the log-scale sequence is Cauchy and
`u k / k ^ (3/2 : ℝ)` converges to a positive limit. -/
private lemma growth_limit (u : ℕ → ℝ) (hpos : ∀ k : ℕ, 1 ≤ k → 0 < u k)
    (K : ℝ) (hK : 0 ≤ K) (k₂ : ℕ)
    (hincr : ∀ k : ℕ, k₂ ≤ k →
      |Real.log (u (k + 1)) - Real.log (u k)
        - 3 / 2 * (Real.log (((k + 1 : ℕ)) : ℝ) - Real.log (k : ℝ))|
      ≤ (4 * K ^ 2 + K + 12) / (k : ℝ) ^ 2) :
    ∃ L : ℝ, 0 < L ∧
      Filter.Tendsto (fun k : ℕ => u k / (k : ℝ) ^ (3 / 2 : ℝ))
        Filter.atTop (nhds L) := by
  -- The log-scale sequence `v` is Cauchy via summable increments.
  set v : ℕ → ℝ := fun k => Real.log (u k) - 3 / 2 * Real.log (k : ℝ) with hvdef
  have hK' : (0 : ℝ) ≤ 4 * K ^ 2 + K + 12 := by nlinarith [sq_nonneg K, hK]
  have hF : Summable (fun n : ℕ => (4 * K ^ 2 + K + 12 : ℝ) / (n : ℝ) ^ 2) := by
    have hS : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have hM := hS.mul_left (4 * K ^ 2 + K + 12)
    refine hM.congr fun n => ?_
    rw [mul_one_div]
  have hG : Summable (fun j : ℕ => (4 * K ^ 2 + K + 12 : ℝ) / (((j + k₂ : ℕ)) : ℝ) ^ 2) :=
    (summable_nat_add_iff k₂).mpr hF
  have hdist : Summable (fun j : ℕ => dist (v (j + k₂)) (v (j + k₂ + 1))) := by
    refine hG.of_nonneg_of_le (fun j => dist_nonneg) fun j => ?_
    have hk : k₂ ≤ j + k₂ := Nat.le_add_left _ _
    have h := hincr (j + k₂) hk
    rw [dist_eq_norm, Real.norm_eq_abs]
    have e : v (j + k₂) - v (j + k₂ + 1)
        = -(Real.log (u (j + k₂ + 1)) - Real.log (u (j + k₂))
          - 3 / 2 * (Real.log (((j + k₂ + 1 : ℕ)) : ℝ)
            - Real.log (((j + k₂ : ℕ)) : ℝ))) := by
      simp only [hvdef]
      ring
    rw [e, abs_neg]
    have hcast2 : ((j + k₂ + 1 : ℕ)) = (j + k₂) + 1 := rfl
    rw [hcast2]
    exact h
  have hshift : CauchySeq (fun j : ℕ => v (j + k₂)) := by
    have hD : Summable (fun j : ℕ => dist ((fun j => v (j + k₂)) j)
        ((fun j => v (j + k₂)) j.succ)) := by
      have e : (fun j : ℕ => dist ((fun j => v (j + k₂)) j)
            ((fun j => v (j + k₂)) j.succ))
            = (fun j : ℕ => dist (v (j + k₂)) (v (j + k₂ + 1))) := by
        funext j
        simp only [Nat.succ_eq_add_one]
        rw [Nat.add_right_comm j 1 k₂]
      rw [e]
      exact hdist
    exact cauchySeq_of_summable_dist hD
  obtain ⟨ℓ, hℓ⟩ := cauchySeq_tendsto_of_complete hshift
  have hv_lim : Filter.Tendsto v Filter.atTop (nhds ℓ) := by
    have hiff := tendsto_add_atTop_iff_nat (l := nhds ℓ) (f := v) k₂
    exact hiff.mp hℓ
  -- Exponentiate back.
  have hexp_lim : Filter.Tendsto (fun k : ℕ => Real.exp (v k))
      Filter.atTop (nhds (Real.exp ℓ)) :=
    (Real.continuous_exp.tendsto ℓ).comp hv_lim
  have heq : (fun k : ℕ => Real.exp (v k)) =ᶠ[Filter.atTop]
      (fun k : ℕ => u k / (k : ℝ) ^ (3 / 2 : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have huk : 0 < u k := hpos k hk
    have hsk : (0 : ℝ) < (k : ℝ) := by exact_mod_cast lt_of_lt_of_le zero_lt_one hk
    have eexp : Real.exp (3 / 2 * Real.log (k : ℝ)) = (k : ℝ) ^ (3 / 2 : ℝ) := by
      rw [Real.rpow_def_of_pos hsk]
      congr 1
      ring
    simp only [hvdef]
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_log huk, Real.exp_neg, eexp]
    simp only [div_eq_mul_inv]
  refine ⟨Real.exp ℓ, Real.exp_pos ℓ, ?_⟩
  exact hexp_lim.congr' heq

/-- Abstract growth lemma: ratios `1 + 3/(2k)` up to `K/k²` force
`u k / k ^ (3/2 : ℝ)` to converge to a positive limit. -/
private lemma growth (u : ℕ → ℝ) (hpos : ∀ k : ℕ, 1 ≤ k → 0 < u k)
    (K : ℝ) (hK : 0 ≤ K) (k₀ : ℕ) (hk₀ : 1 ≤ k₀)
    (hstep : ∀ k : ℕ, k₀ ≤ k →
      |u (k + 1) / u k - (1 + 3 / (2 * (k : ℝ)))| ≤ K / (k : ℝ) ^ 2) :
    ∃ L : ℝ, 0 < L ∧
      Filter.Tendsto (fun k : ℕ => u k / (k : ℝ) ^ (3 / 2 : ℝ))
        Filter.atTop (nhds L) := by
  have hbase1 : Filter.Tendsto (fun k : ℕ => ((k : ℝ) ^ (-1 : ℝ)))
      Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 by norm_num)).comp
      tendsto_natCast_atTop_atTop
  have hbase2 : Filter.Tendsto (fun k : ℕ => ((k : ℝ) ^ (-2 : ℝ)))
      Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (show (0 : ℝ) < 2 by norm_num)).comp
      tendsto_natCast_atTop_atTop
  have h1 : Filter.Tendsto (fun k : ℕ => 3 / (2 * (k : ℝ)))
      Filter.atTop (nhds 0) := by
    have e : (fun k : ℕ => 3 / (2 * (k : ℝ)))
        = (fun k : ℕ => (3 / 2 : ℝ) * (k : ℝ) ^ (-1 : ℝ)) := by
      funext k
      rw [Real.rpow_neg_one]
      ring
    rw [e]
    simpa using hbase1.const_mul (3 / 2 : ℝ)
  have h2 : Filter.Tendsto (fun k : ℕ => K / (k : ℝ) ^ 2)
      Filter.atTop (nhds 0) := by
    have e : (fun k : ℕ => K / (k : ℝ) ^ 2)
        = (fun k : ℕ => K * (k : ℝ) ^ (-2 : ℝ)) := by
      funext k
      rw [Real.rpow_neg (Nat.cast_nonneg k), Real.rpow_two, div_eq_mul_inv]
    rw [e]
    simpa using hbase2.const_mul K
  have hzev : Filter.Tendsto (fun k : ℕ => 3 / (2 * (k : ℝ)) + K / (k : ℝ) ^ 2)
      Filter.atTop (nhds 0) := by
    simpa using h1.add h2
  obtain ⟨k₁, hk₁⟩ := Filter.eventually_atTop.mp
    (hzev.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)))
  set k₂ := max k₁ (max k₀ 2) with hk₂
  have hk₂₀ : k₀ ≤ k₂ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hk₂₁ : k₁ ≤ k₂ := le_max_left _ _
  have hk₂pos : 1 ≤ k₂ := le_trans hk₀ hk₂₀
  have hk₂two : 2 ≤ k₂ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hsmall : ∀ k : ℕ, k₂ ≤ k →
      3 / (2 * (k : ℝ)) + K / (k : ℝ) ^ 2 < 1 / 2 :=
    fun k hk => hk₁ k (le_trans hk₂₁ hk)
  have hkr : ∀ k : ℕ, k₂ ≤ k → (0 : ℝ) < (k : ℝ) := by
    intro k hk
    have h1k : 1 ≤ k := le_trans hk₂pos hk
    exact_mod_cast lt_of_lt_of_le zero_lt_one h1k
  have h1k : ∀ k : ℕ, k₂ ≤ k → (1 : ℝ) ≤ (k : ℝ) := by
    intro k hk
    exact_mod_cast le_trans hk₂pos hk
  have hudev : ∀ k : ℕ, k₂ ≤ k →
      |u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))| ≤ K / (k : ℝ) ^ 2 := by
    intro k hk
    have h := hstep k (le_trans hk₂₀ hk)
    have e : u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))
        = u (k + 1) / u k - (1 + 3 / (2 * (k : ℝ))) := by ring
    rw [e]
    exact h
  have htnn : ∀ k : ℕ, k₂ ≤ k → 0 ≤ 3 / (2 * (k : ℝ)) := by
    intro k hk
    exact div_nonneg (by norm_num)
      (mul_nonneg (by norm_num) (le_of_lt (hkr k hk)))
  have htbound : ∀ k : ℕ, k₂ ≤ k → |u (k + 1) / u k - 1| ≤ 1 / 2 := by
    intro k hk
    have e : u (k + 1) / u k - 1
        = (u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))) + 3 / (2 * (k : ℝ)) := by
      ring
    calc |u (k + 1) / u k - 1|
        = |(u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))) + 3 / (2 * (k : ℝ))| := by
          rw [← e]
      _ ≤ |u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))| + |3 / (2 * (k : ℝ))| :=
          abs_add_le _ _
      _ = |u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))| + 3 / (2 * (k : ℝ)) := by
          rw [abs_of_nonneg (htnn k hk)]
      _ ≤ K / (k : ℝ) ^ 2 + 3 / (2 * (k : ℝ)) := by
          exact add_le_add (hudev k hk) le_rfl
      _ = 3 / (2 * (k : ℝ)) + K / (k : ℝ) ^ 2 := by ring
      _ ≤ 1 / 2 := le_of_lt (hsmall k hk)
  have hinvbound : ∀ k : ℕ, k₂ ≤ k → |1 / (k : ℝ)| ≤ 1 / 2 := by
    intro k hk
    have hsk := hkr k hk
    have h2k : (2 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast le_trans hk₂two hk
    rw [abs_of_nonneg (le_of_lt (div_pos one_pos hsk))]
    calc 1 / (k : ℝ) ≤ 1 / 2 :=
          one_div_le_one_div_of_le (by norm_num) h2k
      _ = 1 / 2 := rfl
  have hsq2 : ∀ a b : ℝ, (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
    intro a b
    nlinarith [sq_nonneg (a - b)]
  have htsq : ∀ k : ℕ, k₂ ≤ k →
      (u (k + 1) / u k - 1) ^ 2 ≤ (2 * K ^ 2 + 9 / 2) / (k : ℝ) ^ 2 := by
    intro k hk
    have hB := hudev k hk
    have hsk := hkr k hk
    have hs1 := h1k k hk
    have hsq : (u (k + 1) / u k - 1) ^ 2
        ≤ 2 * (u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))) ^ 2
          + 2 * (3 / (2 * (k : ℝ))) ^ 2 := by
      have h := hsq2 (u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ)))
        (3 / (2 * (k : ℝ)))
      have e : (u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ)))
          + 3 / (2 * (k : ℝ)) = u (k + 1) / u k - 1 := by ring
      rwa [e] at h
    have hKnn : 0 ≤ K / (k : ℝ) ^ 2 := div_nonneg hK (sq_nonneg _)
    have hB2 : (u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))) ^ 2
        ≤ (K / (k : ℝ) ^ 2) ^ 2 := by
      have h2 : |u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))|
          ≤ |K / (k : ℝ) ^ 2| := by
        rw [abs_of_nonneg hKnn]
        exact hB
      exact sq_le_sq.mpr h2
    have h44 : (K / (k : ℝ) ^ 2) ^ 2 ≤ K ^ 2 / (k : ℝ) ^ 2 := by
      have h1sq : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by
        nlinarith [sq_nonneg ((k : ℝ) - 1), hs1]
      have hKs : K / (k : ℝ) ^ 2 ≤ K := div_le_self hK h1sq
      calc (K / (k : ℝ) ^ 2) ^ 2
          = (K / (k : ℝ) ^ 2) * (K / (k : ℝ) ^ 2) := pow_two _
        _ ≤ (K / (k : ℝ) ^ 2) * K :=
            mul_le_mul_of_nonneg_left hKs hKnn
        _ = K ^ 2 / (k : ℝ) ^ 2 := by ring
    have h32 : (3 / (2 * (k : ℝ))) ^ 2 = (9 / 4) / (k : ℝ) ^ 2 := by
      rw [div_pow, show (3 : ℝ) ^ 2 = 9 by norm_num,
        show (2 * (k : ℝ)) ^ 2 = 4 * (k : ℝ) ^ 2 by ring]
      ring
    have hfin : 2 * ((K / (k : ℝ) ^ 2) ^ 2) + 2 * ((9 / 4) / (k : ℝ) ^ 2)
        ≤ (2 * K ^ 2 + 9 / 2) / (k : ℝ) ^ 2 := by
      have h2a := mul_le_mul_of_nonneg_left h44 (show (0 : ℝ) ≤ 2 by norm_num)
      have e : 2 * (K ^ 2 / (k : ℝ) ^ 2) + 2 * ((9 / 4) / (k : ℝ) ^ 2)
          = (2 * K ^ 2 + 9 / 2) / (k : ℝ) ^ 2 := by ring
      linarith
    linarith [hsq, hB2, h32, hfin]
  have htri : ∀ a b c : ℝ, |a + b - c| ≤ |a| + |b| + |c| := by
    intro a b c
    calc |a + b - c| = |(a + b) + (-c)| := by rw [sub_eq_add_neg]
      _ ≤ |a + b| + |-c| := abs_add_le _ _
      _ = |a + b| + |c| := by rw [abs_neg]
      _ ≤ (|a| + |b|) + |c| := by
          have h := abs_add_le a b
          linarith
      _ = |a| + |b| + |c| := by ring
  have hincr : ∀ k : ℕ, k₂ ≤ k →
      |Real.log (u (k + 1)) - Real.log (u k)
        - 3 / 2 * (Real.log (((k + 1 : ℕ)) : ℝ) - Real.log (k : ℝ))|
      ≤ (4 * K ^ 2 + K + 12) / (k : ℝ) ^ 2 := by
    intro k hk
    have huk : 0 < u k := hpos k (le_trans hk₂pos hk)
    have huk1 : 0 < u (k + 1) :=
      hpos (k + 1) (by omega)
    have hsk := hkr k hk
    have hcast : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    have e1 : Real.log (u (k + 1)) - Real.log (u k)
        = Real.log (u (k + 1) / u k) :=
      (Real.log_div (ne_of_gt huk1) (ne_of_gt huk)).symm
    have e2 : Real.log (((k + 1 : ℕ)) : ℝ) - Real.log (k : ℝ)
        = Real.log (1 + 1 / (k : ℝ)) := by
      have hpos1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith [hsk]
      rw [hcast, ← Real.log_div (ne_of_gt hpos1) (ne_of_gt hsk)]
      congr 1
      rw [add_div, div_self (ne_of_gt hsk)]
    have e3 : Real.log (u (k + 1) / u k)
        = Real.log (1 + (u (k + 1) / u k - 1)) := by
      congr 1
      ring
    have key : Real.log (u (k + 1)) - Real.log (u k)
        - 3 / 2 * (Real.log (((k + 1 : ℕ)) : ℝ) - Real.log (k : ℝ))
        = (Real.log (1 + (u (k + 1) / u k - 1)) - (u (k + 1) / u k - 1))
          + (u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ)))
          - 3 / 2 * (Real.log (1 + 1 / (k : ℝ)) - 1 / (k : ℝ)) := by
      rw [e1, e2, e3]
      ring
    have hA : |Real.log (1 + (u (k + 1) / u k - 1)) - (u (k + 1) / u k - 1)|
        ≤ 2 * (u (k + 1) / u k - 1) ^ 2 :=
      log_one_add_le _ (htbound k hk)
    have hB : |u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))| ≤ K / (k : ℝ) ^ 2 :=
      hudev k hk
    have hC : |Real.log (1 + 1 / (k : ℝ)) - 1 / (k : ℝ)|
        ≤ 2 * (1 / (k : ℝ)) ^ 2 :=
      log_one_add_le _ (hinvbound k hk)
    have hC2 : (1 / (k : ℝ)) ^ 2 = 1 / (k : ℝ) ^ 2 := by
      rw [div_pow, one_pow]
    have htsqk := htsq k hk
    rw [key]
    have hmul : |3 / 2 * (Real.log (1 + 1 / (k : ℝ)) - 1 / (k : ℝ))|
        = 3 / 2 * |Real.log (1 + 1 / (k : ℝ)) - 1 / (k : ℝ)| := by
      rw [abs_mul, abs_of_nonneg (by norm_num)]
    have hle : |(Real.log (1 + (u (k + 1) / u k - 1)) - (u (k + 1) / u k - 1))
          + (u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ)))
          - 3 / 2 * (Real.log (1 + 1 / (k : ℝ)) - 1 / (k : ℝ))|
        ≤ |Real.log (1 + (u (k + 1) / u k - 1)) - (u (k + 1) / u k - 1)|
          + |u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))|
          + |3 / 2 * (Real.log (1 + 1 / (k : ℝ)) - 1 / (k : ℝ))| :=
      htri _ _ _
    rw [hmul] at hle
    -- Clear denominators by multiplying with `S = (k:ℝ)^2 > 0`.
    have hS : (0 : ℝ) < (k : ℝ) ^ 2 := pow_pos hsk 2
    have hSne : (k : ℝ) ^ 2 ≠ 0 := ne_of_gt hS
    have gA : |Real.log (1 + (u (k + 1) / u k - 1)) - (u (k + 1) / u k - 1)|
          * (k : ℝ) ^ 2
        ≤ 2 * ((u (k + 1) / u k - 1) ^ 2 * (k : ℝ) ^ 2) := by
      have h := mul_le_mul_of_nonneg_right hA hS.le
      linarith [h]
    have gB : |u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))| * (k : ℝ) ^ 2 ≤ K := by
      have h := mul_le_mul_of_nonneg_right hB hS.le
      rwa [div_mul_cancel₀ _ hSne] at h
    have gC : |Real.log (1 + 1 / (k : ℝ)) - 1 / (k : ℝ)| * (k : ℝ) ^ 2 ≤ 2 := by
      have h := mul_le_mul_of_nonneg_right hC hS.le
      have e : (2 * (1 / (k : ℝ)) ^ 2) * (k : ℝ) ^ 2 = 2 := by
        rw [hC2, mul_assoc, div_mul_cancel₀ _ hSne, mul_one]
      rwa [e] at h
    have gt : (u (k + 1) / u k - 1) ^ 2 * (k : ℝ) ^ 2 ≤ 2 * K ^ 2 + 9 / 2 := by
      have h := mul_le_mul_of_nonneg_right htsqk hS.le
      rwa [div_mul_cancel₀ _ hSne] at h
    have gV : |(Real.log (1 + (u (k + 1) / u k - 1)) - (u (k + 1) / u k - 1))
          + (u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ)))
          - 3 / 2 * (Real.log (1 + 1 / (k : ℝ)) - 1 / (k : ℝ))| * (k : ℝ) ^ 2
        ≤ 4 * K ^ 2 + K + 12 := by
      have hstep := mul_le_mul_of_nonneg_right hle hS.le
      have e : (|Real.log (1 + (u (k + 1) / u k - 1)) - (u (k + 1) / u k - 1)|
            + |u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))|
            + 3 / 2 * |Real.log (1 + 1 / (k : ℝ)) - 1 / (k : ℝ)|) * (k : ℝ) ^ 2
          = |Real.log (1 + (u (k + 1) / u k - 1)) - (u (k + 1) / u k - 1)|
            * (k : ℝ) ^ 2
            + |u (k + 1) / u k - 1 - 3 / (2 * (k : ℝ))| * (k : ℝ) ^ 2
            + 3 / 2 * (|Real.log (1 + 1 / (k : ℝ)) - 1 / (k : ℝ)|
              * (k : ℝ) ^ 2) := by
        ring
      have h2 : 2 * ((u (k + 1) / u k - 1) ^ 2 * (k : ℝ) ^ 2)
          ≤ 2 * (2 * K ^ 2 + 9 / 2) := by
        linarith [gt]
      linarith [hstep, e, gA, gB, gC, h2]
    exact (le_div_iff₀ hS).mpr gV
  exact growth_limit u hpos K hK k₂ hincr

/-- Ratio bounds for `J` at exponential points: the input for `growth`. -/
private lemma logRecip_ratio :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      |w.logRecip (Real.exp (((k + 1 : ℕ)) : ℝ)) / w.logRecip (Real.exp (k : ℝ))
        - (1 + 3 / (2 * (k : ℝ)))| ≤ K / (k : ℝ) ^ 2 := by
  obtain ⟨C, hC⟩ := w.logRecip_near
  obtain ⟨D, hD, hCD⟩ : ∃ D : ℝ, 0 ≤ D ∧ C ≤ D :=
    ⟨|C|, abs_nonneg _, le_abs_self _⟩
  have hC' : ∀ x : ℝ, 1 ≤ x →
      |w.logRecip x - 2 / 3 * w.recip x * Real.log x| ≤ 2 / 3 * D * w.recip x := by
    intro x hx
    have h := hC x hx
    have hA := w.recip_nonneg x
    have h3 : C * w.recip x ≤ D * w.recip x :=
      mul_le_mul_of_nonneg_right hCD hA
    calc |w.logRecip x - 2 / 3 * w.recip x * Real.log x| ≤ 2 / 3 * C * w.recip x := h
      _ ≤ 2 / 3 * D * w.recip x := by linarith [h3]
  have hE : ∀ k : ℕ, (1 : ℝ) ≤ Real.exp (k : ℝ) := by
    intro k
    have h := Real.add_one_le_exp (k : ℝ)
    have hnn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hA1 : w.recip 1 = 1 := by
    have hfl : ⌊(1 : ℝ)⌋₊ = 1 := Nat.floor_one
    have hIoc : Finset.Ioc 0 (1 : ℕ) = {1} := by decide
    unfold Weight.recip
    rw [hfl, hIoc, Finset.sum_singleton]
    simp
  have hJ1zero : w.logRecip 1 = 0 := by
    have hfl : ⌊(1 : ℝ)⌋₊ = 1 := Nat.floor_one
    have hIoc : Finset.Ioc 0 (1 : ℕ) = {1} := by decide
    unfold Weight.logRecip
    rw [hfl, hIoc, Finset.sum_singleton]
    simp
  have hlogR : ∀ k : ℕ,
      Real.log (Real.exp (((k + 1 : ℕ)) : ℝ) / Real.exp (k : ℝ)) = 1 := by
    intro k
    have hcast : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt (Real.exp_pos _)),
      Real.log_exp, Real.log_exp, hcast]
    ring
  have hEmono : ∀ k : ℕ,
      Real.exp (k : ℝ) ≤ Real.exp (((k + 1 : ℕ)) : ℝ) := by
    intro k
    have hcast : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    apply Real.exp_le_exp_of_le
    linarith
  have hJ1 : 1 ≤ w.logRecip (Real.exp 1) := by
    have h1e : (1 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp (1 : ℝ)
      linarith
    obtain ⟨lo, _⟩ := w.logRecip_increment (le_rfl : (1 : ℝ) ≤ 1) h1e
    have hlog : Real.log (Real.exp 1 / 1) = 1 := by
      rw [div_one, Real.log_exp]
    rw [hA1, hJ1zero, hlog] at lo
    linarith
  have hJk : ∀ k : ℕ, 1 ≤ k → (1 : ℝ) ≤ w.logRecip (Real.exp (k : ℝ)) := by
    intro k hk
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have h1k : Real.exp 1 ≤ Real.exp (k : ℝ) :=
      Real.exp_le_exp_of_le hkR
    have h1e : (1 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp (1 : ℝ)
      linarith
    obtain ⟨lo, _⟩ := w.logRecip_increment h1e h1k
    have hnn : 0 ≤ w.recip (Real.exp 1)
        * Real.log (Real.exp (k : ℝ) / Real.exp 1) := by
      apply mul_nonneg (w.recip_nonneg _)
      apply Real.log_nonneg
      rw [le_div_iff₀ (Real.exp_pos _)]
      simpa using h1k
    linarith [lo, hnn, hJ1]
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (2 * D + 2)
  have hk₀R : 2 * D + 2 < (k₀ : ℝ) := hk₀
  have hk₀pos : 1 ≤ k₀ := by
    have hle : (1 : ℝ) ≤ (k₀ : ℝ) := by linarith [hk₀R, hD]
    exact_mod_cast hle
  refine ⟨3 * (2 * D + 1) / 2, by linarith [hD], k₀, hk₀pos, fun k hk => ?_⟩
  have hs1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_trans hk₀pos hk
  have hsk : (0 : ℝ) < (k : ℝ) := by linarith
  have hsk2 : 2 * D + 2 ≤ (k : ℝ) := le_trans hk₀R.le (by exact_mod_cast hk)
  have hJpos : 0 < w.logRecip (Real.exp (k : ℝ)) := by
    have h := hJk k (le_trans hk₀pos hk)
    linarith
  have hN6k := hC' (Real.exp (k : ℝ)) (hE k)
  rw [Real.log_exp] at hN6k
  have hN6k1 := hC' (Real.exp (((k + 1 : ℕ)) : ℝ)) (hE (k + 1))
  have hlogk1 : Real.log (Real.exp (((k + 1 : ℕ)) : ℝ)) = ((k + 1 : ℕ) : ℝ) :=
    Real.log_exp _
  rw [hlogk1] at hN6k1
  obtain ⟨hN7lo, hN7hi⟩ := w.logRecip_increment (hE k) (hEmono k)
  rw [hlogR k, mul_one] at hN7lo hN7hi
  have hposSD : (0 : ℝ) < (k : ℝ) + D := add_pos_of_pos_of_nonneg hsk hD
  have hposT : (0 : ℝ) < ((k : ℝ) + 1) - D := by linarith [hsk2, hD]
  have hSDne : (k : ℝ) + D ≠ 0 := ne_of_gt hposSD
  have hTne : ((k : ℝ) + 1) - D ≠ 0 := ne_of_gt hposT
  have hsne : (k : ℝ) ≠ 0 := ne_of_gt hsk
  have hs2ne : (k : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hsne
  have hAlo : (3 / 2) * w.logRecip (Real.exp (k : ℝ)) / ((k : ℝ) + D)
      ≤ w.recip (Real.exp (k : ℝ)) := by
    have hhi := (abs_le.mp hN6k).2
    have hle : w.logRecip (Real.exp (k : ℝ))
        ≤ (2 / 3) * ((k : ℝ) + D) * w.recip (Real.exp (k : ℝ)) := by
      linarith [hhi]
    have hpos : (0 : ℝ) ≤ (3 / 2) / ((k : ℝ) + D) :=
      div_nonneg (by norm_num) hposSD.le
    have h := mul_le_mul_of_nonneg_right hle hpos
    have e1 : ((2 / 3) * ((k : ℝ) + D) * w.recip (Real.exp (k : ℝ)))
          * ((3 / 2) / ((k : ℝ) + D))
        = w.recip (Real.exp (k : ℝ)) := by
      field_simp
    have e0 : w.logRecip (Real.exp (k : ℝ)) * ((3 / 2) / ((k : ℝ) + D))
        = (3 / 2) * w.logRecip (Real.exp (k : ℝ)) / ((k : ℝ) + D) := by ring
    rw [e0, e1] at h
    exact h
  have hA'hi : w.recip (Real.exp (((k + 1 : ℕ)) : ℝ))
      ≤ w.logRecip (Real.exp (((k + 1 : ℕ)) : ℝ))
        * (3 / (2 * (((k : ℝ) + 1) - D))) := by
    have hlo := (abs_le.mp hN6k1).1
    have hcast : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    have hle' : (2 / 3) * (((k : ℝ) + 1) - D)
          * w.recip (Real.exp (((k + 1 : ℕ)) : ℝ))
        ≤ w.logRecip (Real.exp (((k + 1 : ℕ)) : ℝ)) := by
      have e : (2 / 3) * (((k : ℝ) + 1) - D)
            * w.recip (Real.exp (((k + 1 : ℕ)) : ℝ))
          = (2 / 3) * w.recip (Real.exp (((k + 1 : ℕ)) : ℝ)) * (((k + 1 : ℕ)) : ℝ)
            - (2 / 3) * D * w.recip (Real.exp (((k + 1 : ℕ)) : ℝ)) := by
        rw [hcast]
        ring
      rw [e]
      linarith [hlo]
    have hpos : (0 : ℝ) ≤ 3 / (2 * (((k : ℝ) + 1) - D)) :=
      div_nonneg (by norm_num) (mul_nonneg (by norm_num) hposT.le)
    have h := mul_le_mul_of_nonneg_right hle' hpos
    have e1 : ((2 / 3) * (((k : ℝ) + 1) - D)
          * w.recip (Real.exp (((k + 1 : ℕ)) : ℝ)))
          * (3 / (2 * (((k : ℝ) + 1) - D)))
        = w.recip (Real.exp (((k + 1 : ℕ)) : ℝ)) := by
      field_simp
    rw [e1] at h
    exact h
  have h1 : (3 / 2) * w.logRecip (Real.exp (k : ℝ)) / ((k : ℝ) + D)
      ≤ w.logRecip (Real.exp (((k + 1 : ℕ)) : ℝ)) - w.logRecip (Real.exp (k : ℝ)) :=
    le_trans hAlo hN7lo
  have h2 : (3 / 2) / ((k : ℝ) + D)
      ≤ (w.logRecip (Real.exp (((k + 1 : ℕ)) : ℝ)) - w.logRecip (Real.exp (k : ℝ)))
        / w.logRecip (Real.exp (k : ℝ)) := by
    rw [le_div_iff₀ hJpos]
    have e : ((3 / 2) / ((k : ℝ) + D)) * w.logRecip (Real.exp (k : ℝ))
        = (3 / 2) * w.logRecip (Real.exp (k : ℝ)) / ((k : ℝ) + D) := by ring
    rw [e]
    exact h1
  have eJJ : w.logRecip (Real.exp (((k + 1 : ℕ)) : ℝ)) / w.logRecip (Real.exp (k : ℝ)) - 1
      = (w.logRecip (Real.exp (((k + 1 : ℕ)) : ℝ)) - w.logRecip (Real.exp (k : ℝ)))
        / w.logRecip (Real.exp (k : ℝ)) := by
    rw [← div_self (ne_of_gt hJpos), ← sub_div]
  have h3 : 1 + (3 / 2) / ((k : ℝ) + D)
      ≤ w.logRecip (Real.exp (((k + 1 : ℕ)) : ℝ)) / w.logRecip (Real.exp (k : ℝ)) := by
    linarith [h2, eJJ]
  have e' : (3 / 2) / ((k : ℝ) + D) - 3 / (2 * (k : ℝ))
      = 3 * D ^ 2 / (2 * (k : ℝ) ^ 2 * ((k : ℝ) + D))
        - (3 * D / 2) / (k : ℝ) ^ 2 := by
    field_simp
    ring
  have hdenpos : (0 : ℝ) < 2 * (k : ℝ) ^ 2 * ((k : ℝ) + D) :=
    mul_pos (mul_pos (by norm_num) (pow_pos hsk 2)) hposSD
  have hnn : (0 : ℝ) ≤ 3 * D ^ 2 / (2 * (k : ℝ) ^ 2 * ((k : ℝ) + D)) :=
    div_nonneg (mul_nonneg (by norm_num) (sq_nonneg D)) hdenpos.le
  have h4 : -((3 * D / 2) / (k : ℝ) ^ 2)
      ≤ (3 / 2) / ((k : ℝ) + D) - 3 / (2 * (k : ℝ)) := by
    rw [e']
    linarith [hnn]
  have hlow : -((3 * D / 2) / (k : ℝ) ^ 2)
      ≤ w.logRecip (Real.exp (((k + 1 : ℕ)) : ℝ)) / w.logRecip (Real.exp (k : ℝ))
        - (1 + 3 / (2 * (k : ℝ))) := by
    linarith [h3, h4]
  have h5 : w.logRecip (Real.exp (((k + 1 : ℕ)) : ℝ)) - w.logRecip (Real.exp (k : ℝ))
      ≤ w.logRecip (Real.exp (((k + 1 : ℕ)) : ℝ))
        * (3 / (2 * (((k : ℝ) + 1) - D))) :=
    le_trans hN7hi hA'hi
  have h6 : w.logRecip (Real.exp (((k + 1 : ℕ)) : ℝ))
        * (1 - 3 / (2 * (((k : ℝ) + 1) - D)))
      ≤ w.logRecip (Real.exp (k : ℝ)) := by
    linarith [h5]
  have hTs : (k : ℝ) ≤ 2 * (((k : ℝ) + 1) - D) - 3 := by linarith [hsk2]
  have h2T3pos : (0 : ℝ) < 2 * (((k : ℝ) + 1) - D) - 3 := by
    linarith [hTs, hsk]
  have h2T3ne : 2 * (((k : ℝ) + 1) - D) - 3 ≠ 0 := ne_of_gt h2T3pos
  have h2Tne : 2 * (((k : ℝ) + 1) - D) ≠ 0 :=
    mul_ne_zero (by norm_num) hTne
  have h2sne : 2 * (k : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hsne
  have hδ : 3 / (2 * (((k : ℝ) + 1) - D)) < 1 := by
    have hT32 : (3 : ℝ) / 2 < ((k : ℝ) + 1) - D := by linarith [hsk2, hD]
    rw [div_lt_one (by linarith [hposT] : (0 : ℝ) < 2 * (((k : ℝ) + 1) - D))]
    linarith [hT32]
  have h1δ : (0 : ℝ) < 1 - 3 / (2 * (((k : ℝ) + 1) - D)) := by linarith [hδ]
  have h1δne : (1 - 3 / (2 * (((k : ℝ) + 1) - D))) ≠ 0 := ne_of_gt h1δ
  have h7 : w.logRecip (Real.exp (((k + 1 : ℕ)) : ℝ)) / w.logRecip (Real.exp (k : ℝ))
      ≤ 1 / (1 - 3 / (2 * (((k : ℝ) + 1) - D))) := by
    rw [le_div_iff₀ h1δ]
    have e : (w.logRecip (Real.exp (((k + 1 : ℕ)) : ℝ)) / w.logRecip (Real.exp (k : ℝ)))
          * (1 - 3 / (2 * (((k : ℝ) + 1) - D)))
        = (w.logRecip (Real.exp (((k + 1 : ℕ)) : ℝ))
            * (1 - 3 / (2 * (((k : ℝ) + 1) - D)))) / w.logRecip (Real.exp (k : ℝ)) := by
      ring
    rw [e, div_le_one hJpos]
    exact h6
  have hfrac : 1 / (1 - 3 / (2 * (((k : ℝ) + 1) - D))) - 1
      = (3 / (2 * (((k : ℝ) + 1) - D)))
        / (1 - 3 / (2 * (((k : ℝ) + 1) - D))) := by
    field_simp
    ring
  have hfrac2 : (3 / (2 * (((k : ℝ) + 1) - D)))
        / (1 - 3 / (2 * (((k : ℝ) + 1) - D)))
      = 3 / (2 * (((k : ℝ) + 1) - D) - 3) := by
    field_simp
  have h10 : 3 / (2 * (((k : ℝ) + 1) - D) - 3) - 3 / (2 * (k : ℝ))
      = 3 * (2 * D + 1) / (2 * (k : ℝ) * (2 * (((k : ℝ) + 1) - D) - 3)) := by
    field_simp
    ring
  have hden_ge : 2 * (k : ℝ) ^ 2
      ≤ 2 * (k : ℝ) * (2 * (((k : ℝ) + 1) - D) - 3) := by
    have h := mul_le_mul_of_nonneg_left hTs (show (0 : ℝ) ≤ 2 * (k : ℝ) by
      linarith [hsk])
    linarith [h]
  have hnum_nn : (0 : ℝ) ≤ 3 * (2 * D + 1) := by linarith [hD]
  have hden_pos : (0 : ℝ) < 2 * (k : ℝ) ^ 2 := by
    have h := pow_pos hsk 2
    linarith [h]
  have h11 : 3 * (2 * D + 1) / (2 * (k : ℝ) * (2 * (((k : ℝ) + 1) - D) - 3))
      ≤ 3 * (2 * D + 1) / (2 * (k : ℝ) ^ 2) := by
    have h1 : (1 : ℝ) / (2 * (k : ℝ) * (2 * (((k : ℝ) + 1) - D) - 3))
        ≤ 1 / (2 * (k : ℝ) ^ 2) :=
      one_div_le_one_div_of_le hden_pos hden_ge
    have e1 : 3 * (2 * D + 1) / (2 * (k : ℝ) * (2 * (((k : ℝ) + 1) - D) - 3))
        = 3 * (2 * D + 1) * (1 / (2 * (k : ℝ) * (2 * (((k : ℝ) + 1) - D) - 3))) := by
      rw [div_eq_mul_inv, inv_eq_one_div]
    have e2 : 3 * (2 * D + 1) / (2 * (k : ℝ) ^ 2)
        = 3 * (2 * D + 1) * (1 / (2 * (k : ℝ) ^ 2)) := by
      rw [div_eq_mul_inv, inv_eq_one_div]
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left h1 hnum_nn
  have h8 : w.logRecip (Real.exp (((k + 1 : ℕ)) : ℝ)) / w.logRecip (Real.exp (k : ℝ)) - 1
      ≤ (3 / (2 * (((k : ℝ) + 1) - D)))
        / (1 - 3 / (2 * (((k : ℝ) + 1) - D))) := by
    linarith [h7, hfrac]
  have hup : w.logRecip (Real.exp (((k + 1 : ℕ)) : ℝ)) / w.logRecip (Real.exp (k : ℝ))
        - (1 + 3 / (2 * (k : ℝ)))
      ≤ (3 * (2 * D + 1) / 2) / (k : ℝ) ^ 2 := by
    have efin : (3 * (2 * D + 1) / 2) / (k : ℝ) ^ 2
        = 3 * (2 * D + 1) / (2 * (k : ℝ) ^ 2) := by ring
    linarith [h8, hfrac2, h10, h11, efin]
  have hfin : |w.logRecip (Real.exp (((k + 1 : ℕ)) : ℝ)) / w.logRecip (Real.exp (k : ℝ))
        - (1 + 3 / (2 * (k : ℝ)))| ≤ (3 * (2 * D + 1) / 2) / (k : ℝ) ^ 2 := by
    rw [abs_le]
    constructor
    · have hKlo : -((3 * (2 * D + 1) / 2) / (k : ℝ) ^ 2)
          ≤ -((3 * D / 2) / (k : ℝ) ^ 2) := by
        have h : (3 * D / 2) ≤ 3 * (2 * D + 1) / 2 := by linarith [hD]
        have h2 : -(3 * (2 * D + 1) / 2) ≤ -(3 * D / 2) := by linarith [h]
        have e1 : -((3 * (2 * D + 1) / 2) / (k : ℝ) ^ 2)
            = (-(3 * (2 * D + 1) / 2)) / (k : ℝ) ^ 2 := by ring
        have e2 : -((3 * D / 2) / (k : ℝ) ^ 2)
            = (-(3 * D / 2)) / (k : ℝ) ^ 2 := by ring
        rw [e1, e2, div_le_div_iff_of_pos_right (pow_pos hsk 2)]
        exact h2
      linarith [hlow, hKlo]
    · exact hup
  exact hfin

/-- `J` at exponential points is positive. -/
private lemma logRecip_exp_pos : ∀ k : ℕ, 1 ≤ k → 0 < w.logRecip (Real.exp (k : ℝ)) := by
  have hA1 : w.recip 1 = 1 := by
    have hfl : ⌊(1 : ℝ)⌋₊ = 1 := Nat.floor_one
    have hIoc : Finset.Ioc 0 (1 : ℕ) = {1} := by decide
    unfold Weight.recip
    rw [hfl, hIoc, Finset.sum_singleton]
    simp
  have hJ1zero : w.logRecip 1 = 0 := by
    have hfl : ⌊(1 : ℝ)⌋₊ = 1 := Nat.floor_one
    have hIoc : Finset.Ioc 0 (1 : ℕ) = {1} := by decide
    unfold Weight.logRecip
    rw [hfl, hIoc, Finset.sum_singleton]
    simp
  have h1e : (1 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hJ1 : 1 ≤ w.logRecip (Real.exp 1) := by
    obtain ⟨lo, _⟩ := w.logRecip_increment (le_rfl : (1 : ℝ) ≤ 1) h1e
    have hlog : Real.log (Real.exp 1 / 1) = 1 := by
      rw [div_one, Real.log_exp]
    rw [hA1, hJ1zero, hlog] at lo
    linarith
  intro k hk
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h1k : Real.exp 1 ≤ Real.exp (k : ℝ) :=
    Real.exp_le_exp_of_le hkR
  have hEk : (1 : ℝ) ≤ Real.exp (k : ℝ) := by
    have h := Real.add_one_le_exp (k : ℝ)
    have hnn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  obtain ⟨lo, _⟩ := w.logRecip_increment h1e h1k
  have hnn : 0 ≤ w.recip (Real.exp 1)
      * Real.log (Real.exp (k : ℝ) / Real.exp 1) := by
    apply mul_nonneg (w.recip_nonneg _)
    apply Real.log_nonneg
    rw [le_div_iff₀ (Real.exp_pos _)]
    simpa using h1k
  linarith [lo, hnn, hJ1]

/-- Sequential version: `A(e^k) / √k → α` for some `α > 0`. -/
private lemma recip_seq_tendsto :
    ∃ α : ℝ, 0 < α ∧
      Filter.Tendsto (fun k : ℕ => w.recip (Real.exp (k : ℝ)) / Real.sqrt (k : ℝ))
        Filter.atTop (nhds α) := by
  obtain ⟨K, hK, k₀, hk₀, hstep⟩ := w.logRecip_ratio
  obtain ⟨C, hC⟩ := w.logRecip_near
  have hpos : ∀ k : ℕ, 1 ≤ k → 0 < (fun k => w.logRecip (Real.exp (k : ℝ))) k :=
    fun k hk => w.logRecip_exp_pos k hk
  obtain ⟨L, hLpos, hL⟩ := growth _ hpos K hK k₀ hk₀ hstep
  have hrpow : ∀ k : ℕ, 1 ≤ k → (k : ℝ) ^ (3 / 2 : ℝ)
      = (k : ℝ) * Real.sqrt (k : ℝ) := by
    intro k hk
    have hsk : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hk
    have e : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
    rw [e, Real.rpow_add hsk, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hconv : ∀ k : ℕ, 1 ≤ k → |C| < (k : ℝ) →
      (3 / 2) * w.logRecip (Real.exp (k : ℝ)) / ((k : ℝ) + C)
        ≤ w.recip (Real.exp (k : ℝ)) ∧
      w.recip (Real.exp (k : ℝ))
        ≤ (3 / 2) * w.logRecip (Real.exp (k : ℝ)) / ((k : ℝ) - C) := by
    intro k hk hCk
    have hEk : (1 : ℝ) ≤ Real.exp (k : ℝ) := by
      have h := Real.add_one_le_exp (k : ℝ)
      have hnn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    have hN6 := hC (Real.exp (k : ℝ)) hEk
    rw [Real.log_exp] at hN6
    have hsk : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hk
    have hCab : -(k : ℝ) < C ∧ C < (k : ℝ) := abs_lt.mp hCk
    have hposPC : (0 : ℝ) < (k : ℝ) + C := by linarith [hCab.1]
    have hposMC : (0 : ℝ) < (k : ℝ) - C := by linarith [hCab.2]
    have hSDne : (k : ℝ) + C ≠ 0 := ne_of_gt hposPC
    have hMDne : (k : ℝ) - C ≠ 0 := ne_of_gt hposMC
    have hhi := (abs_le.mp hN6).2
    have hlo := (abs_le.mp hN6).1
    constructor
    · have hle : w.logRecip (Real.exp (k : ℝ))
          ≤ (2 / 3) * ((k : ℝ) + C) * w.recip (Real.exp (k : ℝ)) := by
        linarith [hhi]
      have hpos : (0 : ℝ) ≤ (3 / 2) / ((k : ℝ) + C) :=
        div_nonneg (by norm_num) hposPC.le
      have h := mul_le_mul_of_nonneg_right hle hpos
      have e1 : ((2 / 3) * ((k : ℝ) + C) * w.recip (Real.exp (k : ℝ)))
            * ((3 / 2) / ((k : ℝ) + C))
          = w.recip (Real.exp (k : ℝ)) := by
        field_simp
      have e0 : w.logRecip (Real.exp (k : ℝ)) * ((3 / 2) / ((k : ℝ) + C))
          = (3 / 2) * w.logRecip (Real.exp (k : ℝ)) / ((k : ℝ) + C) := by ring
      rw [e0, e1] at h
      exact h
    · have hle : (2 / 3) * ((k : ℝ) - C) * w.recip (Real.exp (k : ℝ))
          ≤ w.logRecip (Real.exp (k : ℝ)) := by
        linarith [hlo]
      have hpos : (0 : ℝ) ≤ (3 / 2) / ((k : ℝ) - C) :=
        div_nonneg (by norm_num) hposMC.le
      have h := mul_le_mul_of_nonneg_right hle hpos
      have e1 : ((2 / 3) * ((k : ℝ) - C) * w.recip (Real.exp (k : ℝ)))
            * ((3 / 2) / ((k : ℝ) - C))
          = w.recip (Real.exp (k : ℝ)) := by
        field_simp
      have e0 : w.logRecip (Real.exp (k : ℝ)) * ((3 / 2) / ((k : ℝ) - C))
          = (3 / 2) * w.logRecip (Real.exp (k : ℝ)) / ((k : ℝ) - C) := by ring
      rw [e0, e1] at h
      exact h
  have hLo : Filter.Tendsto
      (fun k : ℕ => (3 / 2) * ((w.logRecip (Real.exp (k : ℝ)) / (k : ℝ) ^ (3 / 2 : ℝ))
        * ((k : ℝ) / ((k : ℝ) + C))))
      Filter.atTop (nhds ((3 / 2) * L)) := by
    have hmul := hL.mul (tendsto_natCast_div_add_atTop C)
    have hmul2 : Filter.Tendsto
        (fun k : ℕ => (3 / 2) * ((w.logRecip (Real.exp (k : ℝ)) / (k : ℝ) ^ (3 / 2 : ℝ))
          * ((k : ℝ) / ((k : ℝ) + C))))
        Filter.atTop (nhds ((3 / 2) * (L * 1))) :=
      tendsto_const_nhds.mul hmul
    simpa [mul_one] using hmul2
  have hHi : Filter.Tendsto
      (fun k : ℕ => (3 / 2) * ((w.logRecip (Real.exp (k : ℝ)) / (k : ℝ) ^ (3 / 2 : ℝ))
        * ((k : ℝ) / ((k : ℝ) - C))))
      Filter.atTop (nhds ((3 / 2) * L)) := by
    have hmul := hL.mul (tendsto_natCast_div_add_atTop (-C))
    have hmul2 : Filter.Tendsto
        (fun k : ℕ => (3 / 2) * ((w.logRecip (Real.exp (k : ℝ)) / (k : ℝ) ^ (3 / 2 : ℝ))
          * ((k : ℝ) / ((k : ℝ) + (-C)))))
        Filter.atTop (nhds ((3 / 2) * (L * 1))) :=
      tendsto_const_nhds.mul hmul
    have heq : (fun k : ℕ => (3 / 2) * ((w.logRecip (Real.exp (k : ℝ)) / (k : ℝ) ^ (3 / 2 : ℝ))
          * ((k : ℝ) / ((k : ℝ) + (-C)))))
        = (fun k : ℕ => (3 / 2) * ((w.logRecip (Real.exp (k : ℝ)) / (k : ℝ) ^ (3 / 2 : ℝ))
          * ((k : ℝ) / ((k : ℝ) - C)))) := by
      funext k
      have hsub : ((k : ℝ) - C) = ((k : ℝ) + (-C)) := by ring
      rw [hsub]
    rw [heq] at hmul2
    simpa [mul_one] using hmul2
  obtain ⟨k₁, hk₁⟩ := exists_nat_gt (|C| + 1)
  have hk₁R : |C| + 1 < (k₁ : ℝ) := hk₁
  have hk₁pos : 1 ≤ k₁ := by
    have hle : (1 : ℝ) ≤ (k₁ : ℝ) := by
      have hCnn : (0 : ℝ) ≤ |C| := abs_nonneg _
      linarith
    exact_mod_cast hle
  refine ⟨(3 / 2) * L, by linarith [hLpos], ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hLo hHi ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop k₁] with k hk
    have hk1 : 1 ≤ k := le_trans hk₁pos hk
    have hCk : |C| < (k : ℝ) := by
      have hle : (k₁ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    have hconvk := hconv k hk1 hCk
    have hsk : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hk1
    have hsqrt : (0 : ℝ) < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hsk
    have hsqne : Real.sqrt (k : ℝ) ≠ 0 := ne_of_gt hsqrt
    have hkne : (k : ℝ) ≠ 0 := ne_of_gt hsk
    have hPCne : (k : ℝ) + C ≠ 0 := ne_of_gt (by
      have hCab : -(k : ℝ) < C := (abs_lt.mp hCk).1
      linarith)
    have e : ((3 / 2) * w.logRecip (Real.exp (k : ℝ)) / ((k : ℝ) + C))
          / Real.sqrt (k : ℝ)
        = (3 / 2) * ((w.logRecip (Real.exp (k : ℝ)) / (k : ℝ) ^ (3 / 2 : ℝ))
          * ((k : ℝ) / ((k : ℝ) + C))) := by
      rw [hrpow k hk1]
      field_simp
    rw [← e]
    exact div_le_div_of_nonneg_right hconvk.1 (Real.sqrt_nonneg _)
  · filter_upwards [Filter.eventually_ge_atTop k₁] with k hk
    have hk1 : 1 ≤ k := le_trans hk₁pos hk
    have hCk : |C| < (k : ℝ) := by
      have hle : (k₁ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    have hconvk := hconv k hk1 hCk
    have hsk : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hk1
    have hsqrt : (0 : ℝ) < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hsk
    have hsqne : Real.sqrt (k : ℝ) ≠ 0 := ne_of_gt hsqrt
    have hkne : (k : ℝ) ≠ 0 := ne_of_gt hsk
    have hMCne : (k : ℝ) - C ≠ 0 := ne_of_gt (by
      have hCab : C < (k : ℝ) := (abs_lt.mp hCk).2
      linarith)
    have e : w.recip (Real.exp (k : ℝ)) / Real.sqrt (k : ℝ)
        ≤ ((3 / 2) * w.logRecip (Real.exp (k : ℝ)) / ((k : ℝ) - C))
          / Real.sqrt (k : ℝ) :=
      div_le_div_of_nonneg_right hconvk.2 (Real.sqrt_nonneg _)
    have e2 : ((3 / 2) * w.logRecip (Real.exp (k : ℝ)) / ((k : ℝ) - C))
          / Real.sqrt (k : ℝ)
        = (3 / 2) * ((w.logRecip (Real.exp (k : ℝ)) / (k : ℝ) ^ (3 / 2 : ℝ))
          * ((k : ℝ) / ((k : ℝ) - C))) := by
      rw [hrpow k hk1]
      field_simp
    rw [e2] at e
    exact e

/-- Shifted end: `A(e^k) / √(k+1) → α`. -/
private lemma recip_seq_low (α : ℝ)
    (hAseq : Filter.Tendsto
      (fun k : ℕ => w.recip (Real.exp (k : ℝ)) / Real.sqrt (k : ℝ))
      Filter.atTop (nhds α)) :
    Filter.Tendsto
      (fun k : ℕ => w.recip (Real.exp (k : ℝ)) / Real.sqrt (((k + 1 : ℕ)) : ℝ))
      Filter.atTop (nhds α) := by
  have hratio : Filter.Tendsto
      (fun k : ℕ => Real.sqrt (k : ℝ) / Real.sqrt (((k + 1 : ℕ)) : ℝ))
      Filter.atTop (nhds 1) := by
    have hbase : Filter.Tendsto (fun k : ℕ => (k : ℝ) / (((k + 1 : ℕ)) : ℝ))
        Filter.atTop (nhds 1) := by
      have h := tendsto_natCast_div_add_atTop (1 : ℝ)
      refine h.congr' ?_
      filter_upwards with k
      have hcast : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [hcast]
    have h2 := (Real.continuous_sqrt.tendsto 1).comp hbase
    rw [Real.sqrt_one] at h2
    refine h2.congr' ?_
    filter_upwards with k
    exact Real.sqrt_div (Nat.cast_nonneg k) _
  have hmul := hAseq.mul hratio
  have heq : (fun k : ℕ => (w.recip (Real.exp (k : ℝ)) / Real.sqrt (k : ℝ))
          * (Real.sqrt (k : ℝ) / Real.sqrt (((k + 1 : ℕ)) : ℝ)))
        =ᶠ[Filter.atTop]
        (fun k : ℕ => w.recip (Real.exp (k : ℝ)) / Real.sqrt (((k + 1 : ℕ)) : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have hsk : (0 : ℝ) < (k : ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hk
    have hsq : Real.sqrt (k : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hsk)
    have hsq1 : Real.sqrt (((k + 1 : ℕ)) : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr
      (by exact_mod_cast Nat.succ_pos k))
    field_simp
  have h2 := hmul.congr' heq
  simpa [mul_one] using h2

/-- Shifted end: `A(e^{k+1}) / √k → α`. -/
private lemma recip_seq_high (α : ℝ)
    (hAseq : Filter.Tendsto
      (fun k : ℕ => w.recip (Real.exp (k : ℝ)) / Real.sqrt (k : ℝ))
      Filter.atTop (nhds α)) :
    Filter.Tendsto
      (fun k : ℕ => w.recip (Real.exp (((k + 1 : ℕ)) : ℝ)) / Real.sqrt (k : ℝ))
      Filter.atTop (nhds α) := by
  have hshift : Filter.Tendsto
      (fun k : ℕ => w.recip (Real.exp (((k + 1 : ℕ)) : ℝ))
        / Real.sqrt (((k + 1 : ℕ)) : ℝ))
      Filter.atTop (nhds α) := by
    have hiff := tendsto_add_atTop_iff_nat (l := nhds α)
      (f := fun k : ℕ => w.recip (Real.exp (k : ℝ)) / Real.sqrt (k : ℝ)) 1
    exact hiff.mpr hAseq
  have hratio : Filter.Tendsto
      (fun k : ℕ => Real.sqrt (((k + 1 : ℕ)) : ℝ) / Real.sqrt (k : ℝ))
      Filter.atTop (nhds 1) := by
    have hbase : Filter.Tendsto (fun k : ℕ => (((k + 1 : ℕ)) : ℝ) / (k : ℝ))
        Filter.atTop (nhds 1) := by
      have h0 : Filter.Tendsto (fun k : ℕ => (1 : ℝ) / (k : ℝ))
          Filter.atTop (nhds 0) :=
        tendsto_const_div_atTop_nhds_zero_nat 1
      have h1 : Filter.Tendsto (fun k : ℕ => 1 + (1 : ℝ) / (k : ℝ))
          Filter.atTop (nhds (1 + 0)) :=
        tendsto_const_nhds.add h0
      rw [add_zero] at h1
      refine h1.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop 1] with k hk
      have hsk : (k : ℝ) ≠ 0 := by
        have : k ≠ 0 := by omega
        exact_mod_cast this
      have hcast : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [hcast, add_div, div_self hsk]
    have h2 := (Real.continuous_sqrt.tendsto 1).comp hbase
    rw [Real.sqrt_one] at h2
    refine h2.congr' ?_
    filter_upwards with k
    exact Real.sqrt_div (Nat.cast_nonneg _) _
  have hmul := hshift.mul hratio
  have heq : (fun k : ℕ => (w.recip (Real.exp (((k + 1 : ℕ)) : ℝ))
          / Real.sqrt (((k + 1 : ℕ)) : ℝ))
          * (Real.sqrt (((k + 1 : ℕ)) : ℝ) / Real.sqrt (k : ℝ)))
        =ᶠ[Filter.atTop]
        (fun k : ℕ => w.recip (Real.exp (((k + 1 : ℕ)) : ℝ)) / Real.sqrt (k : ℝ)) := by
    filter_upwards with k
    have hS : Real.sqrt (((k + 1 : ℕ)) : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr
      (by exact_mod_cast Nat.succ_pos k))
    field_simp
  have h2 := hmul.congr' heq
  simpa [mul_one] using h2

/-- `A(x) / √(log x)` converges to a positive limit. -/
private lemma recip_tendsto :
    ∃ α : ℝ, 0 < α ∧
      Filter.Tendsto (fun x => w.recip x / Real.sqrt (Real.log x))
        Filter.atTop (nhds α) := by
  obtain ⟨α, hαpos, hAseq⟩ := w.recip_seq_tendsto
  have hlow := w.recip_seq_low α hAseq
  have hhigh := w.recip_seq_high α hAseq
  have hk_tend : Filter.Tendsto (fun x : ℝ => ⌊Real.log x⌋₊)
      Filter.atTop Filter.atTop :=
    tendsto_nat_floor_atTop.comp Real.tendsto_log_atTop
  have hlowx : Filter.Tendsto
      (fun x : ℝ => w.recip (Real.exp (⌊Real.log x⌋₊ : ℝ)) /
        Real.sqrt (((⌊Real.log x⌋₊ + 1 : ℕ)) : ℝ))
      Filter.atTop (nhds α) := hlow.comp hk_tend
  have hhighx : Filter.Tendsto
      (fun x : ℝ => w.recip (Real.exp (((⌊Real.log x⌋₊ + 1 : ℕ)) : ℝ)) /
        Real.sqrt ((⌊Real.log x⌋₊ : ℕ) : ℝ))
      Filter.atTop (nhds α) := hhigh.comp hk_tend
  refine ⟨α, hαpos, ?_⟩
  have key_lo : ∀ᶠ x : ℝ in Filter.atTop,
      w.recip (Real.exp (⌊Real.log x⌋₊ : ℝ)) /
          Real.sqrt (((⌊Real.log x⌋₊ + 1 : ℕ)) : ℝ)
        ≤ w.recip x / Real.sqrt (Real.log x) := by
    filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with x hxe
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
    have hlog1 : (1 : ℝ) ≤ Real.log x := by
      have h := Real.log_le_log (Real.exp_pos 1) hxe
      rwa [Real.log_exp] at h
    have hlognn : (0 : ℝ) ≤ Real.log x := by linarith
    have hkd : ((⌊Real.log x⌋₊ : ℕ) : ℝ) ≤ Real.log x := Nat.floor_le hlognn
    have hku : Real.log x < ((⌊Real.log x⌋₊ : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hexpk : Real.exp ((⌊Real.log x⌋₊ : ℕ) : ℝ) ≤ x := by
      have h := Real.exp_le_exp.mpr hkd
      rwa [Real.exp_log hxpos] at h
    have hcast1 : ((((⌊Real.log x⌋₊ + 1 : ℕ))) : ℝ)
        = ((⌊Real.log x⌋₊ : ℕ) : ℝ) + 1 := by push_cast; ring
    have hAle1 : w.recip (Real.exp ((⌊Real.log x⌋₊ : ℕ) : ℝ)) ≤ w.recip x :=
      w.recip_mono hexpk
    have hsq2 : Real.sqrt (Real.log x)
        ≤ Real.sqrt ((((⌊Real.log x⌋₊ + 1 : ℕ))) : ℝ) := by
      rw [hcast1]
      exact Real.sqrt_le_sqrt hku.le
    have hsqrt_log : (0 : ℝ) < Real.sqrt (Real.log x) :=
      Real.sqrt_pos.mpr (by linarith)
    calc w.recip (Real.exp ((⌊Real.log x⌋₊ : ℕ) : ℝ)) /
            Real.sqrt ((((⌊Real.log x⌋₊ + 1 : ℕ))) : ℝ)
        ≤ w.recip (Real.exp ((⌊Real.log x⌋₊ : ℕ) : ℝ)) / Real.sqrt (Real.log x) :=
          div_le_div_of_nonneg_left (w.recip_nonneg _) hsqrt_log hsq2
      _ ≤ w.recip x / Real.sqrt (Real.log x) :=
          div_le_div_of_nonneg_right hAle1 hsqrt_log.le
  have key_hi : ∀ᶠ x : ℝ in Filter.atTop,
      w.recip x / Real.sqrt (Real.log x)
        ≤ w.recip (Real.exp ((((⌊Real.log x⌋₊ + 1 : ℕ))) : ℝ)) /
          Real.sqrt (((⌊Real.log x⌋₊ : ℕ)) : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with x hxe
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
    have hlog1 : (1 : ℝ) ≤ Real.log x := by
      have h := Real.log_le_log (Real.exp_pos 1) hxe
      rwa [Real.log_exp] at h
    have hlognn : (0 : ℝ) ≤ Real.log x := by linarith
    have hk1 : 1 ≤ ⌊Real.log x⌋₊ := (Nat.one_le_floor_iff _).mpr hlog1
    have hkd : ((⌊Real.log x⌋₊ : ℕ) : ℝ) ≤ Real.log x := Nat.floor_le hlognn
    have hku : Real.log x < ((⌊Real.log x⌋₊ : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hsk : (0 : ℝ) < ((⌊Real.log x⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hk1
    have hcast1 : ((((⌊Real.log x⌋₊ + 1 : ℕ))) : ℝ)
        = ((⌊Real.log x⌋₊ : ℕ) : ℝ) + 1 := by push_cast; ring
    have hxexp : x < Real.exp ((((⌊Real.log x⌋₊ + 1 : ℕ))) : ℝ) := by
      have h := Real.exp_lt_exp.mpr hku
      rw [Real.exp_log hxpos, ← hcast1] at h
      exact h
    have hAle2 : w.recip x ≤ w.recip (Real.exp ((((⌊Real.log x⌋₊ + 1 : ℕ))) : ℝ)) :=
      w.recip_mono hxexp.le
    have hsq1 : Real.sqrt (((⌊Real.log x⌋₊ : ℕ)) : ℝ)
        ≤ Real.sqrt (Real.log x) :=
      Real.sqrt_le_sqrt hkd
    have hsqrt_log : (0 : ℝ) < Real.sqrt (Real.log x) :=
      Real.sqrt_pos.mpr (by linarith)
    calc w.recip x / Real.sqrt (Real.log x)
        ≤ w.recip (Real.exp ((((⌊Real.log x⌋₊ + 1 : ℕ))) : ℝ)) /
          Real.sqrt (Real.log x) :=
          div_le_div_of_nonneg_right hAle2 hsqrt_log.le
      _ ≤ w.recip (Real.exp ((((⌊Real.log x⌋₊ + 1 : ℕ))) : ℝ)) /
          Real.sqrt (((⌊Real.log x⌋₊ : ℕ)) : ℝ) :=
          div_le_div_of_nonneg_left (w.recip_nonneg _)
            (Real.sqrt_pos.mpr hsk) hsq1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowx hhighx key_lo key_hi

/-- `A(x)` tends to infinity. -/
private lemma recip_atTop (α : ℝ) (hα : 0 < α)
    (hA : Filter.Tendsto (fun x => w.recip x / Real.sqrt (Real.log x))
      Filter.atTop (nhds α)) :
    Filter.Tendsto w.recip Filter.atTop Filter.atTop := by
  have hsqrt : Filter.Tendsto (fun x : ℝ => Real.sqrt (Real.log x))
      Filter.atTop Filter.atTop := by
    have h1 : Filter.Tendsto (fun y : ℝ => y ^ (1/2 : ℝ))
        Filter.atTop Filter.atTop :=
      tendsto_rpow_atTop (by norm_num)
    have h2 := h1.comp Real.tendsto_log_atTop
    refine h2.congr' ?_
    filter_upwards with x
    exact (Real.sqrt_eq_rpow _).symm
  have hAev : ∀ᶠ x : ℝ in Filter.atTop, α / 2 ≤ w.recip x / Real.sqrt (Real.log x) := by
    have hmem : Set.Ioi (α / 2) ∈ nhds α := Ioi_mem_nhds (by linarith)
    filter_upwards [hA.eventually hmem] with x hx
    exact le_of_lt (Set.mem_Ioi.mp hx)
  have hlogev : ∀ᶠ x : ℝ in Filter.atTop, (1:ℝ) ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop 1)
  have hev : ∀ᶠ x : ℝ in Filter.atTop,
      Real.sqrt (Real.log x) * (α / 2) ≤ w.recip x := by
    filter_upwards [hAev, hlogev] with x hx1 hx2
    have hpos : (0:ℝ) < Real.sqrt (Real.log x) :=
      Real.sqrt_pos.mpr (by linarith)
    have h := (le_div_iff₀ hpos).mp hx1
    linarith [h]
  exact Filter.tendsto_atTop_mono' _ hev
    (hsqrt.atTop_mul_const (by linarith))

/-- The log-weighted sum over the natural density:
`(Σ_{n ≤ x} w.f n · log n) / (x · A(x)) → 1 / 2`. -/
private lemma logMass_tendsto :
    Filter.Tendsto
      (fun x => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, w.f n * Real.log (n : ℝ))
        / (x * w.recip x))
      Filter.atTop (nhds (1 / 2 : ℝ)) := by
  obtain ⟨α, hαpos, hA⟩ := w.recip_tendsto
  have hAinf := w.recip_atTop α hαpos hA
  have hKpos : (0:ℝ) < Real.log 4 + 4 := by
    have h := Real.log_pos (by norm_num : (1:ℝ) < 4)
    linarith
  have hK1 : (1/2 : ℝ) ≤ Real.log 4 + 4 := by
    have h := Real.log_pos (by norm_num : (1:ℝ) < 4)
    linarith
  have hK : ∀ y : ℝ, 0 ≤ y → |w.psi y - y / 2| ≤ (Real.log 4 + 4) * y := by
    intro y hy
    have h1 : 0 ≤ w.psi y := w.psi_nonneg y
    have h2 : w.psi y ≤ (Real.log 4 + 4) * y := w.psi_le_mul_self hy
    have h3 : (0:ℝ) ≤ y / 2 := by linarith
    have h4 : y / 2 ≤ (Real.log 4 + 4) * y := by
      have hnn := mul_nonneg (sub_nonneg.mpr hK1) hy
      linarith
    rw [abs_le]
    constructor <;> linarith
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hevY : ∀ᶠ y : ℝ in Filter.atTop, dist (w.psi y / y) (1/2) ≤ ε/4 :=
    w.psi_tendsto.eventually
      (Metric.closedBall_mem_nhds (1/2 : ℝ) (show (0:ℝ) < ε/4 by linarith))
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.mp hevY
  set Y : ℝ := max Y₀ 1 with hYdef
  have hY1 : (1:ℝ) ≤ Y := le_max_right _ _
  have hYpos : (0:ℝ) < Y := by linarith
  have hYrel : ∀ y : ℝ, Y ≤ y → |w.psi y - y/2| ≤ (ε/4) * y := by
    intro y hy
    have hy0 : (0:ℝ) < y := lt_of_lt_of_le hYpos hy
    have h := hY₀ y (le_trans (le_max_left _ _) hy)
    rw [Real.dist_eq] at h
    have hyne : y ≠ 0 := ne_of_gt hy0
    have e : w.psi y - y/2 = y * (w.psi y / y - 1/2) := by
      field_simp
    rw [e, abs_mul, abs_of_nonneg hy0.le]
    calc y * |w.psi y / y - 1 / 2| ≤ y * (ε/4) :=
        mul_le_mul_of_nonneg_left h hy0.le
      _ = (ε/4) * y := by ring
  have hBpos : (0:ℝ) < 4 * ((Real.log 4 + 4) * Y) / ε :=
    div_pos (mul_pos (by norm_num) (mul_pos hKpos hYpos)) hε
  have hB : ∀ᶠ x : ℝ in Filter.atTop, 4 * ((Real.log 4 + 4) * Y) / ε ≤ w.recip x :=
    hAinf.eventually (Filter.eventually_ge_atTop _)
  filter_upwards [Filter.eventually_ge_atTop 1, hB] with x hx1 hBA
  have hx0 : (0:ℝ) ≤ x := by linarith
  have hxpos : (0:ℝ) < x := by linarith
  have hApos : (0:ℝ) < w.recip x := lt_of_lt_of_le hBpos hBA
  have hxA : (0:ℝ) < x * w.recip x := mul_pos hxpos hApos
  have hhalf : x / 2 * w.recip x
      = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, w.f m * (x / (2 * (m:ℝ))) := by
    have hrecip : w.recip x = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, w.f m / (m:ℝ) := rfl
    rw [hrecip, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  have hdiff : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, w.f n * Real.log (n:ℝ)) - x/2 * w.recip x
      = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, w.f m * (w.psi (x/(m:ℝ)) - x/(2*(m:ℝ))) := by
    rw [w.logMass_eq, hhalf, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    ring
  have hbig : ∀ m ∈ Finset.Ioc 0 ⌊x⌋₊, Y ≤ x/(m:ℝ) →
      |w.f m * (w.psi (x/(m:ℝ)) - x/(2*(m:ℝ)))| ≤ (ε/4) * (x * (w.f m/(m:ℝ))) := by
    intro m hmI hYm
    have hm1 : 1 ≤ m := (Finset.mem_Ioc.mp hmI).1
    have hmpos : (0:ℝ) < (m:ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hm1
    have h1 := hYrel _ hYm
    have hnn : (0:ℝ) ≤ w.f m := w.nonneg m
    have e : x / (2 * (m:ℝ)) = (x/(m:ℝ)) / 2 := by ring
    rw [abs_mul, abs_of_nonneg hnn]
    calc w.f m * |w.psi (x/(m:ℝ)) - x/(2*(m:ℝ))|
        = w.f m * |w.psi (x/(m:ℝ)) - (x/(m:ℝ))/2| := by rw [e]
      _ ≤ w.f m * ((ε/4) * (x/(m:ℝ))) :=
          mul_le_mul_of_nonneg_left h1 hnn
      _ = (ε/4) * (x * (w.f m/(m:ℝ))) := by ring
  have hsmall : ∀ m ∈ Finset.Ioc 0 ⌊x⌋₊, ¬ Y ≤ x/(m:ℝ) →
      |w.f m * (w.psi (x/(m:ℝ)) - x/(2*(m:ℝ)))| ≤ (Real.log 4 + 4) * Y := by
    intro m hmI hYm
    have hm1 : 1 ≤ m := (Finset.mem_Ioc.mp hmI).1
    have hmpos : (0:ℝ) < (m:ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hm1
    have hlt : x/(m:ℝ) < Y := lt_of_not_ge hYm
    have hxm0 : (0:ℝ) ≤ x/(m:ℝ) := div_nonneg hx0 hmpos.le
    have h1 := hK _ hxm0
    have hle1 : w.f m ≤ 1 := w.le_one m
    have hnn : (0:ℝ) ≤ w.f m := w.nonneg m
    have e : x / (2 * (m:ℝ)) = (x/(m:ℝ)) / 2 := by ring
    rw [← e] at h1
    calc |w.f m * (w.psi (x/(m:ℝ)) - x/(2*(m:ℝ)))|
        = w.f m * |w.psi (x/(m:ℝ)) - x/(2*(m:ℝ))| := by
          rw [abs_mul, abs_of_nonneg hnn]
      _ ≤ 1 * ((Real.log 4 + 4) * (x/(m:ℝ))) :=
          mul_le_mul hle1 h1 (abs_nonneg _) (by norm_num)
      _ = (Real.log 4 + 4) * (x/(m:ℝ)) := one_mul _
      _ ≤ (Real.log 4 + 4) * Y :=
          mul_le_mul_of_nonneg_left hlt.le hKpos.le
  have hbig_sum : ∑ m ∈ (Finset.Ioc 0 ⌊x⌋₊).filter
        (fun (m : ℕ) => Y ≤ x/(m:ℝ)),
        |w.f m * (w.psi (x/(m:ℝ)) - x/(2*(m:ℝ)))|
      ≤ ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (ε/4) * (x * (w.f m/(m:ℝ))) :=
    le_trans
      (Finset.sum_le_sum (fun m hm =>
        hbig m (Finset.mem_of_mem_filter m hm) ((Finset.mem_filter.mp hm).2)))
      (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _)
        (fun m _ _ => mul_nonneg (show (0:ℝ) ≤ ε/4 by linarith)
          (mul_nonneg hx0
            (div_nonneg (w.nonneg m) (Nat.cast_nonneg m)))))
  have hcardx : (((Finset.Ioc 0 ⌊x⌋₊).filter
      (fun (m : ℕ) => ¬ Y ≤ x/(m:ℝ))).card : ℝ) ≤ x := by
    calc (((Finset.Ioc 0 ⌊x⌋₊).filter
        (fun (m : ℕ) => ¬ Y ≤ x/(m:ℝ))).card : ℝ)
        ≤ (((Finset.Ioc 0 ⌊x⌋₊).card : ℕ) : ℝ) := by
            exact_mod_cast Finset.card_filter_le _ _
      _ = (⌊x⌋₊ : ℝ) := by rw [Nat.card_Ioc, Nat.sub_zero]
      _ ≤ x := Nat.floor_le hx0
  have hsmall_sum : ∑ m ∈ (Finset.Ioc 0 ⌊x⌋₊).filter
        (fun (m : ℕ) => ¬ Y ≤ x/(m:ℝ)),
        |w.f m * (w.psi (x/(m:ℝ)) - x/(2*(m:ℝ)))|
      ≤ x * ((Real.log 4 + 4) * Y) :=
    le_trans
      (Finset.sum_le_sum (fun m hm =>
        hsmall m (Finset.mem_of_mem_filter m hm) ((Finset.mem_filter.mp hm).2)))
      (le_trans
        (le_of_eq (by rw [Finset.sum_const, nsmul_eq_mul]))
        (mul_le_mul_of_nonneg_right hcardx
          (mul_nonneg hKpos.le hYpos.le)))
  have hsum_le : |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, w.f n * Real.log (n:ℝ)) - x/2 * w.recip x|
      ≤ (ε/4) * (x * w.recip x) + x * ((Real.log 4 + 4) * Y) := by
    rw [hdiff]
    calc |∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, w.f m * (w.psi (x/(m:ℝ)) - x/(2*(m:ℝ)))|
        ≤ ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊,
            |w.f m * (w.psi (x/(m:ℝ)) - x/(2*(m:ℝ)))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = (∑ m ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun (m : ℕ) => Y ≤ x/(m:ℝ)),
              |w.f m * (w.psi (x/(m:ℝ)) - x/(2*(m:ℝ)))|)
          + (∑ m ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun (m : ℕ) => ¬ Y ≤ x/(m:ℝ)),
              |w.f m * (w.psi (x/(m:ℝ)) - x/(2*(m:ℝ)))|) :=
          (Finset.sum_filter_add_sum_filter_not _ _ _).symm
      _ ≤ (∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (ε/4) * (x * (w.f m/(m:ℝ))))
          + x * ((Real.log 4 + 4) * Y) :=
          _root_.add_le_add hbig_sum hsmall_sum
      _ = (ε/4) * (x * w.recip x) + x * ((Real.log 4 + 4) * Y) := by
          congr 1
          calc ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (ε/4) * (x * (w.f m/(m:ℝ)))
              = (ε/4) * x * ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (w.f m/(m:ℝ)) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro m _
                ring
            _ = (ε/4) * (x * w.recip x) := by
                have hrecip : w.recip x = ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, w.f m/(m:ℝ) := rfl
                rw [hrecip]
                ring
  have e : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, w.f n * Real.log (n:ℝ)) / (x * w.recip x) - 1/2
      = ((∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, w.f n * Real.log (n:ℝ)) - x/2 * w.recip x)
        / (x * w.recip x) := by
    have hxAne : x * w.recip x ≠ 0 := ne_of_gt hxA
    field_simp
  have hBY : (Real.log 4 + 4) * Y / w.recip x ≤ ε/4 := by
    rw [div_le_iff₀ hApos]
    have h2 : 4 * ((Real.log 4 + 4) * Y) ≤ w.recip x * ε := by
      rwa [div_le_iff₀ hε] at hBA
    linarith [h2]
  have hfin : |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, w.f n * Real.log (n:ℝ)) / (x * w.recip x)
      - 1/2| ≤ ε/2 := by
    rw [e, abs_div, abs_of_nonneg hxA.le, div_le_iff₀ hxA]
    have h1 : x * ((Real.log 4 + 4) * Y) ≤ (ε/4) * (x * w.recip x) := by
      have e2 : x * ((Real.log 4 + 4) * Y)
          = (x * w.recip x) * ((Real.log 4 + 4) * Y / w.recip x) := by
        have hAne : w.recip x ≠ 0 := ne_of_gt hApos
        field_simp
      rw [e2]
      calc (x * w.recip x) * ((Real.log 4 + 4) * Y / w.recip x)
          ≤ (x * w.recip x) * (ε/4) :=
            mul_le_mul_of_nonneg_left hBY hxA.le
        _ = (ε/4) * (x * w.recip x) := by ring
    linarith [hsum_le, h1]
  change dist ((∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, w.f n * Real.log (n:ℝ)) / (x * w.recip x))
    (1/2 : ℝ) < ε
  rw [Real.dist_eq]
  linarith [hfin, hε]

/-- For `x ≥ 1`: `∑_{n ≤ x} log (x / n) ≤ x`, via `N!`. -/
private lemma log_sum_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Real.log (x / (n:ℝ)) ≤ x := by
  set N : ℕ := ⌊x⌋₊ with hNdef
  have hN1 : 1 ≤ N := (Nat.one_le_floor_iff x).mpr hx
  have hNpos : (0:ℝ) < (N:ℝ) := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one hN1
  have hNnn : (0:ℝ) ≤ (N:ℝ) := le_of_lt hNpos
  have hxpos : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hIoc : Finset.Ioc 0 N = Finset.Ico 1 (N+1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  have hlogne : ∀ i ∈ Finset.Ico 1 (N+1), ((i : ℕ):ℝ) ≠ 0 := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
    exact_mod_cast ne_of_gt (lt_of_lt_of_le zero_lt_one hi1)
  have hlogfact : ∑ n ∈ Finset.Ico 1 (N+1), Real.log ((n:ℕ):ℝ)
      = Real.log (((Nat.factorial N : ℕ)):ℝ) := by
    have hprod : (∏ i ∈ Finset.Ico 1 (N+1), ((i:ℕ):ℝ)) = (((Nat.factorial N : ℕ)):ℝ) := by
      rw [← Nat.cast_prod]
      exact_mod_cast Finset.prod_Ico_id_eq_factorial N
    rw [← hprod]
    exact (Real.log_prod hlogne).symm
  have hS : ∑ n ∈ Finset.Ioc 0 N, Real.log (x/(n:ℝ))
      = (N:ℝ) * Real.log x - Real.log (((Nat.factorial N : ℕ)):ℝ) := by
    rw [hIoc]
    calc ∑ n ∈ Finset.Ico 1 (N+1), Real.log (x/((n:ℕ):ℝ))
        = ∑ n ∈ Finset.Ico 1 (N+1),
            (Real.log x - Real.log ((n:ℕ):ℝ)) :=
          Finset.sum_congr rfl (fun i hi =>
            Real.log_div (ne_of_gt hxpos) (hlogne i hi))
      _ = (Finset.Ico 1 (N+1)).card • Real.log x
          - ∑ n ∈ Finset.Ico 1 (N+1), Real.log ((n:ℕ):ℝ) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const]
      _ = (N:ℝ) * Real.log x - Real.log (((Nat.factorial N : ℕ)):ℝ) := by
          have hcard : (Finset.Ico 1 (N+1)).card = N := by simp [Nat.card_Ico]
          rw [hlogfact, hcard, nsmul_eq_mul]
  have hfact : (N:ℝ) * Real.log (N:ℝ) - Real.log (((Nat.factorial N : ℕ)):ℝ) ≤ (N:ℝ) := by
    have hexp : HasSum (fun n : ℕ => (N:ℝ)^n / (((Nat.factorial n : ℕ)):ℝ))
        (Real.exp (N:ℝ)) := by
      have h : HasSum (fun n : ℕ => (N:ℝ)^n / (((Nat.factorial n : ℕ)):ℝ))
          (NormedSpace.exp (N:ℝ)) :=
        NormedSpace.expSeries_div_hasSum_exp _
      rwa [← Real.exp_eq_exp_ℝ] at h
    have hfact_le : (N:ℝ)^N / (((Nat.factorial N : ℕ)):ℝ) ≤ Real.exp (N:ℝ) := by
      have hle := hexp.summable.sum_le_tsum {N} (fun i _ =>
        div_nonneg (pow_nonneg hNnn _) (Nat.cast_nonneg _))
      rw [Finset.sum_singleton, hexp.tsum_eq] at hle
      exact hle
    have hpos1 : (0:ℝ) < (N:ℝ)^N / (((Nat.factorial N : ℕ)):ℝ) :=
      div_pos (pow_pos hNpos _)
        (Nat.cast_pos.mpr (Nat.factorial_pos _))
    have h2 := Real.log_le_log hpos1 hfact_le
    rw [Real.log_exp] at h2
    have e : Real.log ((N:ℝ)^N / (((Nat.factorial N : ℕ)):ℝ))
        = (N:ℝ) * Real.log (N:ℝ) - Real.log (((Nat.factorial N : ℕ)):ℝ) := by
      rw [Real.log_div (ne_of_gt (pow_pos hNpos _))
        (ne_of_gt (Nat.cast_pos.mpr (Nat.factorial_pos _))), Real.log_pow]
    rwa [e] at h2
  have hxd : (N:ℝ) * Real.log (x/(N:ℝ)) ≤ x - (N:ℝ) := by
    have h1 : Real.log (x/(N:ℝ)) ≤ x/(N:ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hxpos hNpos)
    have hNne : (N:ℝ) ≠ 0 := ne_of_gt hNpos
    have h2 := mul_le_mul_of_nonneg_left h1 hNnn
    have e : (N:ℝ) * (x/(N:ℝ) - 1) = x - (N:ℝ) := by
      rw [mul_sub, mul_one]
      congr 1
      rw [mul_comm]
      exact div_mul_cancel₀ _ hNne
    rwa [e] at h2
  have hsplit : (N:ℝ) * Real.log x
      = (N:ℝ) * Real.log (x/(N:ℝ)) + (N:ℝ) * Real.log (N:ℝ) := by
    have e : Real.log (x/(N:ℝ)) = Real.log x - Real.log (N:ℝ) :=
      Real.log_div (ne_of_gt hxpos) (ne_of_gt hNpos)
    rw [e]
    ring
  linarith [hS, hfact, hxd, hsplit]

/-- Natural density: `N(x) · √(log x) / x → α / 2`. -/
private lemma count_tendsto (α : ℝ)
    (hA : Filter.Tendsto (fun x => w.recip x / Real.sqrt (Real.log x))
      Filter.atTop (nhds α)) :
    Filter.Tendsto (fun x => w.mass x * Real.sqrt (Real.log x) / x)
      Filter.atTop (nhds (α / 2)) := by
  obtain ⟨α', hα'pos, hA'⟩ := w.recip_tendsto
  have hAinf := w.recip_atTop α' hα'pos hA'
  -- The `J₂` sum and its bounds.
  have hJ2eq : ∀ x : ℝ, 1 ≤ x →
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, w.f n * Real.log (x/(n:ℝ)))
      = w.mass x * Real.log x
        - (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, w.f n * Real.log (n:ℝ)) := by
    intro x hx
    have hxpos : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx
    have hmass : w.mass x = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, w.f n := rfl
    rw [hmass, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Ioc.mp hn).1
    have hnpos : (0:ℝ) < (n:ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hn1
    rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt hnpos)]
    ring
  have hJ2nn : ∀ᶠ x : ℝ in Filter.atTop,
      0 ≤ (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, w.f n * Real.log (x/(n:ℝ)))
        / (x * w.recip x) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with x hx
    have hxpos : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx
    have hApos : (0:ℝ) < w.recip x :=
      lt_of_lt_of_le (by norm_num) (w.recip_ge_one hx)
    apply div_nonneg _ (mul_nonneg hxpos.le hApos.le)
    apply Finset.sum_nonneg
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Ioc.mp hn).1
    have hnpos : (0:ℝ) < (n:ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hn1
    have hnx : (n:ℝ) ≤ x := by
      have h1 : n ≤ ⌊x⌋₊ := (Finset.mem_Ioc.mp hn).2
      exact le_trans (by exact_mod_cast h1) (Nat.floor_le (by linarith))
    have hlog : 0 ≤ Real.log (x/(n:ℝ)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hnpos]
      simpa using hnx
    exact mul_nonneg (w.nonneg n) hlog
  have hJ2le : ∀ᶠ x : ℝ in Filter.atTop,
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, w.f n * Real.log (x/(n:ℝ)))
        / (x * w.recip x) ≤ 1 / w.recip x := by
    filter_upwards [Filter.eventually_ge_atTop 1] with x hx
    have hxpos : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx
    have hApos : (0:ℝ) < w.recip x :=
      lt_of_lt_of_le (by norm_num) (w.recip_ge_one hx)
    have hxA : (0:ℝ) < x * w.recip x := mul_pos hxpos hApos
    have hJle : (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, w.f n * Real.log (x/(n:ℝ))) ≤ x := by
      calc ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, w.f n * Real.log (x/(n:ℝ))
          ≤ ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Real.log (x/(n:ℝ)) := by
            apply Finset.sum_le_sum
            intro n hn
            have hn1 : 1 ≤ n := (Finset.mem_Ioc.mp hn).1
            have hnpos : (0:ℝ) < (n:ℝ) := by
              exact_mod_cast lt_of_lt_of_le zero_lt_one hn1
            have hnx : (n:ℝ) ≤ x := by
              have h1 : n ≤ ⌊x⌋₊ := (Finset.mem_Ioc.mp hn).2
              exact le_trans (by exact_mod_cast h1)
                (Nat.floor_le (by linarith))
            have hlog : 0 ≤ Real.log (x/(n:ℝ)) := by
              apply Real.log_nonneg
              rw [le_div_iff₀ hnpos]
              simpa using hnx
            calc w.f n * Real.log (x/(n:ℝ))
                ≤ 1 * Real.log (x/(n:ℝ)) :=
                  mul_le_mul_of_nonneg_right (w.le_one n) hlog
              _ = Real.log (x/(n:ℝ)) := one_mul _
        _ ≤ x := log_sum_le hx
    calc (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, w.f n * Real.log (x/(n:ℝ))) / (x * w.recip x)
        ≤ x / (x * w.recip x) :=
          div_le_div_of_nonneg_right hJle hxA.le
      _ = 1 / w.recip x := by
          have hxne : x ≠ 0 := ne_of_gt hxpos
          have hAne : w.recip x ≠ 0 := ne_of_gt hApos
          field_simp
  have h1A : Filter.Tendsto (fun x => 1 / w.recip x) Filter.atTop (nhds 0) := by
    have h := tendsto_inv_atTop_zero.comp hAinf
    refine h.congr' ?_
    filter_upwards with x
    exact (one_div _).symm
  have hJ2 : Filter.Tendsto
      (fun x => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, w.f n * Real.log (x/(n:ℝ)))
        / (x * w.recip x))
      Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1A
      hJ2nn hJ2le
  have hHlog : Filter.Tendsto
      (fun x => w.mass x * Real.log x / (x * w.recip x))
      Filter.atTop (nhds (1 / 2)) := by
    have heq : (fun x => w.mass x * Real.log x / (x * w.recip x)) =ᶠ[Filter.atTop]
        (fun x => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, w.f n * Real.log (x/(n:ℝ)))
          / (x * w.recip x)
          + (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, w.f n * Real.log (n:ℝ)) / (x * w.recip x)) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with x hx
      rw [hJ2eq x hx]
      ring
    have hsum := hJ2.add w.logMass_tendsto
    rw [show (0:ℝ) + 1/2 = 1/2 by ring] at hsum
    have hsum' : Filter.Tendsto
        (fun x => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, w.f n * Real.log (x/(n:ℝ)))
          / (x * w.recip x)
          + (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, w.f n * Real.log (n:ℝ)) / (x * w.recip x))
        Filter.atTop (nhds (1/2)) := hsum
    exact hsum'.congr' heq.symm
  have heq2 : (fun x => (w.mass x * Real.log x / (x * w.recip x))
        * (w.recip x / Real.sqrt (Real.log x)))
      =ᶠ[Filter.atTop]
      (fun x => w.mass x * Real.sqrt (Real.log x) / x) := by
    filter_upwards [Filter.eventually_gt_atTop 1] with x hx
    have hlog : 0 < Real.log x := Real.log_pos hx
    have hsq : Real.sqrt (Real.log x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hlog)
    have hApos : (0:ℝ) < w.recip x :=
      lt_of_lt_of_le (by norm_num) (w.recip_ge_one (le_of_lt hx))
    have hxne : x ≠ 0 := ne_of_gt (by linarith)
    have hAne : w.recip x ≠ 0 := ne_of_gt hApos
    have hdiv : Real.log x / Real.sqrt (Real.log x)
        = Real.sqrt (Real.log x) := by
      rw [div_eq_iff hsq, Real.mul_self_sqrt hlog.le]
    calc (w.mass x * Real.log x / (x * w.recip x))
            * (w.recip x / Real.sqrt (Real.log x))
        = (w.mass x / x) * (Real.log x / Real.sqrt (Real.log x)) := by
          field_simp
      _ = (w.mass x / x) * Real.sqrt (Real.log x) := by rw [hdiv]
      _ = w.mass x * Real.sqrt (Real.log x) / x := by ring
  have hprod := hHlog.mul hA
  have eα : (1/2 : ℝ) * α = α / 2 := by ring
  rw [eα] at hprod
  have hprod' : Filter.Tendsto
      (fun x => (w.mass x * Real.log x / (x * w.recip x))
        * (w.recip x / Real.sqrt (Real.log x)))
      Filter.atTop (nhds (α/2)) := hprod
  exact hprod'.congr' heq2

end Weight

end exists_tendsto_sum_of_prime_mod_four

open exists_tendsto_sum_of_prime_mod_four

/-- **Mean values for weights selecting one odd prime class modulo four.** Suppose that
$f : \mathbb{N} \to [0,1]$ is completely multiplicative with $f(0)=0$ and $f(1)=1$. Suppose
that on odd primes $f$ equals the indicator of one unit residue class modulo four.
There is an $α > 0$ such that
$\sum_{n \le x} f(n)/n$ is asymptotic to $α\sqrt{\log x}$ and
$\sum_{n \le x} f(n)$ is asymptotic to $(α/2)x/\sqrt{\log x}$.
Both sums start at $n = 1$.

Source: Eduard Wirsing, “Das asymptotische Verhalten von Summen über multiplikative Funktionen”,
*Math. Ann.* **143** (1961), 75–102. For the mean-value formula specialized here to
$τ = 1/2$, see also Pieter Moree, *Chebyshev's bias for composite numbers with restricted
prime divisors*, Theorem 1 ([arXiv:math/0112100](https://arxiv.org/abs/math/0112100)). -/
public theorem exists_tendsto_sum_of_prime_mod_four (f : ℕ →*₀ ℝ)
    (h₀ : ∀ n, 0 ≤ f n) (h₁ : ∀ n, f n ≤ 1) (a : ZMod 4) (ha : IsUnit a)
    (hp : ∀ p : ℕ, p.Prime → p ≠ 2 → f p = if (p : ZMod 4) = a then 1 else 0) :
    ∃ α : ℝ, 0 < α ∧
      Tendsto (fun x : ℝ => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, f n / (n : ℝ)) / √(Real.log x))
        atTop (𝓝 α) ∧
      Tendsto (fun x : ℝ => (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, f n) * √(Real.log x) / x)
        atTop (𝓝 (α / 2)) := by
  let w : Weight := ⟨f, h₀, h₁, a, ha, hp⟩
  obtain ⟨α, hα, hA⟩ := w.recip_tendsto
  exact ⟨α, hα, hA, w.count_tendsto α hA⟩

end MetaMathlibExt
