/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PrimeCounting.ResidueClass
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Harmonic.Bounds
import MathlibExt.NumberTheory.PrimeCounting.BrunTitchmarsh
import MathlibExt.NumberTheory.ArithmeticFunction.MoebiusSummatory

/-!
# The average of `(p - 1) / φ(p - 1)` over primes

Sums over primes `p ≤ x` of a divisor sum over `p - 1` become sums over moduli `δ` weighted by
the number `π(x; δ, 1)` of primes `p ≡ 1 (mod δ)`. Combined with `n / φ(n) ≤ ∑_{δ ∣ n} 1/φ(δ)`,
the Brun–Titchmarsh inequality for small `δ` and the trivial bound for large `δ` show that
`(p - 1) / φ(p - 1)` is bounded on average over primes.

## Main statements

* `Nat.sum_primesLE_sum_divisors_sub_one_eq`:
  `∑_{p ≤ N} ∑_{δ ∣ p - 1} f(δ) = ∑_{δ ≤ N} π(N; δ, 1) f(δ)`.
* `Nat.primeCountingMod_one_le_div`: the trivial bound `π(N; δ, 1) ≤ N / δ`.
* `Nat.sum_primesLE_sub_one_div_totient_isBigO`: `∑_{p ≤ x} (p - 1)/φ(p - 1) = O(x / log x)`.
-/

@[expose] public section

open Finset

namespace Nat

/-- `∑_{p ≤ N} ∑_{δ ∣ p - 1} f(δ) = ∑_{δ ≤ N} π(N; δ, 1) f(δ)`. -/
theorem sum_primesLE_sum_divisors_sub_one_eq {R : Type*} [NonAssocSemiring R] (N : ℕ)
    (f : ℕ → R) :
    ∑ p ∈ primesLE N, ∑ δ ∈ (p - 1).divisors, f δ =
      ∑ δ ∈ Icc 1 N, (primeCountingMod N δ 1 : R) * f δ := by
  have hdiv : ∀ p ∈ primesLE N, (p - 1).divisors = (Icc 1 N).filter (· ∣ p - 1) := by
    intro p hp
    have h2 := (mem_primesLE.mp hp).2.two_le
    have hpN := (mem_primesLE.mp hp).1
    ext δ
    rw [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hd, hne⟩
      have := Nat.pos_of_dvd_of_pos hd (by omega)
      have := Nat.le_of_dvd (by omega) hd
      exact ⟨⟨by omega, by omega⟩, hd⟩
    · rintro ⟨-, hd⟩
      exact ⟨hd, by omega⟩
  rw [Finset.sum_congr rfl fun p hp => by rw [hdiv p hp]]
  rw [Finset.sum_comm' (t' := Icc 1 N)
    (s' := fun δ => (primesLE N).filter (fun p => δ ∣ p - 1))]
  · refine Finset.sum_congr rfl fun δ _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul, primeCountingMod]
    congr 2
    exact congrArg Finset.card (Finset.filter_congr fun p hp =>
      (Nat.ModEq.comm.trans (Nat.modEq_iff_dvd' (mem_primesLE.mp hp).2.one_lt.le)).symm)
  · intro p δ
    simp only [Finset.mem_filter]
    tauto

/-- The trivial bound `π(N; δ, 1) ≤ N / δ`: `p ↦ p - 1` maps the primes `p ≡ 1 (mod δ)` into
the multiples of `δ` in `[1, N]`. -/
theorem primeCountingMod_one_le_div (N δ : ℕ) : primeCountingMod N δ 1 ≤ N / δ := by
  unfold primeCountingMod
  rw [← Nat.Ioc_filter_dvd_card_eq_div]
  refine Finset.card_le_card_of_injOn (fun p => p - 1) ?_ ?_
  · intro p hp
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp
    have hp' := mem_primesLE.mp hp.1
    have h2 := hp'.2.two_le
    have h3 := (Nat.modEq_iff_dvd' hp'.2.one_lt.le).1 hp.2.symm
    simp only [Finset.coe_filter, Finset.mem_Ioc, Set.mem_ofPred_eq]
    exact ⟨⟨by omega, by omega⟩, h3⟩
  · intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha hb
    have := (mem_primesLE.mp ha.1).2.two_le
    have := (mem_primesLE.mp hb.1).2.two_le
    simp only at hab
    omega

/-- `n / φ(n) ≤ ∑_{δ ∣ n} 1/φ(δ)` for `n > 0`, from `n = ∑_{δ ∣ n} φ(n/δ)` and
`φ(δ) φ(n/δ) ≤ φ(n)`. -/
private theorem div_totient_le_sum_divisors (n : ℕ) (hn : 0 < n) :
    (n : ℝ) / n.totient ≤ ∑ δ ∈ n.divisors, 1 / (δ.totient : ℝ) := by
  have hφpos : ∀ m : ℕ, 0 < m → (0 : ℝ) < (m.totient : ℝ) := fun m hm => by
    exact_mod_cast Nat.totient_pos.mpr hm
  have h1 : (n : ℝ) = ∑ δ ∈ n.divisors, ((n / δ).totient : ℝ) := by
    have := Nat.sum_div_divisors n Nat.totient
    rw [Nat.sum_totient] at this
    exact_mod_cast this.symm
  rw [h1, Finset.sum_div]
  refine Finset.sum_le_sum fun δ hδ => ?_
  have hδn := Nat.dvd_of_mem_divisors hδ
  have hδ0 := Nat.pos_of_mem_divisors hδ
  have hsm : ((δ.totient : ℝ)) * ((n / δ).totient : ℝ) ≤ n.totient := by
    have := Nat.totient_super_multiplicative δ (n / δ)
    rw [Nat.mul_div_cancel' hδn] at this
    exact_mod_cast this
  rw [div_le_div_iff₀ (hφpos n hn) (hφpos δ hδ0)]
  linarith

/-- `∑_{p ≤ x} (p - 1) / φ(p - 1) = O(x / log x)`: on average over primes, `(p - 1)/φ(p - 1)`
is bounded. -/
theorem sum_primesLE_sub_one_div_totient_isBigO :
    (fun x : ℝ => ∑ p ∈ primesLE ⌊x⌋₊, ((p - 1 : ℕ) : ℝ) / ((p - 1).totient : ℝ)) =O[Filter.atTop]
      (fun x : ℝ => x / Real.log x) := by
  classical
  have hφpos : ∀ n : ℕ, 0 < n → (0 : ℝ) < (n.totient : ℝ) := fun n hn => by
    exact_mod_cast Nat.totient_pos.mpr hn
  have hφone : ∀ n : ℕ, 0 < n → (1 : ℝ) ≤ (n.totient : ℝ) := fun n hn => by
    exact_mod_cast Nat.totient_pos.mpr hn
  -- pair interchange
  have hP : ∀ (F : ℕ → ℕ → ℝ), (∀ a b, 0 ≤ F a b) → ∀ N : ℕ,
      ∑ d ∈ Icc 1 N, ∑ e ∈ d.divisors, F e (d / e) ≤ ∑ e ∈ Icc 1 N, ∑ m ∈ Icc 1 N, F e m := by
    intro F hF N
    rw [← sum_Icc_sum_Icc_div_eq_sum_Icc_sum_divisors]
    exact Finset.sum_le_sum fun e _ => Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc_right (Nat.div_le_self N e)) fun _ _ _ => hF _ _
  -- `∑_{n ≤ N} 1/n² ≤ 2`
  have hsq : ∀ N : ℕ, ∑ n ∈ Icc 1 N, 1 / (n : ℝ) ^ 2 ≤ 2 := by
    have key : ∀ N : ℕ, ∑ n ∈ Icc 1 N, 1 / (n : ℝ) ^ 2 ≤ 2 - 2 / ((N : ℝ) + 1) := by
      intro N
      induction N with
      | zero => norm_num
      | succ N ih =>
        rw [Finset.sum_Icc_succ_top (by omega)]
        have h : 1 / ((N + 1 : ℕ) : ℝ) ^ 2 ≤ 2 / ((N : ℝ) + 1) - 2 / (((N + 1 : ℕ) : ℝ) + 1) := by
          push_cast
          rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
            (by positivity)]
          nlinarith [sq_nonneg ((N : ℝ) + 1)]
        linarith
    intro N
    have := key N
    have : 0 ≤ 2 / ((N : ℝ) + 1) := by positivity
    linarith
  -- harmonic bound
  have hharm : ∀ N : ℕ, ∑ m ∈ Icc 1 N, 1 / (m : ℝ) ≤ 1 + Real.log N := by
    intro N
    have h := harmonic_le_one_add_log N
    rw [harmonic_eq_sum_Icc] at h
    push_cast at h
    simpa [one_div] using h
  -- `∑_{d ≤ N} 1/(d φ(d)) ≤ 4`
  have hA : ∀ N : ℕ, ∑ d ∈ Icc 1 N, 1 / ((d : ℝ) * d.totient) ≤ 4 := by
    intro N
    calc ∑ d ∈ Icc 1 N, 1 / ((d : ℝ) * d.totient)
        ≤ ∑ d ∈ Icc 1 N, ∑ e ∈ d.divisors,
            (1 / (e : ℝ) ^ 2) * (1 / ((d / e : ℕ) : ℝ) ^ 2) := by
          refine Finset.sum_le_sum fun d hd => ?_
          have hd0 : 0 < d := by simp at hd; omega
          have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
          have hφd := hφpos d hd0
          calc 1 / ((d : ℝ) * d.totient) = (d : ℝ) / d.totient * (1 / (d : ℝ) ^ 2) := by
                field_simp
            _ ≤ (∑ δ ∈ d.divisors, 1 / (δ.totient : ℝ)) * (1 / (d : ℝ) ^ 2) :=
                mul_le_mul_of_nonneg_right (div_totient_le_sum_divisors d hd0) (by positivity)
            _ = ∑ e ∈ d.divisors, 1 / (e.totient : ℝ) * (1 / (d : ℝ) ^ 2) := Finset.sum_mul _ _ _
            _ ≤ _ := by
                refine Finset.sum_le_sum fun e he => ?_
                have hed := Nat.dvd_of_mem_divisors he
                have he0 := Nat.pos_of_mem_divisors he
                have hde : (e : ℝ) * ((d / e : ℕ) : ℝ) = d := by
                  exact_mod_cast Nat.mul_div_cancel' hed
                have hm0 : 0 < d / e := Nat.div_pos (Nat.le_of_dvd hd0 hed) he0
                have heR : (0 : ℝ) < e := by exact_mod_cast he0
                have hmR : (0 : ℝ) < ((d / e : ℕ) : ℝ) := by exact_mod_cast hm0
                have h1 : (1 / (e : ℝ) ^ 2) * (1 / ((d / e : ℕ) : ℝ) ^ 2) = 1 / (d : ℝ) ^ 2 := by
                  rw [← hde]; field_simp
                rw [h1]
                have h2 := hφone e he0
                have h3 : 1 / (e.totient : ℝ) ≤ 1 := by
                  rw [div_le_one (by linarith)]; exact h2
                have h4 : (0 : ℝ) ≤ 1 / (d : ℝ) ^ 2 := by positivity
                nlinarith
      _ ≤ ∑ e ∈ Icc 1 N, ∑ m ∈ Icc 1 N, (1 / (e : ℝ) ^ 2) * (1 / (m : ℝ) ^ 2) :=
          hP (fun a b => (1 / (a : ℝ) ^ 2) * (1 / (b : ℝ) ^ 2)) (fun a b => by positivity) N
      _ = (∑ e ∈ Icc 1 N, 1 / (e : ℝ) ^ 2) * ∑ m ∈ Icc 1 N, 1 / (m : ℝ) ^ 2 :=
          (Finset.sum_mul_sum _ _ _ _).symm
      _ ≤ 2 * 2 := mul_le_mul (hsq N) (hsq N) (Finset.sum_nonneg fun _ _ => by positivity)
          (by norm_num)
      _ = 4 := by norm_num
  -- `∑_{δ ≤ N} 1/φ(δ)² ≤ 16`
  have hB : ∀ N : ℕ, ∑ δ ∈ Icc 1 N, 1 / (δ.totient : ℝ) ^ 2 ≤ 16 := by
    intro N
    calc ∑ δ ∈ Icc 1 N, 1 / (δ.totient : ℝ) ^ 2
        ≤ ∑ d ∈ Icc 1 N, ∑ e ∈ d.divisors,
            (1 / ((e : ℝ) * e.totient)) * (1 / (((d / e : ℕ) : ℝ) * (d / e).totient)) := by
          refine Finset.sum_le_sum fun d hd => ?_
          have hd0 : 0 < d := by simp at hd; omega
          have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
          have hφd := hφpos d hd0
          calc 1 / (d.totient : ℝ) ^ 2 = (d : ℝ) / d.totient * (1 / ((d : ℝ) * d.totient)) := by
                field_simp
            _ ≤ (∑ δ ∈ d.divisors, 1 / (δ.totient : ℝ)) * (1 / ((d : ℝ) * d.totient)) :=
                mul_le_mul_of_nonneg_right (div_totient_le_sum_divisors d hd0) (by positivity)
            _ = ∑ e ∈ d.divisors, 1 / (e.totient : ℝ) * (1 / ((d : ℝ) * d.totient)) :=
                Finset.sum_mul _ _ _
            _ ≤ _ := by
                refine Finset.sum_le_sum fun e he => ?_
                have hed := Nat.dvd_of_mem_divisors he
                have he0 := Nat.pos_of_mem_divisors he
                have hde : (e : ℝ) * ((d / e : ℕ) : ℝ) = d := by
                  exact_mod_cast Nat.mul_div_cancel' hed
                have hm0 : 0 < d / e := Nat.div_pos (Nat.le_of_dvd hd0 hed) he0
                have heR : (0 : ℝ) < e := by exact_mod_cast he0
                have hmR : (0 : ℝ) < ((d / e : ℕ) : ℝ) := by exact_mod_cast hm0
                have hφe := hφone e he0
                have hφm := hφpos (d / e) hm0
                have hsm : (e.totient : ℝ) * ((d / e).totient : ℝ) ≤ d.totient := by
                  have := Nat.totient_super_multiplicative e (d / e)
                  rw [Nat.mul_div_cancel' hed] at this
                  exact_mod_cast this
                rw [_root_.div_mul_div_comm, _root_.div_mul_div_comm, one_mul]
                apply one_div_le_one_div_of_le (by positivity)
                calc (e : ℝ) * e.totient * (((d / e : ℕ) : ℝ) * (d / e).totient)
                    = ((e : ℝ) * ((d / e : ℕ) : ℝ)) *
                        ((e.totient : ℝ) * ((d / e).totient : ℝ)) := by
                      ring
                  _ ≤ (d : ℝ) * d.totient := by
                      rw [hde]; exact mul_le_mul_of_nonneg_left hsm hdR.le
                  _ ≤ (e.totient : ℝ) * ((d : ℝ) * d.totient) := by
                      nlinarith [mul_pos hdR hφd]
      _ ≤ ∑ e ∈ Icc 1 N, ∑ m ∈ Icc 1 N,
            (1 / ((e : ℝ) * e.totient)) * (1 / ((m : ℝ) * m.totient)) :=
          hP (fun a b => (1 / ((a : ℝ) * a.totient)) * (1 / ((b : ℝ) * b.totient)))
            (fun a b => by positivity) N
      _ = (∑ e ∈ Icc 1 N, 1 / ((e : ℝ) * e.totient)) *
            ∑ m ∈ Icc 1 N, 1 / ((m : ℝ) * m.totient) :=
          (Finset.sum_mul_sum _ _ _ _).symm
      _ ≤ 4 * 4 := mul_le_mul (hA N) (hA N) (Finset.sum_nonneg fun _ _ => by positivity)
          (by norm_num)
      _ = 16 := by norm_num
  -- `∑_{δ ≤ N} 1/φ(δ) ≤ 4 (1 + log N)`
  have hC : ∀ N : ℕ, ∑ δ ∈ Icc 1 N, 1 / (δ.totient : ℝ) ≤ 4 * (1 + Real.log N) := by
    intro N
    calc ∑ δ ∈ Icc 1 N, 1 / (δ.totient : ℝ)
        ≤ ∑ d ∈ Icc 1 N, ∑ e ∈ d.divisors,
            (1 / ((e : ℝ) * e.totient)) * (1 / ((d / e : ℕ) : ℝ)) := by
          refine Finset.sum_le_sum fun d hd => ?_
          have hd0 : 0 < d := by simp at hd; omega
          have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
          have hφd := hφpos d hd0
          calc 1 / (d.totient : ℝ) = (d : ℝ) / d.totient * (1 / (d : ℝ)) := by
                field_simp
            _ ≤ (∑ δ ∈ d.divisors, 1 / (δ.totient : ℝ)) * (1 / (d : ℝ)) :=
                mul_le_mul_of_nonneg_right (div_totient_le_sum_divisors d hd0) (by positivity)
            _ = ∑ e ∈ d.divisors, 1 / (e.totient : ℝ) * (1 / (d : ℝ)) :=
                Finset.sum_mul _ _ _
            _ = _ := by
                refine Finset.sum_congr rfl fun e he => ?_
                have hed := Nat.dvd_of_mem_divisors he
                have he0 := Nat.pos_of_mem_divisors he
                have hde : (e : ℝ) * ((d / e : ℕ) : ℝ) = d := by
                  exact_mod_cast Nat.mul_div_cancel' hed
                have hm0 : 0 < d / e := Nat.div_pos (Nat.le_of_dvd hd0 hed) he0
                have heR : (0 : ℝ) < e := by exact_mod_cast he0
                have hmR : (0 : ℝ) < ((d / e : ℕ) : ℝ) := by exact_mod_cast hm0
                have hφe := hφpos e he0
                rw [← hde]
                field_simp
      _ ≤ ∑ e ∈ Icc 1 N, ∑ m ∈ Icc 1 N, (1 / ((e : ℝ) * e.totient)) * (1 / (m : ℝ)) :=
          hP (fun a b => (1 / ((a : ℝ) * a.totient)) * (1 / (b : ℝ)))
            (fun a b => by positivity) N
      _ = (∑ e ∈ Icc 1 N, 1 / ((e : ℝ) * e.totient)) * ∑ m ∈ Icc 1 N, 1 / (m : ℝ) :=
          (Finset.sum_mul_sum _ _ _ _).symm
      _ ≤ 4 * (1 + Real.log N) := mul_le_mul (hA N) (hharm N)
          (Finset.sum_nonneg fun _ _ => by positivity) (by norm_num)
  refine Asymptotics.IsBigO.of_bound 256 ?_
  filter_upwards [Filter.eventually_ge_atTop (16 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hlog16 : Real.log 16 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlog2 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have hlog1 : 1 ≤ Real.log x := by
    have := Real.log_two_gt_d9
    linarith
  have hlogpos : 0 < Real.log x := by linarith
  have hsx : 0 < √x := Real.sqrt_pos.mpr hx0
  have hsxx : √x * √x = x := Real.mul_self_sqrt hx0.le
  have hs4 : 4 ≤ √x := by
    rw [show (4 : ℝ) = √16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌊x⌋₊ := ⟨_, rfl⟩
  have hNx : (N : ℝ) ≤ x := by rw [hN]; exact Nat.floor_le hx0.le
  have hxN : x < N + 1 := by rw [hN]; exact Nat.lt_floor_add_one x
  have hN1 : 1 ≤ N := by rw [hN]; exact Nat.le_floor (by norm_num; linarith)
  have hNhalf : x / 2 ≤ N := by linarith
  have hS : ∑ p ∈ primesLE ⌊x⌋₊, ((p - 1 : ℕ) : ℝ) / ((p - 1).totient : ℝ)
      ≤ ∑ δ ∈ Icc 1 N, (primeCountingMod N δ 1 : ℝ) * (1 / (δ.totient : ℝ)) := by
    rw [← hN, ← sum_primesLE_sum_divisors_sub_one_eq]
    refine Finset.sum_le_sum fun p hp => ?_
    have := (mem_primesLE.mp hp).2.two_le
    exact div_totient_le_sum_divisors (p - 1) (by omega)
  have hterm : ∀ δ ∈ Icc 1 N, (primeCountingMod N δ 1 : ℝ) * (1 / (δ.totient : ℝ)) ≤
      8 * x / Real.log x * (1 / (δ.totient : ℝ) ^ 2) + √x * (1 / (δ.totient : ℝ)) := by
    intro δ hδ
    have hδ1 : 1 ≤ δ := (Finset.mem_Icc.1 hδ).1
    have hδR : (1 : ℝ) ≤ δ := by exact_mod_cast hδ1
    have hφ := hφpos δ (by omega)
    by_cases hcase : (δ : ℝ) ≤ √x
    · have hδN : δ < N := by
        have : (δ : ℝ) < N := by nlinarith
        exact_mod_cast this
      have hBT := MathlibExt.NumberTheory.PrimeCounting.BrunTitchmarshWanted.brun_titchmarsh
        N δ 1 (Nat.coprime_one_left δ) hδ1 hδN
      have hNδ : √x / 2 ≤ (N : ℝ) / δ := by
        rw [le_div_iff₀ (by linarith)]
        nlinarith
      have hl : Real.log x / 4 ≤ Real.log ((N : ℝ) / δ) := by
        have h1 : Real.log (√x / 2) = Real.log x / 2 - Real.log 2 := by
          rw [Real.log_div hsx.ne' (by norm_num), Real.log_sqrt hx0.le]
        have h2 : Real.log (√x / 2) ≤ Real.log ((N : ℝ) / δ) :=
          Real.log_le_log (by positivity) hNδ
        linarith
      have hlpos : 0 < Real.log ((N : ℝ) / δ) := by linarith
      have h1 : (primeCountingMod N δ 1 : ℝ) ≤ 8 * x / Real.log x * (1 / δ.totient) := by
        refine hBT.trans ?_
        calc 2 * (N : ℝ) / (δ.totient * Real.log ((N : ℝ) / δ))
            ≤ 2 * x / (δ.totient * (Real.log x / 4)) := by
              apply div_le_div₀ (by positivity) (by linarith) (by positivity)
              exact mul_le_mul_of_nonneg_left hl hφ.le
          _ = 8 * x / Real.log x * (1 / δ.totient) := by field_simp; ring
      have h2 : (primeCountingMod N δ 1 : ℝ) * (1 / (δ.totient : ℝ)) ≤
          8 * x / Real.log x * (1 / (δ.totient : ℝ) ^ 2) := by
        calc (primeCountingMod N δ 1 : ℝ) * (1 / (δ.totient : ℝ))
            ≤ 8 * x / Real.log x * (1 / δ.totient) * (1 / (δ.totient : ℝ)) :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = _ := by ring
      have h3 : 0 ≤ √x * (1 / (δ.totient : ℝ)) := by positivity
      linarith
    · have h1 : (primeCountingMod N δ 1 : ℝ) ≤ √x := by
        calc (primeCountingMod N δ 1 : ℝ) ≤ ((N / δ : ℕ) : ℝ) := by
              exact_mod_cast primeCountingMod_one_le_div N δ
          _ ≤ (N : ℝ) / δ := Nat.cast_div_le
          _ ≤ x / δ := div_le_div_of_nonneg_right hNx (by linarith)
          _ ≤ √x := by
              rw [div_le_iff₀ (by linarith)]
              nlinarith
      have h2 : (primeCountingMod N δ 1 : ℝ) * (1 / (δ.totient : ℝ)) ≤
          √x * (1 / (δ.totient : ℝ)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      have h3 : 0 ≤ 8 * x / Real.log x * (1 / (δ.totient : ℝ) ^ 2) := by positivity
      linarith
  have hlogN : Real.log N ≤ Real.log x := Real.log_le_log (by exact_mod_cast hN1) hNx
  -- `(log x)² ≤ 16 √x`
  have hq : √(√x) * √(√x) = √x := Real.mul_self_sqrt hsx.le
  have hqpos : 0 < √(√x) := Real.sqrt_pos.mpr hsx
  have hl4 : Real.log x ≤ 4 * √(√x) := by
    have e1 : Real.log (√(√x)) = Real.log x / 4 := by
      rw [Real.log_sqrt hsx.le, Real.log_sqrt hx0.le]; ring
    have e2 := Real.log_le_sub_one_of_pos hqpos
    linarith
  have hL2 : Real.log x * Real.log x ≤ 16 * √x := by
    have := mul_le_mul hl4 hl4 hlogpos.le (by positivity)
    nlinarith
  have hkey : √x * (4 * (1 + Real.log x)) ≤ 128 * (x / Real.log x) := by
    rw [← mul_div_assoc, le_div_iff₀ hlogpos]
    calc √x * (4 * (1 + Real.log x)) * Real.log x
        ≤ √x * 8 * (Real.log x * Real.log x) := by
          nlinarith [mul_nonneg (mul_nonneg hsx.le hlogpos.le) (sub_nonneg.2 hlog1)]
      _ ≤ √x * 8 * (16 * √x) := mul_le_mul_of_nonneg_left hL2 (by positivity)
      _ = 128 * (√x * √x) := by ring
      _ = 128 * x := by rw [hsxx]
  have hfinal : ∑ p ∈ primesLE ⌊x⌋₊, ((p - 1 : ℕ) : ℝ) / ((p - 1).totient : ℝ)
      ≤ 256 * (x / Real.log x) := by
    calc _ ≤ _ := hS
      _ ≤ ∑ δ ∈ Icc 1 N, (8 * x / Real.log x * (1 / (δ.totient : ℝ) ^ 2) +
            √x * (1 / (δ.totient : ℝ))) := Finset.sum_le_sum hterm
      _ = 8 * x / Real.log x * ∑ δ ∈ Icc 1 N, 1 / (δ.totient : ℝ) ^ 2 +
            √x * ∑ δ ∈ Icc 1 N, 1 / (δ.totient : ℝ) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 8 * x / Real.log x * 16 + √x * (4 * (1 + Real.log x)) :=
          _root_.add_le_add (mul_le_mul_of_nonneg_left (hB N) (by positivity))
            (mul_le_mul_of_nonneg_left ((hC N).trans (by linarith)) hsx.le)
      _ ≤ 256 * (x / Real.log x) := by
          have : 8 * x / Real.log x * 16 = 128 * (x / Real.log x) := by ring
          linarith
  have hnn : 0 ≤ ∑ p ∈ primesLE ⌊x⌋₊, ((p - 1 : ℕ) : ℝ) / ((p - 1).totient : ℝ) :=
    Finset.sum_nonneg fun _ _ => by positivity
  rw [Real.norm_of_nonneg hnn, Real.norm_of_nonneg (by positivity)]
  exact hfinal

end Nat
