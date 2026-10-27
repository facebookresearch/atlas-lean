/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Mertens' first theorem

This file proves Mertens' first theorem for the von Mangoldt function,
`∑_{n ≤ x} Λ(n) / n = log x + O(1)`, with an explicit constant. The proof compares
Legendre's identity `log N! = ∑_{d ≤ N} Λ(d) ⌊N / d⌋` with Stirling's lower bound for
`log N!` and Chebyshev's upper bound `ψ(x) ≤ (log 4 + 4) x`.

## Main statements

* `Chebyshev.log_factorial_eq_sum_vonMangoldt_mul_div`: Legendre's identity in von Mangoldt
  form.
* `Chebyshev.abs_sum_vonMangoldt_div_sub_log_le`: Mertens' first theorem with the explicit
  constant `log 4 + 6`.
* `Chebyshev.sum_vonMangoldt_div_sub_log_isBigO_one`: the same statement as a `IsBigO` bound.
-/

@[expose] public section

open Finset ArithmeticFunction

namespace Chebyshev

/-- Legendre's identity in von Mangoldt form: `log N! = ∑_{d ≤ N} Λ(d) ⌊N / d⌋`. -/
theorem log_factorial_eq_sum_vonMangoldt_mul_div (N : ℕ) :
    Real.log (N.factorial : ℝ) =
      ∑ d ∈ Finset.Ioc 0 N, vonMangoldt d * ((N / d : ℕ) : ℝ) := by
  have hcast : ((N.factorial : ℕ) : ℝ) = ∏ m ∈ Finset.Ico 1 (N + 1), (m : ℝ) := by
    have h := Finset.prod_Ico_id_eq_factorial N
    rw [← h, Finset.prod_natCast]
  rw [hcast, Real.log_prod (fun m hm => by
    rw [Finset.mem_Ico] at hm
    exact_mod_cast ne_of_gt hm.1)]
  have h1 : ∀ m ∈ Finset.Ico 1 (N + 1), Real.log (m : ℝ) =
      ∑ d ∈ Finset.Icc 1 N, (if d ∣ m then vonMangoldt d else 0) := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    have hmpos : 0 < m := hm.1
    have hmN : m ≤ N := by omega
    have hsub : m.divisors ⊆ Finset.Icc 1 N := by
      intro x hx
      rw [Nat.mem_divisors] at hx
      rw [Finset.mem_Icc]
      exact ⟨Nat.pos_of_dvd_of_pos hx.1 hmpos, le_trans (Nat.le_of_dvd hmpos hx.1) hmN⟩
    have hfilter : m.divisors = (Finset.Icc 1 N).filter (fun d => d ∣ m) := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨hdvd, -⟩
        exact ⟨hsub (Nat.mem_divisors.mpr ⟨hdvd, ne_of_gt hmpos⟩), hdvd⟩
      · rintro ⟨-, hdvd⟩
        exact ⟨hdvd, ne_of_gt hmpos⟩
    conv_lhs => rw [← vonMangoldt_sum (n := m), hfilter, Finset.sum_filter]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.sum_filter]
  have hcard : ({m ∈ Finset.Ico 1 (N + 1) | d ∣ m}.card : ℝ)
      = ((N / d : ℕ) : ℝ) := by
    congr 1
    have hset : {m ∈ Finset.Ico 1 (N + 1) | d ∣ m} = {x ∈ Finset.Ioc 0 N | d ∣ x} := by
      ext x
      simp [Finset.mem_Ico, Finset.mem_Ioc]
      omega
    rw [hset, Nat.Ioc_filter_dvd_card_eq_div]
  simp [Finset.sum_const, nsmul_eq_mul, hcard, mul_comm]

/-- **Mertens' first theorem**, with an explicit constant:
`|∑_{n ≤ x} Λ(n) / n - log x| ≤ log 4 + 6` for every `x ≥ 1`. -/
theorem abs_sum_vonMangoldt_div_sub_log_le (x : ℝ) (hx : 1 ≤ x) :
    |∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, vonMangoldt n / (n : ℝ) - Real.log x|
      ≤ Real.log 4 + 6 := by
  set N := ⌊x⌋₊ with hNdef
  have hN : 1 ≤ N := (Nat.one_le_floor_iff x).mpr hx
  have hNge1R : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hNx : (N:ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxN1 : x < (N:ℝ) + 1 := Nat.lt_floor_add_one x
  set A := ∑ d ∈ Finset.Ioc 0 N, vonMangoldt d / (d : ℝ) with hAdef
  have hpsi : ∑ d ∈ Finset.Ioc 0 N, vonMangoldt d = Chebyshev.psi (N:ℝ) := by
    have h := Chebyshev.psi_eq_sum_Icc (N:ℝ)
    rw [Nat.floor_natCast] at h
    have hsplit : Finset.Icc 0 N = insert 0 (Finset.Ioc 0 N) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_insert]
      omega
    rw [hsplit, Finset.sum_insert (by simp)] at h
    simp at h
    exact h.symm
  have hNA : Real.log (N.factorial : ℝ) ≤ (N:ℝ) * A := by
    rw [log_factorial_eq_sum_vonMangoldt_mul_div, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    rw [Finset.mem_Ioc] at hd
    have hle : ((N / d : ℕ):ℝ) ≤ (N:ℝ)/(d:ℝ) := Nat.cast_div_le
    have hnn : 0 ≤ vonMangoldt d := vonMangoldt_nonneg
    calc vonMangoldt d * ((N/d:ℕ):ℝ)
        ≤ vonMangoldt d * ((N:ℝ)/(d:ℝ)) :=
          mul_le_mul_of_nonneg_left hle hnn
      _ = (N:ℝ) * (vonMangoldt d / (d:ℝ)) := by ring
  have hStirl := Stirling.le_log_factorial_stirling (n := N) (by omega)
  have hlogNnn : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg hNge1R
  have h2pi : 0 ≤ Real.log (2 * Real.pi) / 2 := by
    apply div_nonneg _ (by norm_num)
    apply Real.log_nonneg
    have hpi := Real.two_le_pi
    linarith
  have hlow : (N:ℝ) * Real.log (N:ℝ) - (N:ℝ) ≤ Real.log (N.factorial : ℝ) := by
    linarith
  have hdiff : ∀ d ∈ Finset.Ioc 0 N, (N:ℝ)/(d:ℝ) - ((N/d:ℕ):ℝ) ≤ 1 := by
    intro d hd
    rw [Finset.mem_Ioc] at hd
    have hdposN : 0 < d := by omega
    have hmod : N % d < d := Nat.mod_lt N hdposN
    have hdecomp : d * (N / d) + N % d = N := Nat.div_add_mod N d
    have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hdposN
    have heq : (N:ℝ)/(d:ℝ) - ((N/d:ℕ):ℝ) = ((N % d : ℕ):ℝ)/(d:ℝ) := by
      have hcast : ((d * (N/d) + N % d : ℕ):ℝ) = (N:ℝ) := by rw [hdecomp]
      push_cast at hcast
      field_simp
      linarith
    rw [heq, div_le_one hdR]
    exact_mod_cast le_of_lt hmod
  have hup : (N:ℝ) * A ≤ Real.log (N.factorial : ℝ) + Chebyshev.psi (N:ℝ) := by
    rw [log_factorial_eq_sum_vonMangoldt_mul_div, Finset.mul_sum, ← hpsi,
      ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro d hd
    have hnn : 0 ≤ vonMangoldt d := vonMangoldt_nonneg
    have h1 := hdiff d hd
    have e1 : (N:ℝ) * (vonMangoldt d / (d:ℝ))
        = vonMangoldt d * ((N:ℝ)/(d:ℝ)) := by ring
    rw [e1]
    have hmul := mul_le_mul_of_nonneg_left h1 hnn
    rw [mul_one] at hmul
    have hsub := mul_sub (vonMangoldt d) ((N:ℝ)/(d:ℝ)) ((N/d:ℕ):ℝ)
    linarith
  have hfact : Real.log (N.factorial : ℝ) ≤ (N:ℝ) * Real.log (N:ℝ) := by
    have h := Nat.factorial_le_pow N
    have hpos : (0:ℝ) < (N.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos N
    have hle : ((N.factorial : ℕ):ℝ) ≤ ((N ^ N : ℕ):ℝ) := by exact_mod_cast h
    rw [Nat.cast_pow] at hle
    calc Real.log (N.factorial:ℝ) ≤ Real.log ((N:ℝ)^N) :=
          Real.log_le_log hpos hle
      _ = (N:ℝ) * Real.log (N:ℝ) := by rw [Real.log_pow]
  have hpsile := Chebyshev.psi_le_const_mul_self (x := (N:ℝ)) (le_of_lt hNpos)
  have hAge1 : Real.log (N:ℝ) - 1 ≤ A := by
    have hmul : (N:ℝ) * (Real.log (N:ℝ) - 1) ≤ (N:ℝ) * A := by
      have hexpand : (N:ℝ)*(Real.log (N:ℝ) - 1)
        = (N:ℝ)*Real.log (N:ℝ) - (N:ℝ) := by ring
      linarith
    exact le_of_mul_le_mul_left hmul hNpos
  have hAle1 : A ≤ Real.log (N:ℝ) + Real.log 4 + 4 := by
    have hmul : (N:ℝ) * A ≤ (N:ℝ) * (Real.log (N:ℝ) + Real.log 4 + 4) := by
      have hexpand : (N:ℝ)*(Real.log (N:ℝ) + Real.log 4 + 4)
        = (N:ℝ)*Real.log (N:ℝ) + (Real.log 4 + 4)*(N:ℝ) := by ring
      linarith
    exact le_of_mul_le_mul_left hmul hNpos
  have hlogNx : Real.log (N:ℝ) ≤ Real.log x := Real.log_le_log hNpos hNx
  have hx2N : x ≤ 2 * (N:ℝ) := by linarith
  have hlogx : Real.log x ≤ Real.log (N:ℝ) + Real.log 2 := by
    have h2N : Real.log x ≤ Real.log (2 * (N:ℝ)) :=
      Real.log_le_log (by linarith) hx2N
    rw [Real.log_mul (by norm_num) (ne_of_gt hNpos)] at h2N
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
  have hlog4nn : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h1 : A - Real.log x ≤ Real.log 4 + 4 := by linarith
  have h2 : -(Real.log 4 + 6) ≤ A - Real.log x := by linarith
  rw [abs_le]
  constructor <;> linarith


/-- **Mertens' first theorem**: `∑_{n ≤ x} Λ(n) / n = log x + O(1)` as `x → ∞`. -/
theorem sum_vonMangoldt_div_sub_log_isBigO_one :
    (fun x : ℝ => ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, vonMangoldt n / (n : ℝ) - Real.log x)
      =O[Filter.atTop] fun _ : ℝ => (1 : ℝ) := by
  refine Asymptotics.IsBigO.of_bound (Real.log 4 + 6) ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
  simpa using abs_sum_vonMangoldt_div_sub_log_le x hx

end Chebyshev
