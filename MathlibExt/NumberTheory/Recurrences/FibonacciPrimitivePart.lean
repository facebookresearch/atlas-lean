/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.NatFib
import MathlibExt.NumberTheory.Padics.FibonomialPrimePowerValuation
import MathlibExt.NumberTheory.Recurrences.FibonacciPrimeDivisibility

/-! # Fibonacci entry points, cyclotomic values and primitive parts

This module defines the Fibonacci entry point `z(k)`, the Fibonacci cyclotomic values `Φ_m` and
the primitive parts `Ψ_m` of the Fibonacci numbers, and proves Lemma 1 of Luca, Pomerance and
Wagner (*Fibonacci integers*, J. Number Theory 131 (2011)), as quoted in Luca's paper on
factorials that are Fibonacci integers: if `∏_{a ∈ I} Φ_a / ∏_{b ∈ J} Φ_b` is a natural number,
the prime factors of `∏_{b ∈ J} Ψ_b` inject into `I`, each prime `p` going to an element of the
form `p^k z(p)` (`exists_injection_primeFactors_fibPrimitivePart`).

The proof computes the `p`-adic valuation of `Φ_a` by Möbius inversion from that of the Fibonacci
numbers: it is `v_p(F_{z(p)})` at `a = z(p)`, `1` at `a = p^k z(p)` with `k ≥ 1` (except
`v_2(Φ_6) = 2`), and `0` otherwise.

The paper's title is cited as printed. The printed product (checked against the journal PDF)
evaluates to `36! / 8`, not `36!` (`8 = F_6`).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Entry point in the Fibonacci sequence.** The entry point (rank of apparition) $z(k)$ of a
natural number $k$ is the least $m > 0$ such that $k$ divides the Fibonacci number $F_m$, and
$z(k) = 0$ if there is no such $m$.

Source: Florian Luca, *`F_4 F_5^6 F_7 F_8^4 F_9 F_{10}^2 F_{12}^5 F_{14} F_{15}^{-1}
F_{18} F_{24} F_{30} = 36!`*, INTEGERS 24 (2024), Article A72, Section 2. -/
public noncomputable def fibEntryPoint (k : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ k ∣ Nat.fib m}

/-- **Fibonacci entry point of $2$.** The least $m > 0$ such that $2$ divides the Fibonacci number
$F_m$ is $3$, that is, the Fibonacci entry point of $2$ is $z(2) = 3$.

Source: Florian Luca, *`F_4 F_5^6 F_7 F_8^4 F_9 F_{10}^2 F_{12}^5 F_{14} F_{15}^{-1}
F_{18} F_{24} F_{30} = 36!`*, INTEGERS 24 (2024), Article A72, Section 2 (`6 = 2 z(2)`). -/
public theorem fibEntryPoint_two : fibEntryPoint 2 = 3 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨by norm_num, by decide⟩
  · refine le_csInf ⟨3, by norm_num, by decide⟩ ?_
    rintro m ⟨hm, hdvd⟩
    by_contra h
    interval_cases m <;> simp_all [Nat.fib_one, Nat.fib_two]

/-- **Fibonacci entry point of $5$.** The least $m > 0$ such that $5$ divides the Fibonacci number
$F_m$ is $5$, that is, the Fibonacci entry point of $5$ is $z(5) = 5$.

Source: Florian Luca, *`F_4 F_5^6 F_7 F_8^4 F_9 F_{10}^2 F_{12}^5 F_{14} F_{15}^{-1}
F_{18} F_{24} F_{30} = 36!`*, INTEGERS 24 (2024), Article A72, Section 2 (the exceptional index `m =
5`). -/
public theorem fibEntryPoint_five : fibEntryPoint 5 = 5 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨by norm_num, by decide⟩
  · refine le_csInf ⟨5, by norm_num, by decide⟩ ?_
    rintro m ⟨hm, hdvd⟩
    by_contra h
    interval_cases m <;> revert hdvd <;> decide

/-- **Fibonacci cyclotomic values.** For a natural number $m$, $\Phi_m$ is the rational number
$\prod_{d \mid m} F_{m/d}^{\mu(d)}$, where $d$ runs over the positive divisors of $m$, $F_k$ is the
$k$-th Fibonacci number and $\mu$ is the Möbius function. For $m > 1$ this is the value
$\Phi_m(\alpha, \beta)$ of the homogenized $m$-th cyclotomic polynomial at the roots
$\alpha, \beta$ of $x^2 - x - 1$.

At $m = 1$ the formula gives $1$, not $\Phi_1(\alpha, \beta) = \alpha - \beta = \sqrt{5}$, and
$m = 0$ is treated as having no divisors, so $\Phi_0 = 1$.

Source: Florian Luca, *`F_4 F_5^6 F_7 F_8^4 F_9 F_{10}^2 F_{12}^5 F_{14} F_{15}^{-1}
F_{18} F_{24} F_{30} = 36!`*, INTEGERS 24 (2024), Article A72, Section 2. -/
public noncomputable def fibCyclotomicValue (m : ℕ) : ℚ :=
  ∏ d ∈ m.divisors, (Nat.fib (m / d) : ℚ) ^ (ArithmeticFunction.moebius d)

/-- **Fibonacci cyclotomic value at $2$.** The Fibonacci cyclotomic value
$\Phi_2 = \prod_{d \mid 2} F_{2/d}^{\mu(d)} = F_2 / F_1$, where $F_k$ is the $k$-th Fibonacci number
and $\mu$ is the Möbius function, equals $1$.

Source: Florian Luca, *`F_4 F_5^6 F_7 F_8^4 F_9 F_{10}^2 F_{12}^5 F_{14} F_{15}^{-1}
F_{18} F_{24} F_{30} = 36!`*, INTEGERS 24 (2024), Article A72, Section 2, Equation (1). -/
public theorem fibCyclotomicValue_two : fibCyclotomicValue 2 = 1 := by
  have h : Nat.divisors 2 = {1, 2} := by decide
  simp [fibCyclotomicValue, h, ArithmeticFunction.moebius_apply_prime Nat.prime_two]

/-- **Primitive part of a Fibonacci number.** For a natural number $m$, the primitive part of the
Fibonacci number $F_m$ is $\Psi_m = \prod_p p^{a_p}$, where the product runs over the primes $p$
dividing $F_m$ whose Fibonacci entry point is $z(p) = m$, and $a_p$ is the exponent of $p$ in
$F_m$.

Source: Florian Luca, *`F_4 F_5^6 F_7 F_8^4 F_9 F_{10}^2 F_{12}^5 F_{14} F_{15}^{-1}
F_{18} F_{24} F_{30} = 36!`*, INTEGERS 24 (2024), Article A72, Section 2. -/
public noncomputable def fibPrimitivePart (m : ℕ) : ℕ :=
  ∏ p ∈ (Nat.fib m).primeFactors with fibEntryPoint p = m, p ^ (Nat.fib m).factorization p

/-- **Primitive part of $F_6$.** The primitive part of the Fibonacci number $F_6$ is $\Psi_6 = 1$:
$F_6 = 8 = 2^3$ and the Fibonacci entry point of $2$ is $z(2) = 3 \ne 6$, so $F_6$ has no prime
factor $p$ with $z(p) = 6$.

Source: Florian Luca, *`F_4 F_5^6 F_7 F_8^4 F_9 F_{10}^2 F_{12}^5 F_{14} F_{15}^{-1}
F_{18} F_{24} F_{30} = 36!`*, INTEGERS 24 (2024), Article A72, Section 2. -/
public theorem fibPrimitivePart_six : fibPrimitivePart 6 = 1 := by
  have h : (Nat.fib 6).primeFactors = {2} := by
    rw [show Nat.fib 6 = 2 ^ 3 by decide, Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two]
  simp [fibPrimitivePart, h, fibEntryPoint_two]

/-! ### Entry points -/

/-- If the entry point of `k` is positive, then `k` divides the Fibonacci number there. -/
private theorem dvd_fib_fibEntryPoint {k : ℕ} (hk : 0 < fibEntryPoint k) :
    k ∣ Nat.fib (fibEntryPoint k) := by
  have hne : {m : ℕ | 0 < m ∧ k ∣ Nat.fib m}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    simp [fibEntryPoint, h] at hk
  exact (Nat.sInf_mem hne).2

/-- `k ∣ F_n` exactly when the (positive) entry point of `k` divides `n`. -/
private theorem dvd_fib_iff_fibEntryPoint_dvd {k : ℕ} (hk : 0 < fibEntryPoint k) (n : ℕ) :
    k ∣ Nat.fib n ↔ fibEntryPoint k ∣ n := by
  constructor
  · intro h
    have hg : k ∣ Nat.fib (Nat.gcd (fibEntryPoint k) n) := by
      rw [Nat.fib_gcd]
      exact Nat.dvd_gcd (dvd_fib_fibEntryPoint hk) h
    have hle : fibEntryPoint k ≤ Nat.gcd (fibEntryPoint k) n :=
      Nat.sInf_le ⟨Nat.gcd_pos_of_pos_left n hk, hg⟩
    exact Nat.gcd_eq_left_iff_dvd.mp (le_antisymm (Nat.gcd_le_left n hk) hle)
  · intro h
    exact (dvd_fib_fibEntryPoint hk).trans (Nat.fib_dvd _ _ h)

/-- **Fibonacci entry point of $3$.** The least $m > 0$ such that $3$ divides the Fibonacci number
$F_m$ is $4$, that is, the Fibonacci entry point of $3$ is $z(3) = 4$.

Source: direct computation ($F_1 = F_2 = 1$, $F_3 = 2$, $F_4 = 3$) from the definition of the
entry point in Florian Luca, *`F_4 F_5^6 F_7 F_8^4 F_9 F_{10}^2 F_{12}^5 F_{14} F_{15}^{-1}
F_{18} F_{24} F_{30} = 36!`*, INTEGERS 24 (2024), Article A72, Section 2. -/
public theorem fibEntryPoint_three : fibEntryPoint 3 = 4 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨by norm_num, by decide⟩
  · refine le_csInf ⟨4, by norm_num, by decide⟩ ?_
    rintro m ⟨hm, hdvd⟩
    by_contra h
    interval_cases m <;> revert hdvd <;> decide

/-- The entry point of a prime `p` is at most `p + 1` (law of apparition). -/
private theorem fibEntryPoint_le_succ {p : ℕ} (hp : p.Prime) : fibEntryPoint p ≤ p + 1 := by
  rcases eq_or_ne p 2 with rfl | hp2
  · rw [fibEntryPoint_two]
  rcases eq_or_ne p 5 with rfl | hp5
  · rw [fibEntryPoint_five]
    omega
  have : Fact p.Prime := ⟨hp⟩
  have h := fib_prime_dvd_fib_of_legendre_sub p hp5 (lt_of_le_of_ne hp.two_le (Ne.symm hp2))
  have h2 := hp.two_le
  have hmem : ∀ m, 0 < m → p ∣ Nat.fib m → fibEntryPoint p ≤ m := fun m hm hdvd =>
    Nat.sInf_le ⟨hm, hdvd⟩
  split_ifs at h
  · exact (hmem _ (by omega) h).trans (by omega)
  · exact hmem _ (by omega) h

/-! ### Valuations of Fibonacci numbers -/

/-- The `p`-adic valuation of `F_n` for an odd prime `p` with a positive entry point `z`:
it is `v_p(F_z) + v_p(n / z)` if `z ∣ n` and `0` otherwise. -/
private theorem multiplicity_fib_of_ne_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hz : 0 < fibEntryPoint p) {n : ℕ} (hn : 0 < n) :
    multiplicity p (Nat.fib n) =
      if fibEntryPoint p ∣ n then
        multiplicity p (Nat.fib (fibEntryPoint p)) + multiplicity p (n / fibEntryPoint p)
      else 0 := by
  have : Fact p.Prime := ⟨hp⟩
  split_ifs with h
  · obtain ⟨j, rfl⟩ := h
    have hj : 1 ≤ j := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    have key := padicValNat_fib_mul p hp2 (fibEntryPoint p) hz (dvd_fib_fibEntryPoint hz) j hj
    rw [Nat.mul_div_cancel_left j hz]
    simpa only [Nat.padicValNat_def] using key
  · exact multiplicity_eq_zero_of_not_dvd (by rwa [dvd_fib_iff_fibEntryPoint_dvd hz])

/-- The Fibonacci numbers modulo `8` have period `12`. -/
private theorem fib_mod_eight (n : ℕ) : Nat.fib n % 8 = Nat.fib (n % 12) % 8 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n 12 with h | h
    · rw [Nat.mod_eq_of_lt h]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
      have hadd : Nat.fib (m + 12) = Nat.fib m * 89 + Nat.fib (m + 1) * 144 := by
        have h := Nat.fib_add m 11
        rw [show Nat.fib 11 = 89 by decide, show Nat.fib (11 + 1) = 144 by decide] at h
        simpa using h
      rw [hadd, Nat.add_mod_right, ← ih m (by omega)]
      omega

/-- Residues of the Lucas number `L_m = 2 F_{m+1} - F_m`. -/
private theorem lucas_mod (m : ℕ) :
    (m % 6 = 0 → (2 * Nat.fib (m + 1) - Nat.fib m) % 4 = 2) ∧
      (m % 6 = 3 → (2 * Nat.fib (m + 1) - Nat.fib m) % 8 = 4) ∧
      (m % 3 ≠ 0 → (2 * Nat.fib (m + 1) - Nat.fib m) % 2 = 1) := by
  have h1 := fib_mod_eight m
  have h2 := fib_mod_eight (m + 1)
  have hle : Nat.fib m ≤ Nat.fib (m + 1) := Nat.fib_le_fib_succ
  have e : (m + 1) % 12 = (m % 12 + 1) % 12 := by omega
  rw [e] at h2
  have hr : m % 12 < 12 := Nat.mod_lt _ (by norm_num)
  interval_cases hm : m % 12 <;> norm_num at h1 h2 <;> omega

private theorem multiplicity_two_eq_zero {x : ℕ} (h : x % 2 = 1) : multiplicity 2 x = 0 :=
  multiplicity_eq_zero_of_not_dvd (by omega)

private theorem multiplicity_two_eq_one {x : ℕ} (h : x % 4 = 2) : multiplicity 2 x = 1 :=
  multiplicity_eq_of_dvd_of_not_dvd (by norm_num; omega) (by norm_num; omega)

private theorem multiplicity_two_eq_two {x : ℕ} (h : x % 8 = 4) : multiplicity 2 x = 2 :=
  multiplicity_eq_of_dvd_of_not_dvd (by norm_num; omega) (by norm_num; omega)

/-- The `2`-adic valuation of `F_n`: `1` if `n ≡ 3 (mod 6)`, `v_2(n / 6) + 3` if `6 ∣ n`, and
`0` otherwise. -/
private theorem multiplicity_two_fib : ∀ {n : ℕ}, 0 < n →
    multiplicity 2 (Nat.fib n) =
      (if 3 ∣ n then 1 else 0) + (if 6 ∣ n then 2 + multiplicity 2 (n / 6) else 0) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hm : 0 < m := by omega
    have hle : Nat.fib m ≤ Nat.fib (m + 1) := Nat.fib_le_fib_succ
    have hFm : 0 < Nat.fib m := Nat.fib_pos.mpr hm
    rw [Nat.fib_two_mul, Nat.multiplicity_mul hFm.ne' (by omega), ih m (by omega) hm]
    obtain ⟨hL0, hL3, hL⟩ := lucas_mod m
    rcases (by omega : m % 3 ≠ 0 ∨ m % 6 = 3 ∨ m % 6 = 0) with h | h | h
    · rw [multiplicity_two_eq_zero (hL h)]
      simp [show ¬ 3 ∣ m by omega, show ¬ 6 ∣ m by omega, show ¬ 3 ∣ 2 * m by omega,
        show ¬ 6 ∣ 2 * m by omega]
    · rw [multiplicity_two_eq_two (hL3 h),
        multiplicity_two_eq_zero (show 2 * m / 6 % 2 = 1 by omega)]
      simp [show 3 ∣ m by omega, show ¬ 6 ∣ m by omega, show 3 ∣ 2 * m by omega,
        show 6 ∣ 2 * m by omega]
    · rw [multiplicity_two_eq_one (hL0 h), show 2 * m / 6 = 2 * (m / 6) by omega,
        Nat.multiplicity_mul two_ne_zero (by omega), Nat.multiplicity_self one_lt_two]
      simp only [show 3 ∣ m by omega, show 6 ∣ m by omega, show 3 ∣ 2 * m by omega,
        show 6 ∣ 2 * m by omega, ↓reduceIte]
      omega
  · have h1 := fib_mod_eight (2 * m + 1)
    have h6 : ¬ 6 ∣ 2 * m + 1 := by omega
    by_cases h3 : 3 ∣ 2 * m + 1
    · have hmod : Nat.fib (2 * m + 1) % 4 = 2 := by
        rcases (by omega : (2 * m + 1) % 12 = 3 ∨ (2 * m + 1) % 12 = 9) with hr | hr <;>
          rw [hr] at h1 <;> norm_num at h1 <;> omega
      rw [multiplicity_two_eq_one hmod]
      simp [h3, h6]
    · have hmod : Nat.fib (2 * m + 1) % 2 = 1 := by
        rcases (by omega : (2 * m + 1) % 12 = 1 ∨ (2 * m + 1) % 12 = 5 ∨
            (2 * m + 1) % 12 = 7 ∨ (2 * m + 1) % 12 = 11) with hr | hr | hr | hr <;>
          rw [hr] at h1 <;> norm_num at h1 <;> omega
      rw [multiplicity_two_eq_zero hmod]
      simp [h3, h6]

/-! ### Möbius sums -/

/-- The sum of `μ(d)` over the divisors `d` of `c` is `1` if `c = 1` and `0` otherwise. -/
private theorem sum_moebius (c : ℕ) :
    ∑ d ∈ c.divisors, (ArithmeticFunction.moebius d : ℤ) = if c = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f c)
    ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  exact h

/-- The Möbius transform of `v_p` is the indicator of the positive powers of `p`. -/
private theorem sum_moebius_mul_multiplicity {p : ℕ} (hp : p.Prime) (c : ℕ) :
    ∑ d ∈ c.divisors, (ArithmeticFunction.moebius d : ℤ) * (multiplicity p (c / d) : ℤ) =
      if c ≠ 1 ∧ c = p ^ multiplicity p c then 1 else 0 := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp
  have key : ∀ n > 0, ∑ i ∈ n.divisors,
      (if i ≠ 1 ∧ i = p ^ multiplicity p i then (1 : ℤ) else 0) = (multiplicity p n : ℤ) := by
    intro n hn
    have hfilter : n.divisors.filter (fun i => i ≠ 1 ∧ i = p ^ multiplicity p i) =
        (Finset.Icc 1 (multiplicity p n)).image (p ^ ·) := by
      ext i
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hin, -⟩, hi1, hip⟩
        refine ⟨multiplicity p i, ⟨?_, ?_⟩, hip.symm⟩
        · rcases Nat.eq_zero_or_pos (multiplicity p i) with h0 | h0
          · exact absurd (by rw [hip, h0, pow_zero]) hi1
          · exact h0
        · rw [← Nat.pow_dvd_iff_le_multiplicity hp.ne_one hn.ne', ← hip]
          exact hin
      · rintro ⟨k, ⟨hk1, hkn⟩, rfl⟩
        refine ⟨⟨(pow_dvd_pow p hkn).trans (pow_multiplicity_dvd p n), hn.ne'⟩, ?_, ?_⟩
        · exact (Nat.one_lt_pow (by omega) hp.one_lt).ne'
        · rw [multiplicity_base_pow hp.one_lt]
    rw [Finset.sum_boole, hfilter,
      Finset.card_image_of_injective _ (Nat.pow_right_injective hp.two_le), Nat.card_Icc,
      Nat.add_sub_cancel]
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp key) c hc
  simp only [Int.cast_id] at h
  rw [Nat.sum_divisorsAntidiagonal
    (fun x y => (ArithmeticFunction.moebius x : ℤ) * (multiplicity p y : ℤ))] at h
  exact h

/-- Möbius sums of a function supported on the multiples of `z`. -/
private theorem sum_moebius_mul_of_dvd {z : ℕ} (hz : 0 < z) (f h : ℕ → ℤ)
    (hf : ∀ n, 0 < n → f n = if z ∣ n then h (n / z) else 0) (a : ℕ) :
    ∑ d ∈ a.divisors, (ArithmeticFunction.moebius d : ℤ) * f (a / d) =
      if z ∣ a then ∑ d ∈ (a / z).divisors, (ArithmeticFunction.moebius d : ℤ) * h (a / z / d)
      else 0 := by
  have hpos : ∀ d ∈ a.divisors, 0 < a / d := fun d hd =>
    Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)
  rw [Finset.sum_congr rfl fun d hd => by rw [hf _ (hpos d hd)]]
  split_ifs with hza
  · obtain ⟨c, rfl⟩ := hza
    rw [Nat.mul_div_cancel_left c hz]
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · simp
    have hsub : c.divisors ⊆ (z * c).divisors :=
      Nat.divisors_subset_of_dvd (by positivity) (dvd_mul_left c z)
    symm
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun d hd => ?_
      have hdc : d ∣ c := Nat.dvd_of_mem_divisors hd
      rw [Nat.mul_div_assoc z hdc, ite_eq_left (dvd_mul_right z _), Nat.mul_div_cancel_left _ hz]
    · intro d hd hdc
      rw [ite_eq_right, mul_zero]
      rintro ⟨k, hk⟩
      apply hdc
      have hdzc : d ∣ z * c := Nat.dvd_of_mem_divisors hd
      have hzc : z * c = z * (d * k) := by
        rw [← Nat.mul_div_cancel' hdzc, hk]
        ring
      exact Nat.mem_divisors.mpr ⟨⟨k, Nat.eq_of_mul_eq_mul_left hz hzc⟩, hc.ne'⟩
  · refine Finset.sum_eq_zero fun d hd => ?_
    rw [ite_eq_right, mul_zero]
    exact fun h' => hza (h'.trans (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd)))

/-! ### Valuations of the Fibonacci cyclotomic values -/

private theorem fib_div_ne_zero {a d : ℕ} (hd : d ∈ a.divisors) : (Nat.fib (a / d) : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.fib_pos.mpr
    (Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd))).ne'

private theorem fibCyclotomicValue_ne_zero (m : ℕ) : fibCyclotomicValue m ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hd => zpow_ne_zero _ (fib_div_ne_zero hd)

private theorem padicValRat_finset_prod {ι : Type*} (p : ℕ) [Fact p.Prime] (s : Finset ι)
    (f : ι → ℚ) (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      padicValRat.mul (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

private theorem padicValRat_multiset_prod (p : ℕ) [Fact p.Prime] (s : Multiset ℚ)
    (hs : ∀ x ∈ s, x ≠ 0) : padicValRat p s.prod = (s.map (padicValRat p)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons,
      padicValRat.mul (hs a (Multiset.mem_cons_self a s))
        (Multiset.prod_ne_zero fun h => hs 0 (Multiset.mem_cons_of_mem h) rfl),
      ih fun x hx => hs x (Multiset.mem_cons_of_mem hx)]

/-- The `p`-adic valuation of `Φ_a` as a Möbius sum of valuations of Fibonacci numbers. -/
private theorem padicValRat_fibCyclotomicValue (p : ℕ) [Fact p.Prime] (a : ℕ) :
    padicValRat p (fibCyclotomicValue a) =
      ∑ d ∈ a.divisors,
        (ArithmeticFunction.moebius d : ℤ) * (multiplicity p (Nat.fib (a / d)) : ℤ) := by
  unfold fibCyclotomicValue
  rw [padicValRat_finset_prod p _ _ fun d hd => zpow_ne_zero _ (fib_div_ne_zero hd)]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [padicValRat.zpow, padicValRat.of_nat]

/-- `v_p(Φ_a)` for an odd prime `p` with a positive entry point `z`. -/
private theorem padicValRat_fibCyclotomicValue_of_ne_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hz : 0 < fibEntryPoint p) (a : ℕ) :
    padicValRat p (fibCyclotomicValue a) =
      if fibEntryPoint p ∣ a then
        (if a / fibEntryPoint p = 1 then 1 else 0) *
            (multiplicity p (Nat.fib (fibEntryPoint p)) : ℤ) +
          (if a / fibEntryPoint p ≠ 1 ∧
              a / fibEntryPoint p = p ^ multiplicity p (a / fibEntryPoint p) then 1 else 0)
      else 0 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [padicValRat_fibCyclotomicValue]
  rw [sum_moebius_mul_of_dvd hz (fun n => (multiplicity p (Nat.fib n) : ℤ))
    (fun m => (multiplicity p (Nat.fib (fibEntryPoint p)) : ℤ) + (multiplicity p m : ℤ))
    (fun n hn => by rw [multiplicity_fib_of_ne_two hp hp2 hz hn]; split_ifs <;> simp)]
  by_cases h : fibEntryPoint p ∣ a
  · rw [ite_eq_left h, ite_eq_left h]
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_moebius,
      sum_moebius_mul_multiplicity hp]
  · rw [ite_eq_right h, ite_eq_right h]

/-- `v_2(Φ_a)`. -/
private theorem padicValRat_two_fibCyclotomicValue (a : ℕ) :
    padicValRat 2 (fibCyclotomicValue a) =
      (if 3 ∣ a then (if a / 3 = 1 then 1 else 0) else 0) +
        (if 6 ∣ a then (if a / 6 = 1 then 1 else 0) * 2 +
          (if a / 6 ≠ 1 ∧ a / 6 = 2 ^ multiplicity 2 (a / 6) then 1 else 0) else 0) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValRat_fibCyclotomicValue]
  have hsplit : ∀ d ∈ a.divisors,
      (ArithmeticFunction.moebius d : ℤ) * (multiplicity 2 (Nat.fib (a / d)) : ℤ) =
        (ArithmeticFunction.moebius d : ℤ) * (if 3 ∣ a / d then 1 else 0) +
          (ArithmeticFunction.moebius d : ℤ) *
            (if 6 ∣ a / d then 2 + (multiplicity 2 (a / d / 6) : ℤ) else 0) := by
    intro d hd
    rw [multiplicity_two_fib (Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd))]
    split_ifs <;> push_cast <;> ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
    sum_moebius_mul_of_dvd (by norm_num : 0 < 3) (fun n => if 3 ∣ n then 1 else 0)
      (fun _ => 1) (fun n _ => rfl),
    sum_moebius_mul_of_dvd (by norm_num : 0 < 6)
      (fun n => if 6 ∣ n then 2 + (multiplicity 2 (n / 6) : ℤ) else 0)
      (fun m => 2 + (multiplicity 2 m : ℤ)) (fun n _ => rfl)]
  simp only [mul_one, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_moebius,
    sum_moebius_mul_multiplicity Nat.prime_two]

/-- `a` is the entry point of `p` times a positive power of `p`. -/
private abbrev IsEntryPointMulPow (p a : ℕ) : Prop :=
  fibEntryPoint p ∣ a ∧ a ≠ fibEntryPoint p ∧
    a / fibEntryPoint p = p ^ multiplicity p (a / fibEntryPoint p)

private theorem padicValRat_fibCyclotomicValue_fibEntryPoint {p : ℕ} (hp : p.Prime)
    (hz : 0 < fibEntryPoint p) :
    padicValRat p (fibCyclotomicValue (fibEntryPoint p)) =
      multiplicity p (Nat.fib (fibEntryPoint p)) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [padicValRat_fibCyclotomicValue, Finset.sum_eq_single 1]
  · simp
  · intro d hd hd1
    have hd0 := Nat.pos_of_mem_divisors hd
    have hpos : 0 < fibEntryPoint p / d := Nat.div_pos (Nat.divisor_le hd) hd0
    have hlt : fibEntryPoint p / d < fibEntryPoint p := Nat.div_lt_self hz (by omega)
    rw [multiplicity_eq_zero_of_not_dvd, Nat.cast_zero, mul_zero]
    rw [dvd_fib_iff_fibEntryPoint_dvd hz]
    exact fun h => absurd (Nat.le_of_dvd hpos h) (by omega)
  · intro h
    exact absurd (Nat.one_mem_divisors.mpr hz.ne') h

private theorem padicValRat_fibCyclotomicValue_nonneg {p : ℕ} (hp : p.Prime)
    (hz : 0 < fibEntryPoint p) (a : ℕ) : 0 ≤ padicValRat p (fibCyclotomicValue a) := by
  rcases eq_or_ne p 2 with rfl | hp2
  · rw [padicValRat_two_fibCyclotomicValue]
    split_ifs <;> omega
  · rw [padicValRat_fibCyclotomicValue_of_ne_two hp hp2 hz]
    split_ifs <;> omega

private theorem padicValRat_fibCyclotomicValue_le {p : ℕ} (hp : p.Prime)
    (hz : 0 < fibEntryPoint p) {a : ℕ} (ha : a ≠ fibEntryPoint p) (ha6 : a ≠ 6) :
    padicValRat p (fibCyclotomicValue a) ≤ if IsEntryPointMulPow p a then 1 else 0 := by
  rcases eq_or_ne p 2 with rfl | hp2
  · rw [fibEntryPoint_two] at ha
    rw [padicValRat_two_fibCyclotomicValue]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    by_cases h6 : 6 ∣ a
    · have h3 : 3 ∣ a := (by norm_num : 3 ∣ 6).trans h6
      have ha3 : a / 3 ≠ 1 := fun h => ha (by omega)
      have ha6' : a / 6 ≠ 1 := fun h => ha6 (by omega)
      rw [ite_eq_left h3, ite_eq_right ha3, ite_eq_left h6, ite_eq_right ha6']
      by_cases hpow : a / 6 = 2 ^ multiplicity 2 (a / 6)
      · have hne : a / 6 ≠ 0 := by
          rw [hpow]
          positivity
        have hP : IsEntryPointMulPow 2 a := by
          refine ⟨by rw [fibEntryPoint_two]; exact h3, by rw [fibEntryPoint_two]; exact ha, ?_⟩
          rw [fibEntryPoint_two, show a / 3 = 2 * (a / 6) by omega,
            Nat.multiplicity_mul two_ne_zero hne, Nat.multiplicity_self one_lt_two,
            pow_add, pow_one, ← hpow]
        rw [ite_eq_left ⟨ha6', hpow⟩, ite_eq_left hP]
        norm_num
      · rw [ite_eq_right (fun h => hpow h.2)]
        split_ifs <;> norm_num
    · have h3 : (if 3 ∣ a then (if a / 3 = 1 then (1 : ℤ) else 0) else 0) = 0 := by
        split_ifs with h3 h31
        · exact absurd (by omega) ha
        · rfl
        · rfl
      rw [ite_eq_right h6, h3, add_zero]
      split_ifs <;> norm_num
  · rw [padicValRat_fibCyclotomicValue_of_ne_two hp hp2 hz]
    by_cases h : fibEntryPoint p ∣ a
    · have hne : a / fibEntryPoint p ≠ 1 := by
        intro h1
        apply ha
        rw [← Nat.mul_div_cancel' h, h1, mul_one]
      rw [ite_eq_left h, ite_eq_right hne, zero_mul, zero_add]
      by_cases hpow : a / fibEntryPoint p = p ^ multiplicity p (a / fibEntryPoint p)
      · rw [ite_eq_left ⟨hne, hpow⟩, ite_eq_left ⟨h, ha, hpow⟩]
      · rw [ite_eq_right (fun h' => hpow h'.2)]
        split_ifs <;> norm_num
    · rw [ite_eq_right h]
      split_ifs <;> norm_num

/-! ### Primitive parts -/

/-- A prime dividing the primitive part `Ψ_m` has entry point `m`. -/
private theorem fibEntryPoint_eq_of_dvd_fibPrimitivePart {p m : ℕ} (hp : p.Prime)
    (h : p ∣ fibPrimitivePart m) : fibEntryPoint p = m := by
  unfold fibPrimitivePart at h
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp h
  rw [Finset.mem_filter] at hq
  have hq' : q.Prime := Nat.prime_of_mem_primeFactors hq.1
  rw [(Nat.prime_dvd_prime_iff_eq hp hq').mp (hp.dvd_of_dvd_pow hpq)]
  exact hq.2

private theorem fibPrimitivePart_pos (m : ℕ) : 0 < fibPrimitivePart m :=
  Finset.prod_pos fun _ hq =>
    pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1).pos _

private theorem fibPrimitivePart_dvd_fib (m : ℕ) : fibPrimitivePart m ∣ Nat.fib m := by
  rcases eq_or_ne (Nat.fib m) 0 with h | h
  · rw [h]
    exact dvd_zero _
  · unfold fibPrimitivePart
    conv_rhs => rw [← Nat.prod_factorization_pow_eq_self h]
    rw [Finsupp.prod, Nat.support_factorization]
    exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)

/-! ### Distinct primes claim distinct indices -/

/-- If `a = r^i z(r) = s^j z(s)` with `j ≥ 1` for distinct primes `r`, `s`, then `s ≤ r + 1`. -/
private theorem le_succ_of_eq_pow_mul_fibEntryPoint {r s i j a : ℕ} (hr : r.Prime) (hs : s.Prime)
    (hrs : r ≠ s) (hj : 0 < j) (hai : a = r ^ i * fibEntryPoint r)
    (haj : a = s ^ j * fibEntryPoint s) (hz : 0 < fibEntryPoint r) : s ≤ r + 1 := by
  have hsa : s ∣ r ^ i * fibEntryPoint r :=
    hai ▸ haj ▸ dvd_mul_of_dvd_left (dvd_pow_self s hj.ne') _
  rcases (Nat.Prime.dvd_mul hs).mp hsa with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hs hr).mp (hs.dvd_of_dvd_pow h)) (Ne.symm hrs)
  · exact (Nat.le_of_dvd hz h).trans (fibEntryPoint_le_succ hr)

private theorem eq_twelve_of_two_pow_mul_three {i j a : ℕ} (hi : a = 2 ^ i * 3)
    (hj : a = 3 ^ j * 4) : a = 12 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : multiplicity 2 (3 ^ j) = 0 := multiplicity_eq_zero_of_not_dvd fun h => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
    omega
  have hv : multiplicity 2 a = i := by
    rw [hi, Nat.multiplicity_mul (by positivity) (by norm_num), multiplicity_base_pow one_lt_two,
      multiplicity_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3), add_zero]
  have hv' : multiplicity 2 a = 2 := by
    rw [hj, Nat.multiplicity_mul (by positivity) (by norm_num), h3,
      show (4 : ℕ) = 2 ^ 2 by norm_num, multiplicity_base_pow one_lt_two, zero_add]
  rw [hi, ← hv, hv']
  norm_num

/-- Two distinct primes can claim the same index `a` only for `a = 12`. -/
private theorem eq_twelve_of_isEntryPointMulPow {p q a : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hPp : IsEntryPointMulPow p a) (hPq : IsEntryPointMulPow q a) : a = 12 := by
  have decomp : ∀ {r : ℕ}, IsEntryPointMulPow r a → 0 < fibEntryPoint r ∧
      0 < multiplicity r (a / fibEntryPoint r) ∧
        a = r ^ multiplicity r (a / fibEntryPoint r) * fibEntryPoint r := by
    rintro r ⟨hdvd, hne, hpow⟩
    refine ⟨Nat.pos_of_ne_zero fun h0 => hne ?_, Nat.pos_of_ne_zero fun h0 => hne ?_, ?_⟩
    · rw [h0] at hdvd ⊢
      exact Nat.eq_zero_of_zero_dvd hdvd
    · rw [← Nat.div_mul_cancel hdvd, hpow, h0, pow_zero, one_mul]
    · rw [← hpow, Nat.div_mul_cancel hdvd]
  obtain ⟨hzp, hk, hak⟩ := decomp hPp
  obtain ⟨hzq, hl, hal⟩ := decomp hPq
  have h1 := le_succ_of_eq_pow_mul_fibEntryPoint hp hq hpq hl hak hal hzp
  have h2 := le_succ_of_eq_pow_mul_fibEntryPoint hq hp (Ne.symm hpq) hk hal hak hzq
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hcases : (p = 2 ∧ q = 3) ∨ (p = 3 ∧ q = 2) := by
    rcases hp.eq_two_or_odd with h | h <;> rcases hq.eq_two_or_odd with h' | h' <;> omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [fibEntryPoint_two] at hak
    rw [fibEntryPoint_three] at hal
    exact eq_twelve_of_two_pow_mul_three hak hal
  · rw [fibEntryPoint_three] at hak
    rw [fibEntryPoint_two] at hal
    exact eq_twelve_of_two_pow_mul_three hal hak

/-! ### Multiset bookkeeping -/

private theorem exists_le_card_eq {α : Type*} (s : Multiset α) {n : ℕ}
    (hn : n ≤ Multiset.card s) : ∃ t ≤ s, Multiset.card t = n := by
  refine ⟨(s.toList.take n : Multiset α), ?_, ?_⟩
  · conv_rhs => rw [← Multiset.coe_toList s]
    exact Multiset.coe_le.mpr (List.take_sublist n _).subperm
  · rw [Multiset.coe_card, List.length_take, Multiset.length_toList, min_eq_left hn]

private theorem sum_map_boole {α : Type*} (s : Multiset α) (P : α → Prop) [DecidablePred P] :
    (s.map fun a => if P a then (1 : ℤ) else 0).sum = (Multiset.card (s.filter P) : ℤ) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    by_cases h : P a
    · simp [Multiset.filter_cons_of_pos _ h, h, ih, add_comm]
    · simp [Multiset.filter_cons_of_neg _ h, h, ih]

/-! ### Lemma 1 -/

/-- **Prime factors of the primitive parts of the denominator indices.** Let $I$ and $J$ be finite
multisets of natural numbers, every element of which is at least $3$ and different from $6$ and
$12$, such that no element of $I$ equals an element of $J$ and
$\prod_{a \in I} \Phi_a / \prod_{b \in J} \Phi_b$ is a natural number, where $\Phi_m$ is the
$m$-th Fibonacci cyclotomic value. Let $\Psi_m$ be the primitive part of the Fibonacci number
$F_m$ and $z(p)$ the Fibonacci entry point of $p$. Then there is a finite multiset $e$ of pairs
$(p, k)$ of natural numbers such that the multiset of first coordinates of $e$ is the multiset of
prime factors of $\prod_{b \in J} \Psi_b$, counted with multiplicity, and the multiset of the
numbers $p^k z(p)$ for $(p, k) \in e$ is a sub-multiset of $I$.

In other words, there is an injection from the prime factors $p_1, \dots, p_r$ of
$\prod_{b \in J} \Psi_b$, counted with multiplicity, into $I$ that sends each $p_l$ to an element
of the form $p_l^{k_l} z(p_l)$.

Source: Florian Luca, *`F_4 F_5^6 F_7 F_8^4 F_9 F_{10}^2 F_{12}^5 F_{14} F_{15}^{-1}
F_{18} F_{24} F_{30} =
36!`*, INTEGERS 24 (2024), Article A72, Lemma 1 (`integers-2024-A72-lem-1`), quoting
Lemma 1 of F. Luca, C. Pomerance and S. Wagner, *Fibonacci integers*, J. Number Theory 131
(2011), 440–457. -/
public theorem exists_injection_primeFactors_fibPrimitivePart (I J : Multiset ℕ)
    (hI : ∀ n ∈ I, 3 ≤ n ∧ n ≠ 6 ∧ n ≠ 12) (hJ : ∀ m ∈ J, 3 ≤ m ∧ m ≠ 6 ∧ m ≠ 12)
    (hIJ : ∀ n ∈ I, ∀ m ∈ J, n ≠ m)
    (hnat : ∃ N : ℕ, (I.map fibCyclotomicValue).prod / (J.map fibCyclotomicValue).prod = N) :
    ∃ e : Multiset (ℕ × ℕ),
      e.map Prod.fst = ((J.map fibPrimitivePart).prod.primeFactorsList : Multiset ℕ) ∧
        e.map (fun pk => pk.1 ^ pk.2 * fibEntryPoint pk.1) ≤ I := by
  classical
  obtain ⟨N, hN⟩ := hnat
  set M : Multiset ℕ := ((J.map fibPrimitivePart).prod.primeFactorsList : Multiset ℕ) with hM
  -- Every prime of `M` divides some `Ψ_b` with `b ∈ J`, so its entry point is `b`.
  have hMJ : ∀ p ∈ M, p.Prime ∧ fibEntryPoint p ∈ J := by
    intro p hp
    have hpM : p ∈ (J.map fibPrimitivePart).prod.primeFactorsList := Multiset.mem_coe.mp hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactorsList hpM
    obtain ⟨x, hx, hpx⟩ :=
      hpp.prime.exists_mem_multiset_dvd (Nat.dvd_of_mem_primeFactorsList hpM)
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp hx
    exact ⟨hpp, (fibEntryPoint_eq_of_dvd_fibPrimitivePart hpp hpx).symm ▸ hb⟩
  have hΦ : ∀ s : Multiset ℕ, ∀ x ∈ s.map fibCyclotomicValue, x ≠ 0 := by
    intro s x hx
    obtain ⟨m, -, rfl⟩ := Multiset.mem_map.mp hx
    exact fibCyclotomicValue_ne_zero m
  -- The multiplicity of `p` in `M` is at most the number of `a ∈ I` that `p` can claim.
  have hcount : ∀ p ∈ M, M.count p ≤ Multiset.card (I.filter (IsEntryPointMulPow p)) := by
    intro p hpM
    obtain ⟨hp, hzJ⟩ := hMJ p hpM
    have : Fact p.Prime := ⟨hp⟩
    have hz : 0 < fibEntryPoint p := by
      have := (hJ _ hzJ).1
      omega
    have hval : ∀ s : Multiset ℕ, padicValRat p (s.map fibCyclotomicValue).prod =
        (s.map fun a => padicValRat p (fibCyclotomicValue a)).sum := fun s => by
      rw [padicValRat_multiset_prod p _ (hΦ s), Multiset.map_map]
      rfl
    have hIJval : (J.map fun b => padicValRat p (fibCyclotomicValue b)).sum ≤
        (I.map fun a => padicValRat p (fibCyclotomicValue a)).sum := by
      have h1 := congrArg (padicValRat p) hN
      rw [padicValRat.div (Multiset.prod_ne_zero fun h => hΦ I 0 h rfl)
        (Multiset.prod_ne_zero fun h => hΦ J 0 h rfl), padicValRat.of_nat, hval, hval] at h1
      have h2 : (0 : ℤ) ≤ (multiplicity p N : ℤ) := Nat.cast_nonneg _
      linarith
    have hQ : (M.count p : ℤ) = (J.map fun b => padicValRat p (fibPrimitivePart b)).sum := by
      have hne : ∀ x ∈ (J.map fibPrimitivePart).map (Nat.cast : ℕ → ℚ), x ≠ 0 := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
        obtain ⟨m, -, rfl⟩ := Multiset.mem_map.mp hy
        exact Nat.cast_ne_zero.mpr (fibPrimitivePart_pos m).ne'
      rw [hM, Multiset.coe_count, Nat.primeFactorsList_count_eq, Nat.factorization_def _ hp,
        ← padicValRat.of_nat, Nat.cast_multiset_prod, padicValRat_multiset_prod p _ hne,
        Multiset.map_map, Multiset.map_map]
      rfl
    have hΨ : (J.map fun b => padicValRat p (fibPrimitivePart b)).sum ≤
        (J.map fun b => padicValRat p (fibCyclotomicValue b)).sum := by
      refine Multiset.sum_map_le_sum_map _ _ fun b _ => ?_
      rw [padicValRat.of_nat]
      by_cases hzb : fibEntryPoint p = b
      · rw [← hzb, padicValRat_fibCyclotomicValue_fibEntryPoint hp hz]
        exact_mod_cast
          (Nat.pow_dvd_iff_le_multiplicity hp.ne_one (Nat.fib_pos.mpr hz).ne').mp
            ((pow_multiplicity_dvd p _).trans (fibPrimitivePart_dvd_fib _))
      · rw [multiplicity_eq_zero_of_not_dvd
          fun h => hzb (fibEntryPoint_eq_of_dvd_fibPrimitivePart hp h), Nat.cast_zero]
        exact padicValRat_fibCyclotomicValue_nonneg hp hz b
    have hIle : (I.map fun a => padicValRat p (fibCyclotomicValue a)).sum ≤
        (Multiset.card (I.filter (IsEntryPointMulPow p)) : ℤ) := by
      rw [← sum_map_boole]
      exact Multiset.sum_map_le_sum_map _ _ fun a ha =>
        padicValRat_fibCyclotomicValue_le hp hz (hIJ a ha _ hzJ) (hI a ha).2.1
    have key := hΨ.trans (hIJval.trans hIle)
    rw [← hQ] at key
    exact_mod_cast key
  -- Distinct primes claim distinct elements of `I`.
  have hdisj : ∀ p ∈ M, ∀ q ∈ M, ∀ a ∈ I,
      IsEntryPointMulPow p a → IsEntryPointMulPow q a → p = q := by
    intro p hpM q hqM a ha hPp hPq
    by_contra hpq
    exact (hI a ha).2.2
      (eq_twelve_of_isEntryPointMulPow (hMJ p hpM).1 (hMJ q hqM).1 hpq hPp hPq)
  have hB : ∀ p ∈ M.toFinset, ∃ B ≤ I.filter (IsEntryPointMulPow p),
      Multiset.card B = M.count p := fun p hp =>
    exists_le_card_eq _ (hcount p (Multiset.mem_toFinset.mp hp))
  choose! B hBle hBcard using hB
  have hmap : ∀ {β : Type} (f : ℕ × ℕ → β), (∑ p ∈ M.toFinset,
      (B p).map fun a => (p, multiplicity p (a / fibEntryPoint p))).map f =
        ∑ p ∈ M.toFinset, (B p).map fun a => f (p, multiplicity p (a / fibEntryPoint p)) := by
    intro β f
    rw [← Multiset.coe_mapAddMonoidHom, map_sum]
    simp only [Multiset.coe_mapAddMonoidHom, Multiset.map_map, Function.comp_def]
  refine ⟨∑ p ∈ M.toFinset, (B p).map fun a => (p, multiplicity p (a / fibEntryPoint p)),
    ?_, ?_⟩
  · rw [hmap]
    conv_rhs => rw [← Multiset.toFinset_sum_count_nsmul_eq M]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Multiset.map_const', hBcard p hp, Multiset.nsmul_singleton]
  · rw [hmap]
    have hid : ∀ p ∈ M.toFinset,
        (B p).map (fun a => p ^ multiplicity p (a / fibEntryPoint p) * fibEntryPoint p) = B p := by
      intro p hp
      conv_rhs => rw [← Multiset.map_id (B p)]
      refine Multiset.map_congr rfl fun a ha => ?_
      obtain ⟨hdvd, -, hpow⟩ := (Multiset.mem_filter.mp (Multiset.mem_of_le (hBle p hp) ha)).2
      rw [← hpow, Nat.div_mul_cancel hdvd, id]
    rw [Finset.sum_congr rfl hid, Multiset.le_iff_count]
    intro a
    rw [Multiset.count_sum']
    have hzero : ∀ q ∈ M.toFinset, (a ∈ I → ¬ IsEntryPointMulPow q a) →
        Multiset.count a (B q) = 0 := by
      intro q hq hnot
      apply Nat.eq_zero_of_le_zero
      calc Multiset.count a (B q)
          ≤ Multiset.count a (I.filter (IsEntryPointMulPow q)) :=
            Multiset.count_le_of_le a (hBle q hq)
        _ = 0 := by
          rw [Multiset.count_filter]
          split_ifs with hPq
          · exact Multiset.count_eq_zero.mpr fun haI => hnot haI hPq
          · rfl
    by_cases hex : ∃ p₀ ∈ M.toFinset, IsEntryPointMulPow p₀ a ∧ a ∈ I
    · obtain ⟨p₀, hp₀, hP₀, haI⟩ := hex
      rw [Finset.sum_eq_single p₀]
      · exact (Multiset.count_le_of_le a (hBle p₀ hp₀)).trans
          (Multiset.count_le_of_le a (Multiset.filter_le _ _))
      · intro q hq hqp₀
        exact hzero q hq fun _ hPq => hqp₀ (hdisj q (Multiset.mem_toFinset.mp hq) p₀
          (Multiset.mem_toFinset.mp hp₀) a haI hPq hP₀)
      · intro h
        exact absurd hp₀ h
    · rw [Finset.sum_eq_zero fun q hq => hzero q hq fun haI hPq => hex ⟨q, hq, hPq, haI⟩]
      exact Nat.zero_le _

end

end MetaMathlibExt
