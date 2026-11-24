/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.LinearCombination

/-!
# Fractional parts of shifted Fibonacci numbers divided by $\sqrt{5}$

Let $F_n$ be the $n$-th Fibonacci number and $\varphi = (1 + \sqrt{5})/2$ the golden ratio, so
that $2\varphi - 1 = \sqrt{5}$. This file defines Wesley's constants $c_{n,\varepsilon}$
(`wesleyFractionalConstant`) and proves Wesley's lemma `fract_fib_add_div_sqrt_five`: for
$n \ge 13$ and $\varepsilon \in \{-4, 0, 4\}$, the fractional part of
$(F_n + \varepsilon)/\sqrt{5}$ is $-2(-\varphi)^{-n}/5 + c_{n,\varepsilon}$, and the parity of
its integer part depends only on $\varepsilon$ and $n \bmod 12$.

## Main declarations

* `MetaMathlibExt.wesleyFractionalConstant`: the constant $c_{n,\varepsilon}$, with
  `wesleyFractionalConstant_zero_of_mod_four_eq_zero`.
* `MetaMathlibExt.fract_fib_add_div_sqrt_five`: the fractional part and the parity of the
  integer part of $(F_n + \varepsilon)/(2\varphi - 1)$.

## Implementation notes

Write $\psi = (1 - \sqrt{5})/2 = (-\varphi)^{-1}$ and $L_n = 2F_{n+1} - F_n$ for the $n$-th Lucas
number. Binet's formula gives $\sqrt{5} F_n = L_n - 2\psi^n$, so
$(F_n + \varepsilon)/\sqrt{5} = (L_n + \varepsilon\sqrt{5})/5 - 2\psi^n/5$, and
$|2\psi^n/5| < 10^{-3}$ for $n \ge 13$. The integer part is therefore
$\lfloor (L_n + k)/5 \rfloor$ with $k = \lfloor \varepsilon\sqrt{5} \rfloor \in \{-9, 0, 8\}$.
The Lucas numbers are periodic modulo $10$ with period $12$ and modulo $5$ with period $4$,
which leaves twelve cases for the fractional part and thirty-six integer cases for the parity.

## References

* William J. Wesley, *Improved Ramsey-type theorems for Fibonacci numbers and other sequences*,
  INTEGERS 25 (2025), Article A29; preprint arXiv:2211.05167, Lemma 9 and its proof.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Wesley's constants $c_{n,\varepsilon}$.** For a natural number $n$ and an integer
$\varepsilon$, the real number $c_{n,\varepsilon}$ is defined by the residue of $n$ modulo $4$:
if $n \equiv 0 \pmod 4$, then $c_{n,\varepsilon} = (4 + (2\sqrt5 - 5)\varepsilon)/10$;
if $n \equiv 1 \pmod 4$, then $c_{n,\varepsilon} = (11 - 4\sqrt5)/5$ when $\varepsilon = -4$ and
$c_{n,\varepsilon} = (4 + (4\sqrt5 - 5)\varepsilon)/20$ otherwise;
if $n \equiv 2 \pmod 4$, then $c_{n,\varepsilon} = (6 + (2\sqrt5 - 5)\varepsilon)/10$;
if $n \equiv 3 \pmod 4$, then $c_{n,\varepsilon} = (9 - 4\sqrt5)/5$ when $\varepsilon = -4$ and
$c_{n,\varepsilon} = (8 + (2\sqrt5 - 5)\varepsilon)/10$ otherwise.

Lemma 5 uses these constants only for $\varepsilon \in \{-4, 0, 4\}$.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Lemma 5 (definition of `c_{n,ε}`). -/
noncomputable def wesleyFractionalConstant (n : ℕ) (ε : ℤ) : ℝ :=
  if n % 4 = 0 then (4 + (2 * √5 - 5) * ε) / 10
  else if n % 4 = 1 then (if ε = -4 then (11 - 4 * √5) / 5 else (4 + (4 * √5 - 5) * ε) / 20)
  else if n % 4 = 2 then (6 + (2 * √5 - 5) * ε) / 10
  else (if ε = -4 then (9 - 4 * √5) / 5 else (8 + (2 * √5 - 5) * ε) / 10)

/-- **Wesley's constant $c_{n,0}$ for $n \equiv 0 \pmod 4$.** For every natural number $n$ with
$n \equiv 0 \pmod 4$, Wesley's constant satisfies $c_{n,0} = 2/5$.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Lemma 5 (definition of `c_{n,ε}`). -/
theorem wesleyFractionalConstant_zero_of_mod_four_eq_zero {n : ℕ} (hn : n % 4 = 0) :
    wesleyFractionalConstant n 0 = 2 / 5 := by
  norm_num [wesleyFractionalConstant, hn]

namespace fract_fib_add_div_sqrt_five

/-- The Lucas number `L (n + 12) = 2 F (n + 13) - F (n + 12)` exceeds `L n` by a multiple
of `10`. -/
private lemma lucas_add_twelve (n : ℕ) :
    2 * (Nat.fib (n + 12 + 1) : ℤ) - Nat.fib (n + 12) =
      2 * (Nat.fib (n + 1) : ℤ) - Nat.fib n + 10 * (20 * Nat.fib n + 32 * Nat.fib (n + 1)) := by
  have h13 : Nat.fib (n + 12 + 1) = Nat.fib n * 144 + Nat.fib (n + 1) * 233 := by
    rw [Nat.fib_add]; norm_num
  have h12 : Nat.fib (n + 12) = Nat.fib n * 89 + Nat.fib (n + 1) * 144 := by
    rw [show n + 12 = n + 11 + 1 from rfl, Nat.fib_add]; norm_num
  rw [h13, h12]; push_cast; ring

/-- The Lucas numbers `2 F (n + 1) - F n` are periodic modulo `10` with period `12`. -/
private lemma lucas_emod_ten (n : ℕ) :
    (2 * (Nat.fib (n + 1) : ℤ) - Nat.fib n) % 10 =
      (2 * (Nat.fib (n % 12 + 1) : ℤ) - Nat.fib (n % 12)) % 10 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 12 with h | h
    · rw [Nat.mod_eq_of_lt h]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
      rw [lucas_add_twelve, Int.add_mul_emod_self_left, ih m (by omega), Nat.add_mod_right]

/-- The Lucas numbers `2 F (n + 1) - F n` are periodic modulo `5` with period `4`. -/
private lemma lucas_emod_five (n : ℕ) :
    (2 * (Nat.fib (n + 1) : ℤ) - Nat.fib n) % 5 =
      (2 * (Nat.fib (n % 4 + 1) : ℤ) - Nat.fib (n % 4)) % 5 := by
  have hs := lucas_emod_ten n
  rw [← Nat.mod_mod_of_dvd n (show 4 ∣ 12 by norm_num)]
  generalize (2 * (Nat.fib (n + 1) : ℤ) - Nat.fib n) = L at hs ⊢
  have h12 : n % 12 < 12 := Nat.mod_lt _ (by norm_num)
  generalize n % 12 = r at hs h12 ⊢
  interval_cases r <;> norm_num [Nat.fib] at hs ⊢ <;> omega

/-- Binet's formula in the form `√5 F n = L n - 2 ψ ^ n`, with `L n = 2 F (n + 1) - F n`. -/
private lemma sqrt_five_mul_fib (n : ℕ) :
    √5 * (Nat.fib n : ℝ) = (2 * Nat.fib (n + 1) - Nat.fib n : ℤ) - 2 * Real.goldenConj ^ n := by
  rw [← Real.fib_succ_sub_goldenRatio_mul_fib n]
  push_cast; ring

/-- `(-φ) ^ (-n) = ψ ^ n`, since `(-φ)⁻¹ = ψ`. -/
private lemma neg_goldenRatio_zpow_neg (n : ℕ) :
    (-Real.goldenRatio) ^ (-(n : ℤ)) = Real.goldenConj ^ n := by
  rw [zpow_neg, zpow_natCast, ← inv_pow, inv_neg, Real.inv_goldenRatio, neg_neg]

/-- For `n ≥ 13`, the correction term `-2 ψ ^ n / 5` has absolute value less than `1 / 1000`. -/
private lemma abs_goldenConj_pow_lt {n : ℕ} (hn : 13 ≤ n) :
    |-(2 * Real.goldenConj ^ n / 5)| < 1 / 1000 := by
  have hsq : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5 : (0 : ℝ) ≤ √5 := Real.sqrt_nonneg 5
  have habs : |Real.goldenConj| ≤ 0.62 := by
    rw [abs_le]; constructor <;> simp only [Real.goldenConj] <;> nlinarith
  have hpow : |Real.goldenConj| ^ n ≤ 0.62 ^ 13 :=
    (pow_le_pow_of_le_one (abs_nonneg _) (habs.trans (by norm_num)) hn).trans
      (pow_le_pow_left₀ (abs_nonneg _) habs 13)
  rw [abs_neg, abs_div, abs_mul, abs_pow]
  norm_num at hpow ⊢
  linarith

/-- If `y = m + (t + c)` with `m` an integer and `0 ≤ t + c < 1`, then `⌊y⌋ = m` and
`Int.fract y = t + c`. -/
private lemma floor_fract_aux {y t c : ℝ} {m : ℤ} (hy : y = m + (t + c)) (h0 : 0 ≤ t + c)
    (h1 : t + c < 1) : ⌊y⌋ = m ∧ Int.fract y = t + c := by
  have hfl : ⌊y⌋ = m := by
    rw [Int.floor_eq_iff]; constructor <;> linarith
  exact ⟨hfl, by rw [Int.fract, hfl, hy]; ring⟩

/-- The core computation: if `L ≡ L_{n mod 4} (mod 5)`, `|t| < 1 / 1000` and `K = ⌊ε √5⌋`,
then `⌊(L + ε √5) / 5 + t⌋ = (L + K) / 5` and the fractional part is `t + c_{n,ε}`. -/
private lemma floor_fract_core (n : ℕ) (L ε K : ℤ) {t : ℝ} (ht : |t| < 1 / 1000)
    (hK : (ε = -4 ∧ K = -9) ∨ (ε = 0 ∧ K = 0) ∨ (ε = 4 ∧ K = 8))
    (hL : L % 5 = (2 * (Nat.fib (n % 4 + 1) : ℤ) - Nat.fib (n % 4)) % 5) :
    ⌊(L + ε * √5) / 5 + t⌋ = (L + K) / 5 ∧
      Int.fract ((L + ε * √5) / 5 + t) = t + wesleyFractionalConstant n ε := by
  have hsq : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5 : (0 : ℝ) ≤ √5 := Real.sqrt_nonneg 5
  have hlo : (2.236 : ℝ) < √5 := by nlinarith
  have hhi : √5 < (2.237 : ℝ) := by nlinarith
  obtain ⟨ht0, ht1⟩ := abs_lt.mp ht
  suffices h : ((((L + K) % 5 : ℤ) : ℝ) - K + ε * √5) / 5 = wesleyFractionalConstant n ε ∧
      0 ≤ t + wesleyFractionalConstant n ε ∧ t + wesleyFractionalConstant n ε < 1 by
    obtain ⟨hc, h0, h1⟩ := h
    refine floor_fract_aux ?_ h0 h1
    have he : (((L + K) % 5 : ℤ) : ℝ) + 5 * ((L + K) / 5 : ℤ) = L + K := by
      exact_mod_cast Int.emod_add_mul_ediv (L + K) 5
    rw [← hc]
    linear_combination (-1 / 5 : ℝ) * he
  obtain ⟨r, hr4, hr⟩ : ∃ r, r < 4 ∧ n % 4 = r := ⟨_, Nat.mod_lt _ (by norm_num), rfl⟩
  rw [hr] at hL
  rw [Int.add_emod, hL]
  refine ⟨?_, ?_, ?_⟩ <;>
    interval_cases r <;> rcases hK with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    norm_num [Nat.fib, wesleyFractionalConstant, hr] <;> linarith

/-- The parity of `(L n + ⌊ε √5⌋) / 5`, read off from `L n mod 10`, which depends only on
`n mod 12`. -/
private lemma even_floor_iff (n : ℕ) (ε K : ℤ)
    (hK : (ε = -4 ∧ K = -9) ∨ (ε = 0 ∧ K = 0) ∨ (ε = 4 ∧ K = 8)) :
    Even ((2 * (Nat.fib (n + 1) : ℤ) - Nat.fib n + K) / 5) ↔
      (ε = 0 ∧ n % 12 ∈ ({0, 1, 2, 3, 5, 10} : Finset ℕ)) ∨
      (ε = 4 ∧ n % 12 ∈ ({0, 2, 3, 9, 10} : Finset ℕ)) ∨
      (ε = -4 ∧ n % 12 ∈ ({0, 1, 2, 5, 7, 10, 11} : Finset ℕ)) := by
  have hs := lucas_emod_ten n
  generalize (2 * (Nat.fib (n + 1) : ℤ) - Nat.fib n) = L at hs ⊢
  have h12 : n % 12 < 12 := Nat.mod_lt _ (by norm_num)
  generalize n % 12 = r at hs h12 ⊢
  interval_cases r <;> rcases hK with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    norm_num [Nat.fib] at hs <;> simp [Int.even_iff] <;> omega

end fract_fib_add_div_sqrt_five

open fract_fib_add_div_sqrt_five in
/-- **Fractional parts of shifted Fibonacci numbers divided by $\sqrt{5}$.** Let $F_n$ be the
$n$-th Fibonacci number, with $F_0 = 0$ and $F_1 = 1$, let $\varphi = (1 + \sqrt{5})/2$ be the
golden ratio, so that $2\varphi - 1 = \sqrt{5}$, and write $\{y\} = y - \lfloor y \rfloor$ for the
fractional part. Let $n \ge 13$ be a natural number and $\varepsilon \in \{-4, 0, 4\}$, let
$c_{n,\varepsilon}$ be Wesley's constant, which depends on $n \bmod 4$ and $\varepsilon$, and put
$y = (F_n + \varepsilon)/(2\varphi - 1)$. Then
(i) $\{y\} = -2(-\varphi)^{-n}/5 + c_{n,\varepsilon}$, and
(ii) $\lfloor y \rfloor$ is even if and only if $\varepsilon = 0$ and
$n \equiv 0, 1, 2, 3, 5, 10 \pmod{12}$, or $\varepsilon = 4$ and
$n \equiv 0, 2, 3, 9, 10 \pmod{12}$, or $\varepsilon = -4$ and
$n \equiv 0, 1, 2, 5, 7, 10, 11 \pmod{12}$.

The paper prints $+2(-\varphi)^{-n}/5$ in (i). The sign $-$ is the one its proof derives
(Equation (1)); the printed sign fails for every $n \ge 13$, since this term is nonzero.

Source: William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other
Sequences*, INTEGERS 25 (2025), Article A29, Lemma 5 (`integers-2025-A29-lem-5`). -/
theorem fract_fib_add_div_sqrt_five (n : ℕ) (hn : 13 ≤ n) (ε : ℤ)
    (hε : ε = -4 ∨ ε = 0 ∨ ε = 4) :
    Int.fract (((Nat.fib n : ℝ) + ε) / (2 * Real.goldenRatio - 1)) =
        -(2 * (-Real.goldenRatio) ^ (-(n : ℤ)) / 5) + wesleyFractionalConstant n ε ∧
    (Even ⌊((Nat.fib n : ℝ) + ε) / (2 * Real.goldenRatio - 1)⌋ ↔
      (ε = 0 ∧ n % 12 ∈ ({0, 1, 2, 3, 5, 10} : Finset ℕ)) ∨
      (ε = 4 ∧ n % 12 ∈ ({0, 2, 3, 9, 10} : Finset ℕ)) ∨
      (ε = -4 ∧ n % 12 ∈ ({0, 1, 2, 5, 7, 10, 11} : Finset ℕ))) := by
  obtain ⟨K, hK⟩ : ∃ K : ℤ, (ε = -4 ∧ K = -9) ∨ (ε = 0 ∧ K = 0) ∨ (ε = 4 ∧ K = 8) := by
    rcases hε with rfl | rfl | rfl <;> simp
  have hy : ((Nat.fib n : ℝ) + ε) / (2 * Real.goldenRatio - 1) =
      (((2 * Nat.fib (n + 1) - Nat.fib n : ℤ) : ℝ) + ε * √5) / 5 +
        -(2 * Real.goldenConj ^ n / 5) := by
    have hsq : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have hden : 2 * Real.goldenRatio - 1 = √5 := by simp only [Real.goldenRatio]; ring
    rw [hden, div_eq_iff (by positivity)]
    linear_combination (√5 / 5) * sqrt_five_mul_fib n - ((Nat.fib n + ε) / 5) * hsq
  obtain ⟨hfl, hfr⟩ := floor_fract_core n _ ε K (abs_goldenConj_pow_lt hn) hK (lucas_emod_five n)
  rw [hy, hfl, hfr, neg_goldenRatio_zpow_neg]
  exact ⟨rfl, even_floor_iff n ε K hK⟩

end

end MetaMathlibExt
