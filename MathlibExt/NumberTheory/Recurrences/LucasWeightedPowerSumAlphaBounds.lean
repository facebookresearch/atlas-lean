/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.Recurrences.LucasBinetFormula

/-!
# Bounds on Lucas sequences by powers of the dominant root

For integer parameters $x \ge 1$ and $y \ne 0$ with $|y + 1| \le x$ and $D = x^2 - 4y > 0$,
this module bounds the terms $U_n(x,y)$ and $V_n(x,y)$ for natural $n \ge 2$ using powers of
$\alpha = (x + \sqrt D)/2$. The paper also allows $y = 0$, where $U_n = x^{n-1}$ and $V_n = x^n$
for $n \ge 2$ and all bounds are equalities; `LucasSequenceParams` models the nonzero case.

## References

* Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
  Equation $\sum_{j=1}^k j F_j^p = F_n^q$ to a Family of Lucas Sequences*, The Fibonacci Quarterly
  62 (2024), no. 3, pp. 241–257, Lemma 2.2.
* Krisztián Gueth, Florian Luca and László Szalay, *On a Diophantine equation involving powers of
  Fibonacci numbers*, Proceedings of the Japan Academy, Series A, Mathematical Sciences 96
  (2020), no. 4, pp. 33–37, Lemma 3 (the Fibonacci case generalized by Lemma 2.2).
* The proof uses `lucas_binet_formulas_of_field` from
  `MathlibExt.NumberTheory.Recurrences.LucasBinetFormula`.
-/

namespace MetaMathlibExt

/-- **Bounds on Lucas sequences by powers of the dominant root.** Let $x$ and $y \neq 0$ be
integers with $x \geq 1$, $|y + 1| \leq x$ and $D = x^2 - 4y > 0$, let $(U_n)$ and $(V_n)$ be the
Lucas sequences with parameters $(x, y)$, given by $U_0 = 0$, $U_1 = 1$, $V_0 = 2$, $V_1 = x$
and $W_{n+2} = x W_{n+1} - y W_n$ for $W = U, V$, and put $\alpha = (x + \sqrt{D})/2$. Then for
every $n \geq 2$ we have $x \alpha^{n-2} \leq U_n$; if $y \leq 0$, then $U_n \leq \alpha^{n-1}$
and $x \alpha^{n-1} \leq V_n \leq \alpha^{n+1}/x$; and if $y \geq 0$, then
$U_n \leq \alpha^n/\sqrt{D}$ and $\alpha^n \leq V_n \leq \alpha^{n+1}/\sqrt{D}$.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 2.2 (`fq-2024-earplynch07182024-lem-2.2`). -/
public theorem lucasU_lucasV_alpha_bounds (P : LucasSequenceParams) (hx : 1 ≤ P.p)
    (hy : |P.q + 1| ≤ P.p) (hD : 0 < P.p ^ 2 - 4 * P.q) {n : ℕ} (hn : 2 ≤ n) :
    let α : ℝ := (P.p + Real.sqrt (P.p ^ 2 - 4 * P.q)) / 2
    (P.p : ℝ) * α ^ (n - 2) ≤ lucasU P n ∧
      (P.q ≤ 0 → (lucasU P n : ℝ) ≤ α ^ (n - 1)) ∧
      (0 ≤ P.q → (lucasU P n : ℝ) ≤ α ^ n / Real.sqrt (P.p ^ 2 - 4 * P.q)) ∧
      (P.q ≤ 0 → (P.p : ℝ) * α ^ (n - 1) ≤ lucasV P n ∧ (lucasV P n : ℝ) ≤ α ^ (n + 1) / P.p) ∧
      (0 ≤ P.q → α ^ n ≤ (lucasV P n : ℝ) ∧
        (lucasV P n : ℝ) ≤ α ^ (n + 1) / Real.sqrt (P.p ^ 2 - 4 * P.q)) := by
  let d : ℝ := Real.sqrt (P.p ^ 2 - 4 * P.q)
  let α : ℝ := (P.p + d) / 2
  let β : ℝ := (P.p - d) / 2
  change (P.p : ℝ) * α ^ (n - 2) ≤ lucasU P n ∧
    (P.q ≤ 0 → (lucasU P n : ℝ) ≤ α ^ (n - 1)) ∧
    (0 ≤ P.q → (lucasU P n : ℝ) ≤ α ^ n / d) ∧
    (P.q ≤ 0 → (P.p : ℝ) * α ^ (n - 1) ≤ lucasV P n ∧ (lucasV P n : ℝ) ≤ α ^ (n + 1) / P.p) ∧
    (0 ≤ P.q → α ^ n ≤ (lucasV P n : ℝ) ∧ (lucasV P n : ℝ) ≤ α ^ (n + 1) / d)
  have hDreal : 0 < (P.p : ℝ) ^ 2 - 4 * P.q := by exact_mod_cast hD
  have hd : 0 < d := Real.sqrt_pos.2 hDreal
  have hp : 0 < (P.p : ℝ) := Int.cast_pos.2 (by omega)
  have hα : 0 < α := div_pos (add_pos hp hd) two_pos
  have hdiff : α - β = d := by dsimp only [α, β]; ring
  have hsum : α + β = (P.p : ℝ) := by dsimp only [α, β]; ring
  have hprod : α * β = (P.q : ℝ) := by
    have hsquare : d ^ 2 = (P.p : ℝ) ^ 2 - 4 * P.q := Real.sq_sqrt hDreal.le
    dsimp only [α, β]
    nlinarith only [hsquare]
  have hne : α ≠ β := sub_ne_zero.mp (hdiff.symm ▸ hd.ne')
  obtain ⟨hU, hV⟩ := (lucas_binet_formulas_of_field P α β hsum hprod).1 hne n
  rw [hdiff] at hU
  -- The smaller root lies in [-1, 1] and the larger root is at least 1.
  have hqabs : |(P.q : ℝ) + 1| ≤ P.p := by exact_mod_cast hy
  obtain ⟨hqlo, hqhi⟩ := abs_le.mp hqabs
  have hdlo : |(P.p : ℝ) - 2| ≤ d := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith only [hqhi])
  have hdhi : d ≤ (P.p : ℝ) + 2 :=
    Real.sqrt_le_iff.mpr ⟨by linarith only [hp], by nlinarith only [hqlo]⟩
  obtain ⟨hdleft, hdright⟩ := abs_le.mp hdlo
  have hβα : |β| ≤ α := calc
    |β| ≤ 1 := abs_le.mpr ⟨by dsimp only [β]; linarith only [hdhi],
      by dsimp only [β]; linarith only [hdright]⟩
    _ ≤ α := by dsimp only [α]; linarith only [hdleft]
  have hpow (k : ℕ) : |β ^ k| ≤ α ^ k := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hβα k
  have hβ₂ : β ^ n ≤ β ^ 2 * α ^ (n - 2) := calc
    β ^ n = β ^ 2 * β ^ (n - 2) := by rw [← pow_add, show 2 + (n - 2) = n by omega]
    _ ≤ β ^ 2 * α ^ (n - 2) :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hpow _)) (sq_nonneg _)
  have hβ₁ : |β ^ n| ≤ |β| * α ^ (n - 1) := calc
    |β ^ n| = |β| * |β ^ (n - 1)| := by
      rw [← abs_mul, ← pow_succ', show n - 1 + 1 = n by omega]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hpow _) (abs_nonneg _)
  have hα₁ : α ^ n = α * α ^ (n - 1) := by
    rw [← pow_succ', show n - 1 + 1 = n by omega]
  -- Both upper bounds for V use x√D = α² - β² ≤ α².
  have hVupper : (P.p : ℝ) * d * α ^ (n - 1) ≤ α ^ (n + 1) := by
    have hpd : (P.p : ℝ) * d ≤ α ^ 2 := by
      rw [← hsum, ← hdiff]
      nlinarith only [sq_nonneg β]
    rw [show n + 1 = 2 + (n - 1) by omega, pow_add]
    exact mul_le_mul_of_nonneg_right hpd (pow_nonneg hα.le _)
  have hβnonpos (hq : P.q ≤ 0) : β ≤ 0 := by
    have hq' : (P.q : ℝ) ≤ 0 := by exact_mod_cast hq
    exact nonpos_of_mul_nonpos_right (hprod.trans_le hq') hα
  have hβnonneg (hq : 0 ≤ P.q) : 0 ≤ β := by
    have hq' : 0 ≤ (P.q : ℝ) := by exact_mod_cast hq
    exact (mul_nonneg_iff_of_pos_left hα).1 (hprod.symm ▸ hq')
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hU]
    apply (le_div_iff₀ hd).2
    rw [show α ^ n = α ^ 2 * α ^ (n - 2) by
      rw [← pow_add, show 2 + (n - 2) = n by omega], ← hsum, ← hdiff]
    nlinarith only [hβ₂]
  · intro hq
    rw [abs_of_nonpos (hβnonpos hq)] at hβ₁
    rw [hU]
    apply (div_le_iff₀ hd).2
    rw [hα₁, ← hdiff]
    nlinarith only [(abs_le.mp hβ₁).1]
  · intro hq
    rw [hU]
    exact div_le_div_of_nonneg_right (sub_le_self _ (pow_nonneg (hβnonneg hq) n)) hd.le
  · intro hq
    rw [abs_of_nonpos (hβnonpos hq)] at hβ₁
    rw [hV]
    constructor
    · rw [hα₁, ← hsum]
      nlinarith only [(abs_le.mp hβ₁).1]
    · apply (le_div_iff₀ hp).2
      have hbound : α ^ n + β ^ n ≤ d * α ^ (n - 1) := by
        rw [hα₁, ← hdiff]
        nlinarith only [(abs_le.mp hβ₁).2]
      calc
        _ ≤ (d * α ^ (n - 1)) * (P.p : ℝ) := mul_le_mul_of_nonneg_right hbound hp.le
        _ = (P.p : ℝ) * d * α ^ (n - 1) := by ring
        _ ≤ _ := hVupper
  · intro hq
    have hβ := hβnonneg hq
    rw [abs_of_nonneg hβ] at hβ₁
    rw [hV]
    refine ⟨le_add_of_nonneg_right (pow_nonneg hβ n), (le_div_iff₀ hd).2 ?_⟩
    have hbound : α ^ n + β ^ n ≤ (P.p : ℝ) * α ^ (n - 1) := by
      rw [hα₁, ← hsum]
      nlinarith only [(abs_le.mp hβ₁).2]
    calc
      _ ≤ ((P.p : ℝ) * α ^ (n - 1)) * d := mul_le_mul_of_nonneg_right hbound hd.le
      _ = (P.p : ℝ) * d * α ^ (n - 1) := by ring
      _ ≤ _ := hVupper

end MetaMathlibExt
