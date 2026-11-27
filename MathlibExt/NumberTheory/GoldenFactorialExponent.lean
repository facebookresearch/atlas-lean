/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# Golden factorial exponent

We define the least positive exponent of the golden ratio bounding a factorial
and prove bounds on its increment from one factorial to the next.
-/

namespace MetaMathlibExt

open Real

@[expose] public section

/-- **Golden factorial exponent.** For a natural number $n$, the golden factorial exponent
$\alpha(n)$ is the least positive integer $m$ with $n! \le \varphi^m$, where $\varphi$ is the golden
ratio. This is the sequence OEIS A214048.

Equivalently $\alpha(n)$ is the positive integer $m$ with $\varphi^{m-1} \le n! \le \varphi^m$; the
number $n!$ is never a power of $\varphi$ for $n \ge 2$, and $\alpha(1) = 1$.

Source: Aleksandar Petojević, Marjana Gorjanac Ranitović, Dragan Rastovac and Milinko
Mandić, *The Golden Ratio, Factorials, and the Lambert W Function*, Journal of Integer
Sequences 27 (2024), Article 24.5.7, Section 2.2, definition (4). -/
public noncomputable def goldenFactorialExponent (n : ℕ) : ℕ :=
  sInf {m : ℕ | 1 ≤ m ∧ (n.factorial : ℝ) ≤ goldenRatio ^ m}

/-- **Every factorial is at most a positive power of the golden ratio.** Let $\varphi$ be the
golden ratio. For every natural number $n$ there is an integer $m \ge 1$ with $n! \le \varphi^m$.

Thus the set of positive integers $m$ with $n! \le \varphi^m$, whose least element is the
golden factorial exponent of $n$, is nonempty.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Section 2.2, definition (4). -/
public theorem exists_goldenRatio_pow_ge_factorial (n : ℕ) :
    ∃ m : ℕ, 1 ≤ m ∧ (n.factorial : ℝ) ≤ goldenRatio ^ m := by
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (n.factorial : ℝ) one_lt_goldenRatio
  refine ⟨max m 1, le_max_right _ _, hm.le.trans ?_⟩
  exact pow_le_pow_right₀ one_lt_goldenRatio.le (le_max_left _ _)

/-- **Defining property of the golden factorial exponent.** Let $\varphi$ be the golden ratio
and, for a natural number $n$, let $\alpha(n)$ be the least positive integer $m$ with
$n! \le \varphi^m$. For every natural number $n$, $\alpha(n) \ge 1$ and
$n! \le \varphi^{\alpha(n)}$.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Section 2.2, definition (4). -/
public theorem goldenFactorialExponent_mem (n : ℕ) :
    1 ≤ goldenFactorialExponent n ∧
      (n.factorial : ℝ) ≤ goldenRatio ^ goldenFactorialExponent n :=
  Nat.sInf_mem (s := .ofPred _) (exists_goldenRatio_pow_ge_factorial n)

/-- **Minimality of the golden factorial exponent.** Let $\varphi$ be the golden ratio and,
for a natural number $n$, let $\alpha(n)$ be the least positive integer $m$ with
$n! \le \varphi^m$. If $n$ and $m$ are natural numbers with $m \ge 1$ and $n! \le \varphi^m$,
then $\alpha(n) \le m$.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Section 2.2, definition (4). -/
public theorem goldenFactorialExponent_le {n m : ℕ} (hm : 1 ≤ m)
    (h : (n.factorial : ℝ) ≤ goldenRatio ^ m) : goldenFactorialExponent n ≤ m :=
  Nat.sInf_le ⟨hm, h⟩

/-- **Golden factorial exponent of $1$.** Let $\varphi$ be the golden ratio and, for a natural
number $n$, let $\alpha(n)$ be the least positive integer $m$ with $n! \le \varphi^m$. Then
$\alpha(1) = 1$.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Table 3. -/
public theorem goldenFactorialExponent_one : goldenFactorialExponent 1 = 1 :=
  le_antisymm (goldenFactorialExponent_le le_rfl (by simpa using one_lt_goldenRatio.le))
    (goldenFactorialExponent_mem 1).1

/-- **Golden factorial exponent of $2$.** Let $\varphi$ be the golden ratio and, for a natural
number $n$, let $\alpha(n)$ be the least positive integer $m$ with $n! \le \varphi^m$. Then
$\alpha(2) = 2$.

This holds because $\varphi < 2 \le \varphi^2 = \varphi + 1$.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Table 3. -/
public theorem goldenFactorialExponent_two : goldenFactorialExponent 2 = 2 := by
  have h2 : ((Nat.factorial 2 : ℕ) : ℝ) ≤ goldenRatio ^ 2 := by
    rw [goldenRatio_sq]
    norm_num [Nat.factorial]
    linarith [one_lt_goldenRatio]
  refine le_antisymm (goldenFactorialExponent_le (by norm_num) h2) ?_
  obtain ⟨h1, h⟩ := goldenFactorialExponent_mem 2
  by_contra hlt
  have hm1 : goldenFactorialExponent 2 = 1 := by omega
  rw [hm1] at h
  norm_num [Nat.factorial] at h
  linarith [goldenRatio_lt_two]

/-- **Increment bounds for the golden factorial exponent.** Let $\varphi$ be the golden ratio
and, for a natural number $n$, let $\alpha(n)$ be the least positive integer $m$ with
$n! \le \varphi^m$. For every natural number $n > 1$,
$$\alpha(n-1) + \lfloor \log_\varphi n \rfloor \le \alpha(n) \le
\alpha(n-1) + \lfloor \log_\varphi n \rfloor + 1.$$

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Lemma 2 (`jis-2024-24.5.7-lem-2`). -/
public theorem goldenFactorialExponent_succ_bounds (n : ℕ) (hn : 1 < n) :
    goldenFactorialExponent (n - 1) + ⌊Real.logb goldenRatio n⌋₊ ≤
        goldenFactorialExponent n ∧
      goldenFactorialExponent n ≤
        goldenFactorialExponent (n - 1) + ⌊Real.logb goldenRatio n⌋₊ + 1 := by
  let k : ℕ := ⌊Real.logb goldenRatio n⌋₊
  have hn_real : (1 : ℝ) < n := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < n := zero_lt_one.trans hn_real
  have hlog := Real.logb_nonneg one_lt_goldenRatio hn_real.le
  have hfloor : goldenRatio ^ k ≤ (n : ℝ) := by
    rw [← Real.rpow_natCast]
    exact (Real.le_logb_iff_rpow_le one_lt_goldenRatio hn_pos).mp (Nat.floor_le hlog)
  have hsucc : (n : ℝ) < goldenRatio ^ (k + 1) := by
    rw [← Real.rpow_natCast, Nat.cast_add, Nat.cast_one]
    exact (Real.logb_lt_iff_lt_rpow one_lt_goldenRatio hn_pos).mp (Nat.lt_floor_add_one _)
  have hfact : (n.factorial : ℝ) = (n : ℝ) * ((n - 1).factorial : ℝ) := by
    have hindex : n - 1 + 1 = n := by omega
    exact_mod_cast (show n.factorial = n * (n - 1).factorial by
      simpa only [hindex] using Nat.factorial_succ (n - 1))
  obtain ⟨hprev_pos, hprev⟩ := goldenFactorialExponent_mem (n - 1)
  refine ⟨?_, goldenFactorialExponent_le (by omega) ?_⟩
  · change goldenFactorialExponent (n - 1) + k ≤ goldenFactorialExponent n
    by_cases htwo : n = 2
    · have hsq : (n : ℝ) < goldenRatio ^ (2 : ℕ) := by
        rw [htwo, Nat.cast_ofNat, goldenRatio_sq]
        linarith [one_lt_goldenRatio]
      have hk : k < 2 := (pow_lt_pow_iff_right₀ one_lt_goldenRatio).mp (hfloor.trans_lt hsq)
      rw [htwo, show 2 - 1 = 1 by decide, goldenFactorialExponent_one,
        goldenFactorialExponent_two]
      omega
    · have hprev_large : 1 < goldenFactorialExponent (n - 1) := by
        have htwo_fact : ((2 : ℕ).factorial : ℝ) ≤ ((n - 1).factorial : ℝ) := by
          exact_mod_cast Nat.factorial_le (show 2 ≤ n - 1 by omega)
        have h := goldenFactorialExponent_le hprev_pos (htwo_fact.trans hprev)
        rwa [goldenFactorialExponent_two] at h
      have hprev_min : goldenRatio ^ (goldenFactorialExponent (n - 1) - 1) <
          ((n - 1).factorial : ℝ) := by
        by_contra! hle
        have := goldenFactorialExponent_le (by omega) hle
        omega
      have hlt_fact : goldenRatio ^ ((goldenFactorialExponent (n - 1) - 1) + k) <
          (n.factorial : ℝ) := by
        rw [pow_add, hfact, mul_comm (n : ℝ)]
        exact mul_lt_mul_of_lt_of_le_of_nonneg_of_pos hprev_min hfloor
          (pow_nonneg goldenRatio_pos.le _) hn_pos
      have hlt_exp := (pow_lt_pow_iff_right₀ one_lt_goldenRatio).mp
        (hlt_fact.trans_le (goldenFactorialExponent_mem n).2)
      omega
  · change (n.factorial : ℝ) ≤ goldenRatio ^ (goldenFactorialExponent (n - 1) + k + 1)
    rw [hfact, add_assoc, pow_add, mul_comm (n : ℝ)]
    exact mul_le_mul hprev hsucc.le hn_pos.le (pow_nonneg goldenRatio_pos.le _)

end

end MetaMathlibExt
