/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Analysis.SpecificLimits.Normed
import MathlibExt.NumberTheory.Recurrences.LucasBinetFormula
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # The k-Jacobsthal sequences and the limit of consecutive ratios -/

namespace MetaMathlibExt

@[expose] public section

/-- **Lucas parameters of the k-Jacobsthal numbers.** For a natural number $k$, the Lucas-sequence
parameters $(P, Q) = (k, -2)$. The Lucas sequences $J_{k,n} = U_n(k, -2)$ and
$j_{k,n} = V_n(k, -2)$ with these parameters are the $k$-Jacobsthal numbers ($J_{k,0} = 0$,
$J_{k,1} = 1$) and the $k$-Jacobsthal–Lucas numbers ($j_{k,0} = 2$, $j_{k,1} = k$); both satisfy
$x_{n+2} = k x_{n+1} + 2 x_n$.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Section 1, recurrences (1) and (2). -/
def kJacobsthalParams (k : ℕ) : LucasSequenceParams where
  p := k
  q := -2
  q_ne_zero := by decide

/-- **The second k-Jacobsthal number.** For every natural number $k$, the $k$-Jacobsthal number
$J_{k,2} = U_2(k, -2)$ equals $k$.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
proof of Theorem 2. -/
theorem lucasU_kJacobsthalParams_two (k : ℕ) : lucasU (kJacobsthalParams k) 2 = k := by
  simp [lucasU, kJacobsthalParams]

/-- **The $k$-Jacobsthal-Lucas number $j_{k,2}$.** For every natural number $k$, the
$k$-Jacobsthal-Lucas numbers $j_{k,n} = V_n(k, -2)$, the Lucas sequence $V$ with parameters
$(P, Q) = (k, -2)$, satisfy $j_{k,2} = k^2 + 4$.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
proof of Theorem 2. -/
theorem lucasV_kJacobsthalParams_two (k : ℕ) :
    lucasV (kJacobsthalParams k) 2 = (k : ℤ) ^ 2 + 4 := by
  simp [lucasV, kJacobsthalParams]
  ring

/-- **Companion $k$-Jacobsthal numbers.** For a natural number $k$ and integers $a, b$, the
companion $k$-Jacobsthal numbers $\mathcal{J}_{k,n}(a, b)$, $n \in \mathbb{N}$, are the integers
defined by $\mathcal{J}_{k,0}(a, b) = a$, $\mathcal{J}_{k,1}(a, b) = b$ and
$\mathcal{J}_{k,n+2}(a, b) = k\,\mathcal{J}_{k,n+1}(a, b) + 2\,\mathcal{J}_{k,n}(a, b)$.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Section 4. -/
def companionKJacobsthal (k : ℕ) (a b : ℤ) : ℕ → ℤ
  | 0 => a
  | 1 => b
  | n + 2 => k * companionKJacobsthal k a b (n + 1) + 2 * companionKJacobsthal k a b n

/-- **Recurrence of the companion $k$-Jacobsthal numbers.** For every natural number $k$, all
integers $a, b$ and every natural number $n$, the companion $k$-Jacobsthal numbers satisfy
$\mathcal{J}_{k,n+2}(a, b) = k\,\mathcal{J}_{k,n+1}(a, b) + 2\,\mathcal{J}_{k,n}(a, b)$.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Section 4. -/
theorem companionKJacobsthal_add_two (k : ℕ) (a b : ℤ) (n : ℕ) :
    companionKJacobsthal k a b (n + 2) =
      k * companionKJacobsthal k a b (n + 1) + 2 * companionKJacobsthal k a b n :=
  rfl

/-- **The second companion $k$-Jacobsthal number.** For every natural number $k$ and all integers
$a, b$, the companion $k$-Jacobsthal numbers satisfy $\mathcal{J}_{k,2}(a, b) = bk + 2a$.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Section 4, list of the first companion numbers. -/
theorem companionKJacobsthal_two (k : ℕ) (a b : ℤ) :
    companionKJacobsthal k a b 2 = b * k + 2 * a := by
  simp [companionKJacobsthal]
  ring

/-- **The $k$-Jacobsthal numbers as companion numbers.** For a natural number $k$, let
$\mathcal{J}_{k,n}(a, b)$ denote the companion $k$-Jacobsthal numbers and $J_{k,n} = U_n(k, -2)$
the $k$-Jacobsthal numbers, the Lucas sequence with parameters $(k, -2)$. Then for every natural
number $n$, $\mathcal{J}_{k,n}(0, 1) = J_{k,n}$: the companion numbers with initial values $0$ and
$1$ are the $k$-Jacobsthal numbers.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Section 4, special cases of the companion numbers. -/
theorem companionKJacobsthal_zero_one (k n : ℕ) :
    companionKJacobsthal k 0 1 n = lucasU (kJacobsthalParams k) n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih1 ih2 =>
      rw [companionKJacobsthal_add_two, ih1, ih2, lucasU_add_two]
      simp [kJacobsthalParams]

local notation "Δ[" k "]" => Real.sqrt ((k : ℝ) ^ 2 + 8)

/-- **Ratio of consecutive $k$-Jacobsthal numbers.** For every positive integer $k$, the
$k$-Jacobsthal numbers $J_{k,n} = U_n(k, -2)$, the Lucas sequence $U$ with parameters
$(P, Q) = (k, -2)$, satisfy $J_{k,n+1}/J_{k,n} \to (k + \sqrt{k^2 + 8})/2$ as $n \to \infty$,
the quotients taken in $\mathbb{R}$.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Theorem 8 (`integers-2025-A74-thm-8`). -/
theorem tendsto_lucasU_kJacobsthal_ratio (k : ℕ) (hk : 0 < k) :
    Filter.Tendsto
      (fun n : ℕ => (lucasU (kJacobsthalParams k) (n + 1) : ℝ) / lucasU (kJacobsthalParams k) n)
      Filter.atTop (nhds ((k + Δ[k]) / 2)) := by
  let α := ((k : ℝ) + Δ[k]) / 2
  let β := ((k : ℝ) - Δ[k]) / 2
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hΔ : 0 < Δ[k] := Real.sqrt_pos.2 (by positivity)
  have hα : 0 < α := by dsimp [α]; positivity
  have hβα : β < α := by dsimp [α, β]; linarith
  have hsum : α + β = ((kJacobsthalParams k).p : ℝ) := by
    simp [α, β, kJacobsthalParams]
    ring
  have hprod : α * β = ((kJacobsthalParams k).q : ℝ) := by
    simp [α, β, kJacobsthalParams]
    nlinarith [Real.sq_sqrt (show 0 ≤ (k : ℝ) ^ 2 + 8 by positivity)]
  have hbinet := (lucas_binet_formulas_of_field _ α β hsum hprod).1 hβα.ne'
  -- Factor out the dominant power in the Binet formula.
  have hterm (n : ℕ) : (lucasU (kJacobsthalParams k) n : ℝ) =
      α ^ n * (1 - (β / α) ^ n) / (α - β) := by
    have hn := pow_ne_zero n hα.ne'
    rw [(hbinet n).1, div_pow β α, one_sub_div hn, mul_div_cancel₀ _ hn]
  have hcontract : |β / α| < 1 := by
    rw [abs_div, abs_of_pos hα, div_lt_one hα, abs_lt]
    exact ⟨by dsimp [α, β]; linarith, hβα⟩
  have hlim : Filter.Tendsto (fun n : ℕ => 1 - (β / α) ^ n) Filter.atTop (nhds 1) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hcontract).const_sub 1
  have hratio := (hlim.comp (Filter.tendsto_add_atTop_nat 1)).div hlim one_ne_zero
  have hscaled := hratio.const_mul α
  rw [div_one, mul_one] at hscaled
  apply hscaled.congr
  intro n
  simp only [Pi.div_apply, Function.comp_apply, hterm, div_div_div_cancel_right₀
    (sub_ne_zero.mpr hβα.ne'), pow_succ α, mul_assoc,
    mul_div_mul_left _ _ (pow_ne_zero n hα.ne'), mul_div_assoc]

end

end MetaMathlibExt
