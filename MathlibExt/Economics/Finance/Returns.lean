/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Returns: compounding of gross returns, additivity of log returns

The simple gross return over one period is `grossReturn P₀ P₁ = P₁ / P₀`;
the log return is its logarithm. Gross returns compound multiplicatively over
two periods (`grossReturn_mul`) and telescope over a price path
(`grossReturn_prod_range`); log returns add over two periods on positive
prices (`logReturn_add`), and the total log return over many periods is the sum
of the per-period log returns (`totalLogReturn_eq_sum`, from `Real.log_prod`).

Domain notes: `grossReturn` and `logReturn` are total definitions in Mathlib
style. A zero terminal price is a total loss with the valid gross return
`grossReturn 100 0 = 0`, and `grossReturn_prod_range` allows it at the end of
the path. A zero initial price is different: there `grossReturn` is the junk
value `0` of Mathlib division by zero. The real-valued log return of a total
loss is undefined, so `logReturn 100 0 = Real.log 0 = 0` is a junk value, the
same as the unchanged-price value `logReturn 100 100`. A genuine log return
requires `0 < P₀` and `0 < P₁`; every theorem that interprets a logarithm as a
return assumes the corresponding positivity.

## Main results

* `MathlibExt.Economics.Finance.Returns.grossReturn_mul`
* `MathlibExt.Economics.Finance.Returns.grossReturn_prod_range`
* `MathlibExt.Economics.Finance.Returns.logReturn_add`
* `MathlibExt.Economics.Finance.Returns.totalLogReturn_eq_sum`

## References

OpenStax, *Principles of Finance*, rates of return. Atlas roadmap target
FI05.T01.
-/

@[expose] public section

namespace MathlibExt.Economics.Finance.Returns

/-- Simple gross return over one period: terminal price divided by initial price.
A zero terminal price is a valid total loss, `grossReturn 100 0 = 0`. Total: at
`P₀ = 0` this is the junk value `0` (Mathlib division by zero), not a return. -/
noncomputable def grossReturn (P₀ P₁ : ℝ) : ℝ := P₁ / P₀

/-- Log return over one period: the log of the gross return. The definition is
total: at nonpositive prices it returns a junk value, e.g.
`logReturn 100 0 = Real.log 0 = 0`, equal to the unchanged-price value
`logReturn 100 100`, although the gross return `grossReturn 100 0 = 0` of that
total loss is valid. A genuine log return requires `0 < P₀` and `0 < P₁`, as
assumed by `logReturn_add`. -/
noncomputable def logReturn (P₀ P₁ : ℝ) : ℝ := Real.log (grossReturn P₀ P₁)

/-- Compounded gross return over a finite set of periods with per-period gross
returns `G i`: the product of the per-period gross returns. -/
noncomputable def compoundedGross {ι : Type*} (G : ι → ℝ) (s : Finset ι) : ℝ :=
  ∏ i ∈ s, G i

/-- Total log return over a finite set of periods: the log of the compounded
gross return. -/
noncomputable def totalLogReturn {ι : Type*} (G : ι → ℝ) (s : Finset ι) : ℝ :=
  Real.log (compoundedGross G s)

/-- **Gross returns compound multiplicatively over two periods.** -/
theorem grossReturn_mul {P₀ P₁ P₂ : ℝ} (h₀ : P₀ ≠ 0) (h₁ : P₁ ≠ 0) :
    grossReturn P₀ P₂ = grossReturn P₀ P₁ * grossReturn P₁ P₂ := by
  unfold grossReturn
  field_simp

/-- **Gross returns telescope over a price path.** The product of the one-period
gross returns along `P 0, …, P n` is the gross return from `P 0` to `P n`.
Only the prices that appear as denominators, `P 0` and `P i` for `i < n`, need
to be nonzero: the terminal price `P n` may be zero (a total loss), and the
arbitrary continuation of `P` past `n` is unconstrained. -/
theorem grossReturn_prod_range {P : ℕ → ℝ} {n : ℕ} (h₀ : P 0 ≠ 0)
    (hP : ∀ i < n, P i ≠ 0) :
    ∏ i ∈ Finset.range n, grossReturn (P i) (P (i + 1)) = grossReturn (P 0) (P n) := by
  induction n with
  | zero =>
    simp [grossReturn, div_self h₀]
  | succ n ih =>
    rw [Finset.prod_range_succ _ n, ih (fun i hi => hP i (Nat.lt_succ_of_lt hi))]
    exact (grossReturn_mul h₀ (hP n (Nat.lt_succ_self n))).symm

/-- **Log returns add over two periods** on strictly positive prices. -/
theorem logReturn_add {P₀ P₁ P₂ : ℝ} (h₀ : 0 < P₀) (h₁ : 0 < P₁) (h₂ : 0 < P₂) :
    logReturn P₀ P₂ = logReturn P₀ P₁ + logReturn P₁ P₂ := by
  unfold logReturn
  rw [grossReturn_mul (ne_of_gt h₀) (ne_of_gt h₁)]
  exact Real.log_mul (div_ne_zero (ne_of_gt h₁) (ne_of_gt h₀))
    (div_ne_zero (ne_of_gt h₂) (ne_of_gt h₁))

/-- **The total log return is the sum of the per-period log returns** on strictly
positive gross returns. -/
theorem totalLogReturn_eq_sum {ι : Type*} {G : ι → ℝ} {s : Finset ι}
    (hG : ∀ i ∈ s, 0 < G i) :
    totalLogReturn G s = ∑ i ∈ s, Real.log (G i) := by
  unfold totalLogReturn compoundedGross
  exact Real.log_prod (fun i hi => ne_of_gt (hG i hi))

end MathlibExt.Economics.Finance.Returns
