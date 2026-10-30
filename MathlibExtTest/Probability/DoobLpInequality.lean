/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.DoobLpInequality

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal ProbabilityTheory

namespace MathlibExtTest.Probability.DoobLpInequality

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℝ}

/-- The general API restates with the exact public signature. -/
example (hmart : Martingale f ℱ μ) (hL2 : ∀ n, MemLp (f n) 2 μ) (n : ℕ) :
    ∫ ω, ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      fun k => |f k ω|) ^ 2 ∂μ ≤
    4 * ∫ ω, (f n ω) ^ 2 ∂μ :=
  hmart.doob_sq_maximal_ineq hL2 n

/-- The zero martingale satisfies the bound, with both sides `0`. -/
example (n : ℕ) :
    ∫ ω, ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      fun k => |(0 : ℕ → Ω → ℝ) k ω|) ^ 2 ∂μ ≤
    4 * ∫ ω, ((0 : ℕ → Ω → ℝ) n ω) ^ 2 ∂μ :=
  (martingale_zero ℝ ℱ μ).doob_sq_maximal_ineq (fun _ => MemLp.zero) n

/-- A constant martingale satisfies the bound, with both sides `c²` and `4c²`. -/
example (c : ℝ) (n : ℕ) :
    ∫ ω, ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      fun k => |(fun _ _ => c) k ω|) ^ 2 ∂μ ≤
    4 * ∫ ω, ((fun _ _ => c) n ω) ^ 2 ∂μ :=
  (martingale_const ℱ μ c).doob_sq_maximal_ineq (fun _ => memLp_const c) n

/-- The predictable quadratic variation of a constant process is `0`: all
increments vanish. This is why the book's `A`-form of the maximal inequality
needs the extra hypothesis `f 0 = 0` a.e. — for a nonzero constant
martingale, `A_n = 0` while the running maximum is `|c|`. -/
example (c : ℝ) (n : ℕ) :
    predictableQuadraticVariation μ ℱ (fun _ _ => c) n = 0 := by
  funext ω
  simp [predictableQuadraticVariation]

/-- The predictable quadratic variation at time `0` is `0` for any process:
the sum over `range 0` is empty. -/
example : predictableQuadraticVariation μ ℱ f 0 = 0 := by
  funext ω
  simp [predictableQuadraticVariation]

/-- The telescoping identity on the zero martingale: both sides are `0`. -/
example (n : ℕ) :
    ∫ ω, predictableQuadraticVariation μ ℱ (0 : ℕ → Ω → ℝ) n ω ∂μ =
      ∫ ω, ((0 : ℕ → Ω → ℝ) n ω) ^ 2 ∂μ - ∫ ω, ((0 : ℕ → Ω → ℝ) 0 ω) ^ 2 ∂μ :=
  (martingale_zero ℝ ℱ μ).integral_predictableQuadraticVariation (fun _ => MemLp.zero) n

/-- The `A`-form of the bound on the zero martingale, whose initial value is `0`. -/
example (n : ℕ) :
    ∫ ω, ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      fun k => |(0 : ℕ → Ω → ℝ) k ω|) ^ 2 ∂μ ≤
    4 * ∫ ω, predictableQuadraticVariation μ ℱ (0 : ℕ → Ω → ℝ) n ω ∂μ :=
  (martingale_zero ℝ ℱ μ).doob_sq_maximal_ineq_predictableQuadraticVariation
    (fun _ => MemLp.zero) (EventuallyEq.refl (ae μ) _) n

/-- The infinite-horizon `A`-form on the zero martingale. -/
example :
    ∫⁻ ω, ⨆ n, ENNReal.ofReal (|(0 : ℕ → Ω → ℝ) n ω| ^ 2) ∂μ ≤
      4 * ∫⁻ ω, ⨆ n, ENNReal.ofReal
        (predictableQuadraticVariation μ ℱ (0 : ℕ → Ω → ℝ) n ω) ∂μ :=
  (martingale_zero ℝ ℱ μ).doob_sq_maximal_ineq_iSup (fun _ => MemLp.zero)
    (EventuallyEq.refl (ae μ) _)

/-- Boundary case `n = 0`: the running maximum is just `|f 0|`. -/
example (ω : Ω) :
    ((Finset.range (0 + 1)).sup' Finset.nonempty_range_add_one
      fun k => |f k ω|) = |f 0 ω| := by
  apply le_antisymm
  · apply Finset.sup'_le Finset.nonempty_range_add_one (fun k => |f k ω|)
    intro k hk
    have hk0 : k = 0 := Nat.lt_one_iff.mp (Finset.mem_range.mp hk)
    rw [hk0]
  · exact Finset.le_sup' (fun k => |f k ω|) (Finset.mem_range.mpr (Nat.zero_lt_succ 0))

end MathlibExtTest.Probability.DoobLpInequality
