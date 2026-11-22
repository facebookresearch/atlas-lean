/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic

/-!
# Dated cash flows and present value

A dated cash flow is `c : ℕ → ℝ`, the amount paid at integer date `t`, over a finite set
of payment dates `s : Finset ℕ`. Its present value under discount factors `D : ℕ → ℝ` is
`presentValue D s c = ∑ t ∈ s, D t * c t`. `D` is an arbitrary term structure; the constant
per-period rate `r` gives `discountFactor r t = ((1 + r) ^ t)⁻¹`. The definitions are total:
no sign condition on `r` or `D` is imposed, `discountFactor (-1) t = 0` for `t ≥ 1` is a junk
value, and results that need a genuine discount factor assume `1 + r ≠ 0` or `0 < 1 + r`.
Linearity below needs no such condition.

## Main results

* `MathlibExt.Economics.Finance.presentValue_add`, `presentValue_smul`: additivity and
  homogeneity in the cash flows (`Finset.sum_add_distrib`, `Finset.mul_sum`).
* `MathlibExt.Economics.Finance.presentValue_linear`: present value is linear in dated cash
  flows.

This file is the shared cash-flow interface for annuities, perpetuities, loan balances,
capital budgeting and the two-period household budget.

## References

OpenStax, *Principles of Finance*, time value of money; SOA Exam FM syllabus (rates and
annuities). Atlas roadmap target FI01.T01.
-/

@[expose] public section

namespace MathlibExt.Economics.Finance

/-- Constant-rate discount factor `(1 + r)⁻ᵗ` for a payment at integer date `t`
(source clause: "discount factor at per-period rate `r`"). The financial factor needs a
rate above `-1`; the definition is total in Mathlib style, and at `r = -1` it takes the
junk value `0` for `t ≥ 1` (`0⁻¹ = 0`). Results that use the factor as a discount assume
`1 + r ≠ 0` or `0 < 1 + r` explicitly. -/
noncomputable def discountFactor (r : ℝ) (t : ℕ) : ℝ :=
  ((1 + r) ^ t)⁻¹

/-- Present value of the dated cash flows `c t`, paid at the dates `t ∈ s`, under
the discount factors `D t` (source clause: "PV = Σ_t D_t c_t"). `D` is an
arbitrary term structure; `discountFactor r` is the constant-rate case. -/
noncomputable def presentValue (D : ℕ → ℝ) (s : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ t ∈ s, D t * c t

/-- Present value is additive in the cash flows. -/
theorem presentValue_add (D : ℕ → ℝ) (s : Finset ℕ) (c d : ℕ → ℝ) :
    presentValue D s (c + d) = presentValue D s c + presentValue D s d := by
  unfold presentValue
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- Present value is homogeneous in the cash flows. -/
theorem presentValue_smul (D : ℕ → ℝ) (s : Finset ℕ) (a : ℝ) (c : ℕ → ℝ) :
    presentValue D s (a • c) = a * presentValue D s c := by
  unfold presentValue
  simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ a _, ← Finset.mul_sum]

/-- Present value is linear in dated cash flows (Atlas roadmap FI01.T01). -/
theorem presentValue_linear (D : ℕ → ℝ) (s : Finset ℕ) (a b : ℝ) (c d : ℕ → ℝ) :
    presentValue D s (a • c + b • d) = a * presentValue D s c + b * presentValue D s d := by
  rw [presentValue_add, presentValue_smul, presentValue_smul]

end MathlibExt.Economics.Finance
