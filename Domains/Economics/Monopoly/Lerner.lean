/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

@[expose] public section

/-!
# The Lerner rule at an interior monopoly optimum

A monopolist with inverse demand `P` and cost `C` earns profit `x P(x) - C(x)` at output `x`. At an
interior local maximum `q > 0` where `P` and `C` are differentiable, Fermat's theorem
(`IsLocalMax.hasDerivAt_eq_zero`) gives marginal revenue `P(q) + q P'(q)` equal to marginal cost
`C'(q)`. With `P(q) > 0` and `P'(q) < 0`, the elasticity of demand in reciprocal-slope form
`ε = P(q) / (q P'(q))` is negative, and the markup satisfies the Lerner rule
`(P(q) - C'(q)) / P(q) = 1 / |ε|`. The formula for `ε` is the usual `(dq/dp)(p/q)` when demand
has a differentiable local inverse near `q`; the theorem does not need or assume one.

## Main results

* `lerner_of_isLocalMax`: the Lerner elasticity rule.

## References

* A. P. Lerner, "The concept of monopoly and the measurement of monopoly power", Review of
  Economic Studies 1 (1934), 157--175.
* A. Mas-Colell, M. D. Whinston and J. R. Green, *Microeconomic Theory*, Oxford University
  Press (1995), Section 12.B (monopoly pricing).
-/

namespace MathlibExt.Economics.Monopoly

/-- Price elasticity of demand at output `q` in reciprocal-slope form, from the inverse demand `P`
and a slope `P'`: `ε = P(q) / (q P')`. The definition imposes no relation between `P'` and `P`;
`lerner_of_isLocalMax` requires `HasDerivAt P P' q`. It equals the usual `(dq/dp) (p/q)` only
when demand has a local inverse `p ↦ q(p)` near `q` differentiable with derivative `1 / P'` (for
example, by the inverse function theorem when `P` is continuously differentiable near `q` with
`P' ≠ 0`); no such assumption is made here. -/
noncomputable def priceElasticity (P : ℝ → ℝ) (P' q : ℝ) : ℝ :=
  P q / (q * P')

/-- **Lerner rule.** If output `q > 0` locally maximizes the monopoly profit `x P(x) - C(x)`, the
inverse demand `P` and cost `C` are differentiable at `q` with `P'(q) < 0`, and the price
`P(q) > 0`, then the markup over marginal cost `C'(q)` satisfies
`(P(q) - C'(q)) / P(q) = 1 / |ε|`. -/
theorem lerner_of_isLocalMax {P C : ℝ → ℝ} {P' C' q : ℝ} (hP : HasDerivAt P P' q)
    (hC : HasDerivAt C C' q) (hmax : IsLocalMax (fun x => x * P x - C x) q) (hq : 0 < q)
    (hp : 0 < P q) (hP' : P' < 0) :
    (P q - C') / P q = 1 / |priceElasticity P P' q| := by
  have hderiv : HasDerivAt (fun x => x * P x - C x) (1 * P q + q * P' - C') q :=
    ((hasDerivAt_id' q).mul hP).sub hC
  have hFOC : 1 * P q + q * P' - C' = 0 := hmax.hasDerivAt_eq_zero hderiv
  have hqP' : q * P' < 0 := mul_neg_of_pos_of_neg hq hP'
  have hPq : P q ≠ 0 := ne_of_gt hp
  have hqP'ne : q * P' ≠ 0 := ne_of_lt hqP'
  have heps : priceElasticity P P' q < 0 := by
    unfold priceElasticity
    exact div_neg_of_pos_of_neg hp hqP'
  have habs : |priceElasticity P P' q| = -priceElasticity P P' q := abs_of_neg heps
  have hFOC' : P q - C' = -(q * P') := by linarith
  rw [habs]
  unfold priceElasticity
  rw [hFOC']
  field_simp

end MathlibExt.Economics.Monopoly
