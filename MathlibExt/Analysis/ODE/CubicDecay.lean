/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Analysis/ODE/CubicDecay.lean` (leanprover/lean-eval,
https://github.com/leanprover/lean-eval), problem `cubic_decay_asymptotic`, at commit
38361be884302c7edce1908c4aef8296eb2cb27e (manifest `manifests/problems/cubic_decay_asymptotic.toml`,
rev 1, submitter Kim Morrison, status archived): the statement of `cubic_decay_asymptotic`, with
the docstring and comments it had in the former wanted module
`WantedExt/Analysis/CubicDecayWanted.lean`.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (the "License"); you may not use these portions
except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License
is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and limitations under
the License. lean-eval ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). Changes made: converted each
`@[eval_problem]` theorem into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with `Batteries.Util.ProofWanted`, inlined any
`LeanEval` helper modules, and placed the declarations in the
`MathlibExt.Analysis.CubicDecayWanted` namespace. Mathematical statements are unchanged.
Later changes (ATLAS, 2026): the docstring of `cubic_decay_asymptotic` was restated to match the
Lean statement; then the `theorem_wanted` was proved and moved from
`WantedExt/Analysis/CubicDecayWanted.lean` to this `MathlibExt` module with unchanged name,
statement and docstring, and the import of `Batteries.Util.ProofWanted` was dropped.

The rest of this file is new ATLAS work, not adapted from lean-eval: the proof of
`cubic_decay_asymptotic`, the private lemmas it uses, the module documentation and the linter
option.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Decay rate of solutions of `y' = -y³`

`cubic_decay_asymptotic`: if `y : ℝ → ℝ` has derivative `-(y t) ^ 3` at every `t > 0`, is
continuous at `0` within `[0, ∞)` and satisfies `y 0 = 1`, then `y t * √t → 1 / √2` as `t → ∞`.

## Proof outline

* The function `F t = (y t ^ 2 * (1 + 2 * t) - 1) ^ 2` is continuous on `[0, ∞)` and has
  derivative `-(4 * y t ^ 2 * (y t ^ 2 * (1 + 2 * t) - 1) ^ 2) ≤ 0` at every `t > 0`, so it is
  antitone on `[0, ∞)`. As `F 0 = 0` and `F ≥ 0`, `F` vanishes there:
  `y t ^ 2 * (1 + 2 * t) = 1` for every `t ≥ 0`. No uniqueness theorem for differential equations
  is needed.
* Hence `u t = y t * √(1 + 2 * t)` is continuous on the connected set `[0, ∞)` with `u t ^ 2 = 1`
  there and `u 0 = 1`, so `u = 1` on `[0, ∞)`: `y` is the explicit solution `1 / √(1 + 2 * t)`.
* For `t > 0`, `y t * √t = 1 / √(1 / t + 2)`, which tends to `1 / √2`.

## Implementation notes

The statement keeps the full name it had in the former wanted module, so the namespace still reads
`CubicDecayWanted` and repeats `Analysis`; the `dupNamespace` linter is turned off for this
declaration only.

## References

* Standard ODE textbook exercise. This is the source cited by problem `cubic_decay_asymptotic` of
  the lean-eval benchmark (leanprover/lean-eval), from which the statement is taken.
-/

@[expose] public section

namespace MathlibExt.Analysis.CubicDecayWanted
namespace Analysis
namespace ODE

/-!
Polynomial decay of `y' = -y³`.

The differential equation `y'(t) = -(y t)³` with `y 0 = 1` has the explicit solution
`y(t) = 1/√(1 + 2t)` on `[0, ∞)`. This benchmark asks for the asymptotic rate
`y t · √t → 1/√2` as `t → ∞`, given only the ODE and the initial condition.

The interesting content is not the explicit form (a hint) but the asymptotic statement:
the prover must combine an ODE hypothesis with a limit calculation. The ODE pins down `y`
uniquely on `[0, ∞)`, and the asymptotic follows from the closed form.
-/

open Filter Topology

open Set in
/-- A function with derivative `-(y t) ^ 3` at every `t > 0` that is continuous at `0` within
`[0, ∞)` is continuous on `[0, ∞)`. -/
private lemma continuousOn_Ici {y : ℝ → ℝ}
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Ici 0) 0) : ContinuousOn y (Ici 0) := fun t ht => by
  rcases (mem_Ici.1 ht).eq_or_lt with rfl | ht
  · exact hy_cont
  · exact (hy_diff t ht).continuousAt.continuousWithinAt

open Set in
/-- A solution of `y' = -y³` on `(0, ∞)` that is continuous at `0` within `[0, ∞)` with `y 0 = 1`
satisfies `y t ^ 2 * (1 + 2 * t) = 1` for every `t ≥ 0`: the function
`(y t ^ 2 * (1 + 2 * t) - 1) ^ 2` is antitone on `[0, ∞)` and vanishes at `0`. -/
private lemma sq_mul_one_add_two_mul_eq_one {y : ℝ → ℝ}
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Ici 0) 0) (hy0 : y 0 = 1) {t : ℝ} (ht : 0 ≤ t) :
    y t ^ 2 * (1 + 2 * t) = 1 := by
  have hyc := continuousOn_Ici hy_diff hy_cont
  have hF : AntitoneOn (fun s => (y s ^ 2 * (1 + 2 * s) - 1) ^ 2) (Ici 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0) (by fun_prop)
      (f' := fun s => -(4 * y s ^ 2 * (y s ^ 2 * (1 + 2 * s) - 1) ^ 2)) (fun s hs => ?_)
      fun s _ => neg_nonpos.2 (by positivity)
    rw [interior_Ici] at hs
    have hp : HasDerivAt (fun s => y s ^ 2) (2 * y s * (-(y s) ^ 3)) s := by
      simpa using (hy_diff s hs).fun_pow 2
    have hl : HasDerivAt (fun s : ℝ => 1 + 2 * s) 2 s := by
      simpa using ((hasDerivAt_id s).const_mul 2).const_add 1
    exact ((((hp.fun_mul hl).sub_const 1).fun_pow 2).congr_deriv (by ring)).hasDerivWithinAt
  have h := hF (mem_Ici.2 le_rfl) (mem_Ici.2 ht) ht
  norm_num [hy0] at h
  nlinarith [sq_nonneg (y t ^ 2 * (1 + 2 * t) - 1)]

open Set in
/-- Under the hypotheses of `cubic_decay_asymptotic`, `y t * √(1 + 2 * t) = 1` for every `t ≥ 0`,
that is, `y` is the explicit solution `1 / √(1 + 2 * t)` on `[0, ∞)`. -/
private lemma mul_sqrt_one_add_two_mul_eq_one {y : ℝ → ℝ}
    (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Ici 0) 0) (hy0 : y 0 = 1) {t : ℝ} (ht : 0 ≤ t) :
    y t * Real.sqrt (1 + 2 * t) = 1 := by
  have hyc := continuousOn_Ici hy_diff hy_cont
  have hu := isPreconnected_Ici.eq_one_or_eq_neg_one_of_sq_eq
    (f := fun s => y s * Real.sqrt (1 + 2 * s)) (by fun_prop) fun s (hs : 0 ≤ s) => by
      simp only [Pi.pow_apply, Pi.one_apply, mul_pow]
      rw [Real.sq_sqrt (by linarith)]
      exact sq_mul_one_add_two_mul_eq_one hy_diff hy_cont hy0 hs
  refine (hu.resolve_right fun h => ?_) (mem_Ici.2 ht)
  have h0 := h (mem_Ici.2 le_rfl)
  norm_num [hy0] at h0

/- Asymptotic decay rate for `y' = -y³, y(0) = 1`: the solution satisfies
`y t · √t → 1/√2` as `t → ∞`. -/
set_option linter.dupNamespace false in
/-- **Decay rate of solutions of $y' = -y^3$.** Let $y : \mathbb{R} \to \mathbb{R}$ be
differentiable at every $t > 0$ with $y'(t) = -y(t)^3$, continuous at $0$ within $[0, \infty)$,
and such that $y(0) = 1$. Then $y(t) \sqrt{t} \to 1/\sqrt{2}$ as $t \to \infty$.

Source: Standard ODE textbook exercise. Via leanprover/lean-eval@38361be, problem
`cubic_decay_asymptotic`. -/
theorem cubic_decay_asymptotic
    (y : ℝ → ℝ) (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0)
    (hy0 : y 0 = 1) :
    Tendsto (fun t : ℝ => y t * Real.sqrt t) atTop (𝓝 (1 / Real.sqrt 2)) := by
  have hlim : Tendsto (fun t : ℝ => 1 / Real.sqrt (1 / t + 2)) atTop (𝓝 (1 / Real.sqrt 2)) := by
    have h : Tendsto (fun t : ℝ => 1 / t + 2) atTop (𝓝 2) := by
      simpa only [one_div, zero_add] using tendsto_inv_atTop_zero.add_const (2 : ℝ)
    exact tendsto_const_nhds.div h.sqrt (by positivity)
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [div_eq_iff (by positivity), mul_assoc, ← Real.sqrt_mul ht.le,
    show t * (1 / t + 2) = 1 + 2 * t by field_simp]
  exact (mul_sqrt_one_add_two_mul_eq_one hy_diff hy_cont hy0 ht.le).symm

end ODE
end Analysis

end MathlibExt.Analysis.CubicDecayWanted
