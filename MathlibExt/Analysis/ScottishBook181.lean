/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Order.Filter.AtTopBot.Interval
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Steinhaus's periodization problem

The difference between consecutive translates of the logistic sigmoid is positive. Its sum
over a finite integer interval telescopes, leaving the sigmoid at the two endpoints.
-/

public section

open Filter Real
open scoped Topology

namespace MathlibExt.Analysis.ScottishBook181Wanted

/--
**Steinhaus's periodization problem (Scottish Book Problem 181).** There is a continuous function
$f : \mathbb{R} \to \mathbb{R}$ with $f(x) > 0$ for every real $x$ such that, for every real $x$,
the series $\sum_{n \in \mathbb{Z}} f(x + n)$ converges and its sum is $1$.

Source:
H. Steinhaus, Problem 181 of the Scottish Book; the addendum Ad 181
records that the Gaussian `(1 / √π) exp (-x ^ 2)` does not have the
property, while Mazur's note gives a construction, taking a positive
continuous `g` with finite periodization and dividing `g` by that
periodization (e.g. `g(x) = exp (-x ^ 2)`). See the commentary in
R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem steinhaus181_periodization_one :
    ∃ f : ℝ → ℝ, Continuous f ∧ (∀ x, 0 < f x) ∧
      ∀ x, tsum (fun n : ℤ => f (x + (n : ℝ))) = 1 := by
  let f (x : ℝ) := sigmoid (x + 1) - sigmoid x
  have hpos (x : ℝ) : 0 < f x := sub_pos.mpr (sigmoid_strictMono (lt_add_one x))
  refine ⟨f, (continuous_sigmoid.comp (continuous_id.add_const 1)).sub continuous_sigmoid,
    hpos, fun x ↦ HasSum.tsum_eq ?_⟩
  -- Nonnegativity lets us compute the unordered sum on the cofinal intervals [-N, N).
  apply (tendsto_iff_tendsto_subseq_of_monotone
    (Finset.sum_mono_set_of_nonneg fun n : ℤ ↦ (hpos (x + n)).le) Finset.tendsto_Ico_neg).2
  have hsum (N : ℕ) : ∑ n ∈ Finset.Ico (-(N : ℤ)) N, f (x + n) =
      sigmoid (x + N) - sigmoid (x + -(N : ℝ)) := by
    simpa only [f, Int.cast_add, Int.cast_one, Int.cast_neg, Int.cast_natCast, ← add_assoc,
      neg_sub_neg] using Finset.sum_Ico_int_sub N (fun n : ℤ ↦ -sigmoid (x + n))
  have htop : Tendsto (fun N : ℕ ↦ sigmoid (x + N)) atTop (𝓝 1) :=
    tendsto_sigmoid_atTop.comp (tendsto_atTop_add_const_left _ x tendsto_natCast_atTop_atTop)
  have hbot : Tendsto (fun N : ℕ ↦ sigmoid (x + -(N : ℝ))) atTop (𝓝 0) :=
    tendsto_sigmoid_atBot.comp (tendsto_atBot_add_const_left _ x
      (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop))
  simpa only [Function.comp_def, hsum, sub_zero] using htop.sub hbot

end MathlibExt.Analysis.ScottishBook181Wanted
