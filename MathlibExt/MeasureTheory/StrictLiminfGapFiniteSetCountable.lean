/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_32.lean` (openbmb/ma-proofbench at commit
31bab4c78fd1b0c464e767d62e9202163d1e9029; L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation
of LLMs for Theorem Proving in Mathematical Analysis*, arXiv:2606.13782):
Copyright (c) 2026 OpenBMB.
Licensed under the MIT License:

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

Authors (of MA-ProofBench, as listed on arXiv:2606.13782): Lushi Pu, Weiming Zhang, Xinheng Xie,
Zixuan Fu, Bingxiang He, Hongya Lyu, Xin Li, Jie Zhou, Yudong Wang.

The adapted portion is the statement of `countable_setOf_lt_top_of_lt_liminf` and its docstring,
formerly the `theorem_wanted` of the same name in
`WantedExt/MeasureTheory/StrictLiminfGapFiniteSetCountableWanted.lean`, whose notice recorded
these changes from the source (which it described as byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench): converted `theorem ma_proofbench_l2_32 … := by sorry` into the Batteries
`theorem_wanted` `countable_setOf_lt_top_of_lt_liminf`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.StrictLiminfGapFiniteSetCountableWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system. Further changes in this file: the
`theorem_wanted` is now a `theorem` with a proof, and `public import Mathlib` is replaced by
narrower imports; the name, namespace, docstring and statement are unchanged.
-/

module

public import MathlibExt.Topology.Order.LocalExtr
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Strict liminf gaps at finite values

If `f a < liminf f (𝓝[≠] a)`, then every point near `a` other than `a` takes a value larger
than `f a`, so `a` is a strict local minimum of `f`. In a second-countable space the strict local
minima of any function form a countable set: a basic open set `U` on which `f` exceeds `f a`
away from `a` determines `a`, because a second point `b` of `U` with the same property would give
both `f a < f b` and `f b < f a`. For a function `f : [0, 1] → [0, ∞]` with a strict liminf gap
at every finite value, the set of finite values is therefore countable.

## Main results

* `countable_setOf_isStrictLocalMin`, `countable_setOf_isStrictLocalMax`: in a second-countable
  space, the strict local minima (maxima) of any function into a preorder form a countable set.
* `countable_setOf_lt_liminf`: for a function from a second-countable space to a complete linear
  order, the points `a` with `f a < liminf f (𝓝[≠] a)` form a countable set.
* `countable_setOf_lt_top_of_lt_liminf`: the MA-ProofBench statement for functions
  `[0, 1] → [0, ∞]`.
-/

public section

open Filter Topology TopologicalSpace

namespace MathlibExt.MeasureTheory.StrictLiminfGapFiniteSetCountableWanted

/-- **Strict local minima form a countable set.** Let $X$ be a second-countable topological
space, let $Y$ be a preordered set and let $f \colon X \to Y$ be any function. Then the set of
points $a \in X$ at which $f$ has a strict local minimum, that is, $f(a) < f(x)$ for all
$x \ne a$ in some neighborhood of $a$, is countable. -/
theorem countable_setOf_isStrictLocalMin {X Y : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [Preorder Y] (f : X → Y) :
    {a | IsStrictLocalMin f a}.Countable := by
  -- Each strict local minimum `a` has a basic open neighborhood on which `f` exceeds `f a`
  -- away from `a`, and such a basic open set contains at most one such point.
  have hcover : {a | IsStrictLocalMin f a} ⊆
      ⋃ U ∈ countableBasis X, {a | a ∈ U ∧ ∀ x ∈ U, x ≠ a → f a < f x} := by
    intro a ha
    obtain ⟨U, hUB, haU, hU⟩ :=
      (isBasis_countableBasis X).mem_nhds_iff.mp (eventually_nhdsWithin_iff.mp ha)
    exact Set.mem_biUnion hUB ⟨haU, fun x hx => hU hx⟩
  refine ((countable_countableBasis X).biUnion fun U _ => Set.Subsingleton.countable ?_).mono
    hcover
  rintro a ⟨haU, ha⟩ b ⟨hbU, hb⟩
  by_contra hab
  exact lt_asymm (ha b hbU (Ne.symm hab)) (hb a haU hab)

/-- **Strict local maxima form a countable set.** Let $X$ be a second-countable topological
space, let $Y$ be a preordered set and let $f \colon X \to Y$ be any function. Then the set of
points $a \in X$ at which $f$ has a strict local maximum, that is, $f(x) < f(a)$ for all
$x \ne a$ in some neighborhood of $a$, is countable. -/
theorem countable_setOf_isStrictLocalMax {X Y : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [Preorder Y] (f : X → Y) :
    {a | IsStrictLocalMax f a}.Countable :=
  countable_setOf_isStrictLocalMin (Y := Yᵒᵈ) (OrderDual.toDual ∘ f)

/-- **A strict liminf gap holds at only countably many points.** Let $X$ be a second-countable
topological space, let $Y$ be a complete linear order and let $f \colon X \to Y$ be any
function. Then the set of points $a \in X$ such that
$$f(a) < \liminf_{x \to a,\ x \ne a} f(x)$$
is countable: each such point is a strict local minimum of $f$. -/
theorem countable_setOf_lt_liminf {X Y : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [CompleteLinearOrder Y] (f : X → Y) :
    {a | f a < liminf f (𝓝[≠] a)}.Countable :=
  (countable_setOf_isStrictLocalMin f).mono fun _ ha => eventually_lt_of_lt_liminf ha

/-- **A strict liminf gap at every finite value forces countably many finite values.** Let
$f : [0,1] \to [0,\infty]$ be such that for every $y \in [0,1]$ with $f(y) \ne \infty$,
$$
\liminf_{x \to y,\ x \ne y} f(x) > f(y),
$$
where $x$ ranges over $[0,1]$. Then the set $\{y\in[0,1] : f(y) < \infty\}$ is countable.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Real functions; Functions of
one variable), `benchmark/level2/ma_proofbench_l2_32.lean` at openbmb/ma-proofbench@31bab4c.
-/
theorem countable_setOf_lt_top_of_lt_liminf
    (f : Set.Icc (0 : ℝ) 1 → ENNReal)
    (hgap : ∀ y : Set.Icc (0 : ℝ) 1,
      f y ≠ (⊤ : ENNReal) →
        Filter.liminf f (nhdsWithin y ({y}ᶜ)) > f y) :
    Set.Countable {y : Set.Icc (0 : ℝ) 1 | f y < (⊤ : ENNReal)} :=
  (countable_setOf_lt_liminf f).mono fun y hy => hgap y hy.ne

end MathlibExt.MeasureTheory.StrictLiminfGapFiniteSetCountableWanted
