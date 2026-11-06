/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Microscopic weightings of metric spaces
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.Order.Basic

@[expose] public section

namespace MathlibExt.Analysis.MicroscopicWeightingWanted

open Filter Matrix

noncomputable def similarityMatrix (X : Type*) [Fintype X] [MetricSpace X]
    (t : ℝ) : Matrix X X ℝ :=
  Matrix.of fun i j => Real.exp (-t * dist i j)

noncomputable def distanceMatrix (X : Type*) [Fintype X] [MetricSpace X] :
    Matrix X X ℝ :=
  Matrix.of fun i j => dist i j

noncomputable def weighting (X : Type*) [Fintype X] [DecidableEq X] [MetricSpace X]
    (t : ℝ) : X → ℝ :=
  (similarityMatrix X t)⁻¹ *ᵥ 1

def HasMicroscopicWeighting (X : Type*) [Fintype X] [DecidableEq X]
    [MetricSpace X] : Prop :=
  ∃ w : X → ℝ, Filter.Tendsto (weighting X) (nhdsWithin 0 (Set.Ioi 0)) (nhds w)

def IsGauging (X : Type*) [Fintype X] (M : Matrix X X ℝ) (g : X → ℝ)
    (c : ℝ) : Prop :=
  ∑ i, g i = 1 ∧ M *ᵥ g = Function.const X c

def HasFiniteConcentration (X : Type*) [Fintype X] (M : Matrix X X ℝ) : Prop :=
  ∃ g c, IsGauging X M g c

def microscopicWeightingIff : Prop :=
  ∀ (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X] [MetricSpace X],
    HasMicroscopicWeighting X ↔ HasFiniteConcentration X (distanceMatrix X)

/--
**Microscopic weighting is not equivalent to finite concentration.** It is not true that every
nonempty finite metric space $X$ has a microscopic weighting if and only if it has finite
concentration. Here, for real $t$, $Z_t$ is the $X \times X$ matrix with entries
$e^{-t\,d(x,y)}$ and $w_t = Z_t^{-1}\mathbf{1}$ is its weighting, where $\mathbf{1}$ is the
all-ones vector and the inverse of a singular matrix is taken to be $0$. The space $X$ has a
microscopic weighting if $w_t$ converges to some $w \colon X \to \mathbb{R}$ as $t \to 0^+$. It
has finite concentration if there are $g \colon X \to \mathbb{R}$ with $\sum_{x \in X} g(x) = 1$
and $c \in \mathbb{R}$ such that $\sum_{y \in X} d(x,y)\,g(y) = c$ for every $x \in X$.

Kenta Kitamura (assisted by ChatGPT) gave an explicit 10-point metric space with finite
concentration but no microscopic weighting.

Source: Kenta Kitamura, microscopic-weighting-counterexample, Lean formalization of the 10-point
counterexample,
https://github.com/KitaKen1/microscopic-weighting-counterexample/blob/eff8979/lean/MicroscopicWeightingCounterexampleFC.lean#L886-L894.
Moved from `OpenConjectures/Analysis/MicroscopicWeighting`.
-/
public theorem_wanted microscopicWeightingIff_refuted : ¬ microscopicWeightingIff

end MathlibExt.Analysis.MicroscopicWeightingWanted
