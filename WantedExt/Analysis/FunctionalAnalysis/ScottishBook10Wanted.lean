/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Topology.Constructions
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook10Wanted

/--
**Continuous linear functionals on the space of all real functions.** Let $H$ be a set and give
the space $\mathbb{R}^H$ of all real-valued functions on $H$ the topology of pointwise
convergence. Then for every continuous linear functional $f \colon \mathbb{R}^H \to \mathbb{R}$
there are a natural number $n$, points $t_1, \dots, t_n \in H$ and real numbers
$\alpha_1, \dots, \alpha_n$ such that $f(x) = \sum_{i=1}^n \alpha_i \, x(t_i)$ for every
$x \in \mathbb{R}^H$.

Continuity is the intended reading of the typescript, whose statement prints no continuity
hypothesis. Without continuity the claim is false: when $H$ is infinite, the algebraic dual of
$\mathbb{R}^H$ is strictly larger than the span of the evaluations.

Source:
S. Banach and S. Mazur, Problem 10 of the Scottish Book, stated as a theorem
in the Scottish Book typescript.
-/
theorem_wanted continuousLinearFunctionalFiniteEvaluations :
    ∀ (H : Type) (f : (H → ℝ) →ₗ[ℝ] ℝ), Continuous f →
      ∃ (n : ℕ) (t : Fin n → H) (α : Fin n → ℝ), ∀ x : H → ℝ,
        f x = ∑ i, α i * x (t i)

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook10Wanted
