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
Let `H` be an arbitrary set and `E` the set of all real-valued functions on
`H`, with pointwise convergence. Then every continuous linear functional `f`
on `E` has the form `f x = ∑ i, α i * x (t i)` for some finite list of
scalars `α i` and points `t i` in `H`. Continuity is for the pointwise
convergence (product) topology; this is the intended reading of the
typescript, whose statement prints no continuity hypothesis. Without
continuity the claim is false: the algebraic dual of `ℝ ^ H` is strictly
larger than the span of the evaluations when `H` is infinite. Source:
S. Banach and S. Mazur, Problem 10 of the Scottish Book, stated as a theorem
in the Scottish Book typescript.
-/
theorem_wanted continuousLinearFunctionalFiniteEvaluations :
    ∀ (H : Type) (f : (H → ℝ) →ₗ[ℝ] ℝ), Continuous f →
      ∃ (n : ℕ) (t : Fin n → H) (α : Fin n → ℝ), ∀ x : H → ℝ,
        f x = ∑ i, α i * x (t i)

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook10Wanted
