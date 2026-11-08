/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook26Wanted

/-- A space of type (F): a complete topological vector space whose topology
is given by a complete translation-invariant metric. -/
def IsTypeF (E : Type) [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] : Prop :=
  ∃ d : E → E → ℝ, (∀ x y, 0 ≤ d x y) ∧ (∀ x y, d x y = 0 ↔ x = y) ∧
    (∀ x y, d x y = d y x) ∧ (∀ x y z, d x z ≤ d x y + d y z) ∧
    (∀ x y z, d (x + z) (y + z) = d x y) ∧
    (∀ U : Set E, IsOpen U ↔ ∀ x ∈ U, ∃ ε > 0, ∀ y, d y x < ε → y ∈ U) ∧
    (∀ x : ℕ → E, (∀ ε > 0, ∃ N, ∀ m n, m ≥ N → n ≥ N → d (x m) (x n) < ε) →
      ∃ y, ∀ ε > 0, ∃ N, ∀ n, n ≥ N → d (x n) y < ε) ∧
    Continuous (fun p : E × E => p.1 + p.2) ∧ Continuous fun p : ℝ × E => p.1 • p.2

/-- A set `R` is bounded if `t n → 0` and `x n ∈ R` imply `t n • x n → 0`,
as printed in the problem statement. -/
def IsBoundedSet (E : Type) [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (R : Set E) : Prop :=
  ∀ (x : ℕ → E) (t : ℕ → ℝ), (∀ n, x n ∈ R) →
    Filter.Tendsto t Filter.atTop (nhds 0) →
    Filter.Tendsto (fun n => t n • x n) Filter.atTop (nhds 0)

/-- A space of type `{F_o}`: a space of type (F) with the condition that if
`x n → 0` and `∑ |t n|` converges, then `∑ t n • x n` converges. -/
def IsTypeFo (E : Type) [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] : Prop :=
  IsTypeF E ∧ ∀ (x : ℕ → E) (t : ℕ → ℝ),
    Filter.Tendsto x Filter.atTop (nhds 0) → Summable (fun n => |t n|) →
    ∃ y, Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, t n • x n)
      Filter.atTop (nhds y)

/-- Mazur and Orlicz's Problem 26 from the Scottish Book: let `E` be a space
of type `{F_o}`, and let `F n` be a sequence of linear functionals on `E`
converging to zero uniformly on every bounded set `R` in `E`. Does the
sequence then converge to zero uniformly in some neighbourhood of zero? -/
def ScottishBookProblem26Claim : Prop :=
  ∀ (E : Type) [TopologicalSpace E] [AddCommGroup E] [Module ℝ E],
    IsTypeFo E →
    ∀ (F : ℕ → E →ₗ[ℝ] ℝ),
      (∀ R : Set E, IsBoundedSet E R →
        ∀ ε > 0, ∃ N, ∀ n, n ≥ N → ∀ x ∈ R, |F n x| < ε) →
      ∃ U : Set E, IsOpen U ∧ (0 : E) ∈ U ∧
        ∀ ε > 0, ∃ N, ∀ n, n ≥ N → ∀ x ∈ U, |F n x| < ε

/--
Problem 26 is false: the answer is negative. Source: S. Mazur and
W. Orlicz, Problem 26 of the Scottish Book (prize: one small beer); the
typescript itself records the answer on the same page: "Ad 26, The answer is
negative. M. Eidelheit, June 4, 1938."
-/
theorem_wanted foBoundedUniformNeighborhood_refuted : ¬ ScottishBookProblem26Claim

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook26Wanted
