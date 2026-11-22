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

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook15Point1Wanted

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

/-- A "sphere" in the ray sense: every ray from the origin meets it exactly
once, in a positive multiple. -/
def IsSphere (E : Type) [AddCommGroup E] [Module ℝ E] (K : Set E) : Prop :=
  0 ∉ K ∧ ∀ x : E, x ≠ 0 → ∃! t : ℝ, 0 < t ∧ t • x ∈ K

/-- A set `R` is bounded if `t n → 0` and `x n ∈ R` imply `t n • x n → 0`,
as printed in the problem statement. -/
def IsBoundedSet (E : Type) [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (R : Set E) : Prop :=
  ∀ (x : ℕ → E) (t : ℕ → ℝ), (∀ n, x n ∈ R) →
    Filter.Tendsto t Filter.atTop (nhds 0) →
    Filter.Tendsto (fun n => t n • x n) Filter.atTop (nhds 0)

/-- The space has a norm inducing its topology and complete for that norm,
i.e. it is of type (B). -/
def AdmitsBanachNorm (E : Type) [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] : Prop :=
  ∃ normFn : E → ℝ, (∀ x, 0 ≤ normFn x) ∧ (∀ x, normFn x = 0 ↔ x = 0) ∧
    (∀ x y, normFn (x + y) ≤ normFn x + normFn y) ∧
    (∀ (a : ℝ) (x : E), normFn (a • x) = |a| * normFn x) ∧
    (∀ U : Set E, IsOpen U ↔ ∀ x ∈ U, ∃ ε > 0, ∀ y, normFn (y - x) < ε → y ∈ U) ∧
    (∀ x : ℕ → E, (∀ ε > 0, ∃ N, ∀ m n, m ≥ N → n ≥ N → normFn (x m - x n) < ε) →
      ∃ y, ∀ ε > 0, ∃ N, ∀ n, n ≥ N → normFn (x n - y) < ε)

/-- Mazur and Orlicz's Problem 15.1 from the Scottish Book: is every space
`E` of type (F) that possesses a bounded sphere necessarily of type (B)? -/
def ScottishBookProblem15Point1Claim : Prop :=
  ∀ (E : Type) [TopologicalSpace E] [AddCommGroup E] [Module ℝ E],
    IsTypeF E → (∃ K : Set E, IsSphere E K ∧ IsBoundedSet E K) → AdmitsBanachNorm E

/--
Problem 15.1 is false: the answer is negative. Source: S. Mazur and
W. Orlicz, Problem 15.1 of the Scottish Book; the typescript itself records
the negative answer (Ad 15.1, Mazur, May 1 1937) with the spaces `ℓ ^ p` and
`L ^ p` for `0 < p < 1`, with quasi-norm given by the sum (respectively
integral) of `|·| ^ p`, as counterexamples: they are of type (F), possess a
bounded sphere, and are not normable, hence not of type (B).
-/
theorem_wanted boundedSphereFImpliesB_refuted : ¬ ScottishBookProblem15Point1Claim

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook15Point1Wanted
