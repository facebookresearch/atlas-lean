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

/-- **Spaces of type (F) in Scottish Book Problem 26.** A real vector space $E$ with a topology
is of type (F) if there is a metric $d$ on $E$ that induces its topology, is translation
invariant, $d(x + z, y + z) = d(x, y)$ for all $x, y, z \in E$, and is complete, and if
addition $E \times E \to E$ and scalar multiplication $\mathbb{R} \times E \to E$ are
continuous. -/
def IsTypeF (E : Type) [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] : Prop :=
  ∃ d : E → E → ℝ, (∀ x y, 0 ≤ d x y) ∧ (∀ x y, d x y = 0 ↔ x = y) ∧
    (∀ x y, d x y = d y x) ∧ (∀ x y z, d x z ≤ d x y + d y z) ∧
    (∀ x y z, d (x + z) (y + z) = d x y) ∧
    (∀ U : Set E, IsOpen U ↔ ∀ x ∈ U, ∃ ε > 0, ∀ y, d y x < ε → y ∈ U) ∧
    (∀ x : ℕ → E, (∀ ε > 0, ∃ N, ∀ m n, m ≥ N → n ≥ N → d (x m) (x n) < ε) →
      ∃ y, ∀ ε > 0, ∃ N, ∀ n, n ≥ N → d (x n) y < ε) ∧
    Continuous (fun p : E × E => p.1 + p.2) ∧ Continuous fun p : ℝ × E => p.1 • p.2

/-- **Bounded sets in Scottish Book Problem 26.** Let $E$ be a real vector space with a topology.
A set $R \subseteq E$ is bounded if for every sequence $(x_n)_{n \ge 0}$ of points of $R$ and
every real sequence $(t_n)_{n \ge 0}$ with $t_n \to 0$, we have $t_n x_n \to 0$ in $E$.

This sequential definition is the one printed in the problem statement. -/
def IsBoundedSet (E : Type) [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (R : Set E) : Prop :=
  ∀ (x : ℕ → E) (t : ℕ → ℝ), (∀ n, x n ∈ R) →
    Filter.Tendsto t Filter.atTop (nhds 0) →
    Filter.Tendsto (fun n => t n • x n) Filter.atTop (nhds 0)

/-- **Spaces of type $\{F_o\}$.** A real vector space $E$ with a topology is of type $\{F_o\}$ if
it is of type (F) and, for every sequence $(x_n)_{n \ge 0}$ in $E$ with $x_n \to 0$ and every
real sequence $(t_n)_{n \ge 0}$ with $\sum_n |t_n| < \infty$, the series $\sum_n t_n x_n$
converges in $E$. -/
def IsTypeFo (E : Type) [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] : Prop :=
  IsTypeF E ∧ ∀ (x : ℕ → E) (t : ℕ → ℝ),
    Filter.Tendsto x Filter.atTop (nhds 0) → Summable (fun n => |t n|) →
    ∃ y, Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, t n • x n)
      Filter.atTop (nhds y)

/-- **Scottish Book Problem 26 (Mazur and Orlicz's claim).** The claim that for every real vector
space $E$ with a topology that is of type $\{F_o\}$ and every sequence $(F_n)_{n \ge 0}$ of
linear functionals $E \to \mathbb{R}$, if $F_n \to 0$ uniformly on every bounded set
$R \subseteq E$, then there is an open set $U \subseteq E$ containing $0$ on which
$F_n \to 0$ uniformly.

Here $F_n \to 0$ uniformly on a set $S$ means that for every $\varepsilon > 0$ there is $N$
with $|F_n(x)| < \varepsilon$ for all $n \ge N$ and all $x \in S$. The $F_n$ are only assumed
linear, not continuous. -/
def ScottishBookProblem26Claim : Prop :=
  ∀ (E : Type) [TopologicalSpace E] [AddCommGroup E] [Module ℝ E],
    IsTypeFo E →
    ∀ (F : ℕ → E →ₗ[ℝ] ℝ),
      (∀ R : Set E, IsBoundedSet E R →
        ∀ ε > 0, ∃ N, ∀ n, n ≥ N → ∀ x ∈ R, |F n x| < ε) →
      ∃ U : Set E, IsOpen U ∧ (0 : E) ∈ U ∧
        ∀ ε > 0, ∃ N, ∀ n, n ≥ N → ∀ x ∈ U, |F n x| < ε

/--
**Mazur and Orlicz's Problem 26 has a negative answer.** The claim of Scottish Book Problem 26
is false: there are a real vector space $E$ with a topology, of type $\{F_o\}$, and a sequence
$(F_n)_{n \ge 0}$ of linear functionals $E \to \mathbb{R}$ that converges to $0$ uniformly on
every bounded subset of $E$ but does not converge to $0$ uniformly on any open set containing
$0$.

Source: S. Mazur and
W. Orlicz, Problem 26 of the Scottish Book (prize: one small beer); the
typescript itself records the answer on the same page: "Ad 26, The answer is
negative. M. Eidelheit, June 4, 1938."
-/
theorem_wanted foBoundedUniformNeighborhood_refuted : ¬ ScottishBookProblem26Claim

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook26Wanted
