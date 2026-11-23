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

/-- **Spaces of type (F).** A real vector space $E$ with a topology is of type (F) when addition
$E \times E \to E$ and scalar multiplication $\mathbb{R} \times E \to E$ are continuous and there
is a metric $d$ on $E$ that is translation invariant, $d(x + z, y + z) = d(x, y)$ for all
$x, y, z \in E$, that induces the topology of $E$, and that is complete: every Cauchy sequence
for $d$ converges for $d$. -/
def IsTypeF (E : Type) [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] : Prop :=
  ∃ d : E → E → ℝ, (∀ x y, 0 ≤ d x y) ∧ (∀ x y, d x y = 0 ↔ x = y) ∧
    (∀ x y, d x y = d y x) ∧ (∀ x y z, d x z ≤ d x y + d y z) ∧
    (∀ x y z, d (x + z) (y + z) = d x y) ∧
    (∀ U : Set E, IsOpen U ↔ ∀ x ∈ U, ∃ ε > 0, ∀ y, d y x < ε → y ∈ U) ∧
    (∀ x : ℕ → E, (∀ ε > 0, ∃ N, ∀ m n, m ≥ N → n ≥ N → d (x m) (x n) < ε) →
      ∃ y, ∀ ε > 0, ∃ N, ∀ n, n ≥ N → d (x n) y < ε) ∧
    Continuous (fun p : E × E => p.1 + p.2) ∧ Continuous fun p : ℝ × E => p.1 • p.2

/-- **Spheres in the ray sense.** Let $E$ be a real vector space. A set $K \subseteq E$ is a
sphere when $0 \notin K$ and for every $x \ne 0$ in $E$ there is exactly one real $t > 0$ with
$t x \in K$; that is, every open ray from the origin meets $K$ exactly once. -/
def IsSphere (E : Type) [AddCommGroup E] [Module ℝ E] (K : Set E) : Prop :=
  0 ∉ K ∧ ∀ x : E, x ≠ 0 → ∃! t : ℝ, 0 < t ∧ t • x ∈ K

/-- **Sequentially bounded sets.** Let $E$ be a real vector space with a topology. A set
$R \subseteq E$ is bounded when for every sequence $(x_n)$ of points of $R$ and every sequence
$(t_n)$ of real numbers with $t_n \to 0$, the sequence $(t_n x_n)$ tends to $0$ in $E$.

This is the definition of boundedness as printed in the statement of Scottish Book
Problem 15.1. -/
def IsBoundedSet (E : Type) [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    (R : Set E) : Prop :=
  ∀ (x : ℕ → E) (t : ℕ → ℝ), (∀ n, x n ∈ R) →
    Filter.Tendsto t Filter.atTop (nhds 0) →
    Filter.Tendsto (fun n => t n • x n) Filter.atTop (nhds 0)

/-- **Spaces of type (B).** A real vector space $E$ with a topology is of type (B) when there is
a function $\|\cdot\| : E \to \mathbb{R}$ with $\|x\| \ge 0$, with $\|x\| = 0$ exactly when
$x = 0$, with $\|x + y\| \le \|x\| + \|y\|$ and with $\|a x\| = |a| \, \|x\|$ for all
$x, y \in E$ and $a \in \mathbb{R}$, such that a set $U \subseteq E$ is open exactly when every
$x \in U$ has an $\varepsilon > 0$ with $y \in U$ whenever $\|y - x\| < \varepsilon$, and such
that every Cauchy sequence for $\|\cdot\|$ converges in $E$ for $\|\cdot\|$. -/
def AdmitsBanachNorm (E : Type) [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] : Prop :=
  ∃ normFn : E → ℝ, (∀ x, 0 ≤ normFn x) ∧ (∀ x, normFn x = 0 ↔ x = 0) ∧
    (∀ x y, normFn (x + y) ≤ normFn x + normFn y) ∧
    (∀ (a : ℝ) (x : E), normFn (a • x) = |a| * normFn x) ∧
    (∀ U : Set E, IsOpen U ↔ ∀ x ∈ U, ∃ ε > 0, ∀ y, normFn (y - x) < ε → y ∈ U) ∧
    (∀ x : ℕ → E, (∀ ε > 0, ∃ N, ∀ m n, m ≥ N → n ≥ N → normFn (x m - x n) < ε) →
      ∃ y, ∀ ε > 0, ∃ N, ∀ n, n ≥ N → normFn (x n - y) < ε)

/-- **Scottish Book Problem 15.1.** The claim of Mazur and Orlicz that every real vector space $E$
with a topology that is of type (F) and contains a bounded sphere is of type (B). -/
def ScottishBookProblem15Point1Claim : Prop :=
  ∀ (E : Type) [TopologicalSpace E] [AddCommGroup E] [Module ℝ E],
    IsTypeF E → (∃ K : Set E, IsSphere E K ∧ IsBoundedSet E K) → AdmitsBanachNorm E

/--
**Negative answer to Scottish Book Problem 15.1.** The Mazur–Orlicz claim of Problem 15.1 is
false: there is a real vector space $E$ with a topology that is of type (F) and contains a
bounded sphere, but is not of type (B).

Source: S. Mazur and
W. Orlicz, Problem 15.1 of the Scottish Book; the typescript itself records
the negative answer (Ad 15.1, Mazur, May 1 1937) with the spaces `ℓ ^ p` and
`L ^ p` for `0 < p < 1`, with quasi-norm given by the sum (respectively
integral) of `|·| ^ p`, as counterexamples: they are of type (F), possess a
bounded sphere, and are not normable, hence not of type (B).
-/
theorem_wanted boundedSphereFImpliesB_refuted : ¬ ScottishBookProblem15Point1Claim

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook15Point1Wanted
