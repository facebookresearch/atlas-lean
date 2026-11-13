/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook51Wanted

/-- Restrict Lebesgue measure to `[0, 1]`, so functions on `[0, 1]` can be
integrated. Mathlib deliberately does not register this as a global instance
(other choices, e.g. the normalized restriction, are also natural); this
file supplies the restricted-Lebesgue instance for `[0, 1]` only. -/
noncomputable local instance scottishBook51MeasureSpace : MeasureTheory.MeasureSpace ↥(Set.Icc (0 : ℝ) 1) :=
  MeasureTheory.Measure.Subtype.measureSpace

/-- **Countability of orthogonal systems of sequences.** This is the statement that every set $S$
of real sequences $(f_n)_{n \in \mathbb{N}}$ with the following two properties is at most
countable: no member of $S$ is the zero sequence; and for any two distinct $f, g \in S$ the series
$\sum_{n} f_n g_n$ converges absolutely and its sum is $0$.

The zero sequence is excluded because it is orthogonal to everything, so without this it
would be a trivial member of every family. -/
def SequenceSystemsAreCountable : Prop :=
  ∀ S : Set (ℕ → ℝ),
    (∀ f ∈ S, f ≠ 0) →
    (∀ f ∈ S, ∀ g ∈ S, f ≠ g →
      Summable (fun n => f n * g n) ∧ ∑' n, f n * g n = 0) →
    S.Countable

/-- **Countability of orthogonal systems of functions.** Let $\lambda$ be Lebesgue measure on
$[0, 1]$. This is the statement that every set $S$ of functions $[0, 1] \to \mathbb{R}$ with the
following three properties is at most countable: no member of $S$ is $\lambda$-almost everywhere
equal to $0$; any two members of $S$ that are equal $\lambda$-almost everywhere are equal; and
any two members $f, g$ of $S$ that are not equal $\lambda$-almost everywhere are measurable, have
$\lambda$-integrable product $fg$, and satisfy $\int_{[0, 1]} f g \, d\lambda = 0$.

No square-integrability is assumed. Without the second property, uncountably many
almost-everywhere-equal copies of one function would satisfy the orthogonality condition
vacuously. The first property excludes the indicator functions of single points, each of which
is zero almost everywhere. -/
def FunctionSystemsAreCountable : Prop :=
  ∀ S : Set (↥(Set.Icc (0 : ℝ) 1) → ℝ),
    (∀ f ∈ S, ¬ (f =ᵐ[MeasureTheory.volume] 0)) →
    (∀ f ∈ S, ∀ g ∈ S, f =ᵐ[MeasureTheory.volume] g → f = g) →
    (∀ f ∈ S, ∀ g ∈ S, ¬ (f =ᵐ[MeasureTheory.volume] g) →
      Measurable f ∧ Measurable g ∧
      MeasureTheory.Integrable (fun x : ↥(Set.Icc (0 : ℝ) 1) => f x * g x) ∧
      MeasureTheory.integral MeasureTheory.volume
        (fun x : ↥(Set.Icc (0 : ℝ) 1) => f x * g x) = 0) →
    S.Countable

/--
**Orthogonal systems need not be countable.** Both of the following statements are false.
(a) Every set $S$ of real sequences $(f_n)_{n \in \mathbb{N}}$ in which no member is the zero
sequence, and in which for any two distinct $f, g \in S$ the series $\sum_n f_n g_n$ converges
absolutely with sum $0$, is at most countable. (b) Let $\lambda$ be Lebesgue measure on
$[0, 1]$. Every set $S$ of functions $[0, 1] \to \mathbb{R}$ in which no member is
$\lambda$-almost everywhere equal to $0$, no two distinct members are equal $\lambda$-almost
everywhere, and any two members $f, g$ that are not equal $\lambda$-almost everywhere are
measurable with $fg$ $\lambda$-integrable and $\int_{[0, 1]} f g \, d\lambda = 0$, is at most
countable.

This answers both parts of Mazur's Problem 51 of the Scottish Book in the negative: Plichko and
Razenkov construct a continuum-sized pairwise-orthogonal family of sequences, and from it an
uncountable orthogonal system of functions on an interval. No square-integrability is assumed;
in $\ell^2$ or $L^2$ an orthogonal family is at most countable, since those spaces are
separable Hilbert spaces.

Source: S. Mazur, Problem 51 of the Scottish Book; A. M. Plichko and
V. Razenkov, On three problems from the Scottish Book connected with
orthogonal systems, Colloq. Math. 70 (1996), 227-234, Section 3; see the
commentary in R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser,
2015).
-/
theorem_wanted orthogonal_systems_not_necessarily_countable :
    ¬ SequenceSystemsAreCountable ∧ ¬ FunctionSystemsAreCountable

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook51Wanted
