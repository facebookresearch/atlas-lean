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

/-- The sequence part of the claim of Problem 51: every pairwise-orthogonal
family of sequences is at most countable. Orthogonality means the series
`∑ n, f n * g n` converges to `0`. The zero sequence is excluded: it is
orthogonal to everything, so without this it would be a trivial member
of every family. -/
def SequenceSystemsAreCountable : Prop :=
  ∀ S : Set (ℕ → ℝ),
    (∀ f ∈ S, f ≠ 0) →
    (∀ f ∈ S, ∀ g ∈ S, f ≠ g →
      Summable (fun n => f n * g n) ∧ ∑' n, f n * g n = 0) →
    S.Countable

/-- The function part of the claim of Problem 51: every pairwise-orthogonal
family of measurable functions on `[0, 1]` is at most countable.
Orthogonality means the product is integrable with integral `0`. No
square-integrability is assumed. An orthogonal system is taken modulo
almost-everywhere equality: every member is nonzero a.e., and `S`
contains at most one representative of each a.e.-equality class. The
second clause is needed alongside orthogonality for a.e.-distinct pairs:
without it, uncountably many a.e.-equal copies of one function would
satisfy the orthogonality hypothesis vacuously. The singleton
indicators `δ_a` are excluded by the first clause, since each is zero
almost everywhere. -/
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
Mazur, Problem 51 of the Scottish Book. (a) Is every set of measurable
functions on `[0, 1]`, in which any two functions of the set are orthogonal,
at most countable? The functions are not assumed to be square-integrable.
(b) The analogous question for sequences: is every set of sequences in
which any two sequences of the set are orthogonal, meaning the sum over
`n` from `1` to infinity of `ξₙ ηₙ` equals `0`, at most countable? The
answer to both parts is no, stated as two separate negations:
Plichko and Razenkov construct a continuum-sized pairwise-orthogonal
family of sequences, and from it an uncountable orthogonal system of
functions on an interval. Orthogonal systems are taken with the
non-degeneracy in `FunctionSystemsAreCountable` / `SequenceSystemsAreCountable`:
nonzero elements modulo a.e. equality, so the singleton-indicator
family is not a trivial witness against the function part. The refutation
uses the absence of square-integrability: in `ℓ²` or `L²` an orthogonal
family is at most countable, since those spaces are separable Hilbert
spaces.
Source: S. Mazur, Problem 51 of the Scottish Book; A. M. Plichko and
V. Razenkov, On three problems from the Scottish Book connected with
orthogonal systems, Colloq. Math. 70 (1996), 227-234, Section 3; see the
commentary in R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser,
2015).
-/
theorem_wanted orthogonal_systems_not_necessarily_countable :
    ¬ SequenceSystemsAreCountable ∧ ¬ FunctionSystemsAreCountable

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook51Wanted
