/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import MathlibExt.NumberTheory.GaussKuzminSymmetry
public import MathlibExt.NumberTheory.GaussKuzminFundamentalIntervals
public import MathlibExt.NumberTheory.GaussKuzminCharacterization
public import MathlibExt.NumberTheory.GaussKuzminSymmetryNontrivialSymmetryLengthThreeAndInfinite
public import MathlibExt.NumberTheory.GaussKuzminSymmetryStablePlusNontrivialSymmetry
public import MathlibExt.NumberTheory.GaussKuzminSymmetryExistsReverseSymmetricDensityNeGaussKuzmin

namespace MetaMathlibExt

@[expose] public section

open MeasureTheory Filter Topology Real

/-- **Generalized Gauss–Kuzmin theorem.** For a real number $x$, let $a_1(x), a_2(x), \dots$ be
the partial denominators of the continued fraction expansion of $x$. For almost every real $x$,
with respect to Lebesgue measure, the following holds: for every string $b = (b_1, \dots, b_n)$
of positive integers, the number of indices $i \in \{0, \dots, N - 1\}$ such that
$a_{i+j}(x) = b_j$ for all $j = 1, \dots, n$, divided by $N$, tends to the Gauss–Kuzmin measure
$P_{GK}(b)$ as $N \to \infty$.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Proposition 1.2 (`integers-2025-A89-prop-1-2`), quoted from Iosifescu and Kraaikamp,
Proposition 4.1.2. -/
public theorem_wanted gaussKuzmin_string_frequency :
    ∀ᵐ x : ℝ, ∀ a : List ℕ, (∀ x ∈ a, 0 < x) →
      Tendsto (fun N : ℕ =>
          (((Finset.range N).filter (fun i => ∀ j (hj : j < a.length),
              (GenContFract.of x).partDens.get? (i + j) = some (a[j] : ℝ))).card : ℝ) / N)
        atTop (𝓝 (gaussKuzminMass a))

/-- **Reversal symmetry of the Gauss–Kuzmin mass.** For every string $a$ of positive integers,
$P_{GK}(\overleftarrow{a}) = P_{GK}(a)$, where $P_{GK}$ is the Gauss–Kuzmin mass and
$\overleftarrow{a}$ is the reverse of $a$.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Proposition 1.3 (`integers-2025-A89-prop-1-3`), equations (1.8) and (1.9). -/
public theorem_wanted gaussKuzminMass_reverse (a : List ℕ) (ha : (∀ x ∈ a, 0 < x)) :
    gaussKuzminMass a.reverse = gaussKuzminMass a

/-- **Reversal symmetry from agreement with the Gauss–Kuzmin measure.** Let $\mu$ be a probability
measure on $\mathbb{R}$ and let $N \ge 1$. For a string $a$ of positive integers write $I(a)$ for
its fundamental interval, $P_{GK}(a)$ for its Gauss–Kuzmin measure and $a^{\mathrm{rev}}$ for its
reverse. If $\mu(I(a)) = P_{GK}(a)$ for every string $a$ of exactly $N$ positive integers, then
$\mu(I(a)) = \mu(I(a^{\mathrm{rev}}))$ for every string $a$ of at most $N$ positive integers.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Lemma 4.1 (`integers-2025-A89-lem-4-1`). -/
public theorem_wanted reverse_symmetric_of_eq_gaussKuzmin_at_length (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (N : ℕ) (hN : 1 ≤ N)
    (hμ : ∀ a : List ℕ, (∀ x ∈ a, 0 < x) → a.length = N →
      μ (cfCylinder a) = ENNReal.ofReal (gaussKuzminMass a)) :
    ∀ a : List ℕ, (∀ x ∈ a, 0 < x) → a.length ≤ N → μ (cfCylinder a) = μ (cfCylinder a.reverse)

/-- **Families of stable strings.** (i) For every positive integer $t$, the strings $(t, 2t)$ and
$(t, 1, 2t + 1)$ are stable. (ii) If $a = (a_1, \dots, a_m)$ is a stable string of positive
integers, then for every positive integer $t$ the string $(t, a_m, \dots, a_1, 2t)$, obtained from
the reverse of $a$ by adding $t$ at the front and $2t$ at the end, is stable. (iii) For every
$n \ge 2$ there are infinitely many stable strings of $n$ positive integers.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Lemma 5.5 (`integers-2025-A89-lem-5-5`). -/
public theorem_wanted isStableString_families :
    (∀ t : ℕ, 1 ≤ t → IsStableString [t, 2 * t] ∧ IsStableString [t, 1, 2 * t + 1]) ∧
      (∀ a : List ℕ, (∀ x ∈ a, 0 < x) → IsStableString a → ∀ t : ℕ, 1 ≤ t →
        IsStableString (t :: a.reverse ++ [2 * t])) ∧
      ∀ n : ℕ, 2 ≤ n →
        {a : List ℕ | a.length = n ∧ (∀ x ∈ a, 0 < x) ∧ IsStableString a}.Infinite

end

end MetaMathlibExt
