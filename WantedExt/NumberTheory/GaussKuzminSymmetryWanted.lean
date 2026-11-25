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

/-- **Reversal symmetry forces the Gauss–Kuzmin density.** Let $f$ be a real function that is
continuous and nonnegative on $[0, 1]$ with $\int_0^1 f(x)\,dx = 1$, and let $S$ be an infinite
set of natural numbers. Write $I(a)$ for the fundamental interval of a string $a$ and
$\overleftarrow{a}$ for the reverse of $a$. If
$\int_{I(a)} f(x)\,dx = \int_{I(\overleftarrow{a})} f(x)\,dx$ for every string $a$ of positive
integers whose length lies in $S$, then $f(x) = \frac{1}{\log 2 \cdot (1 + x)}$ for every
$x \in [0, 1]$.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Theorem 1 (`integers-2025-A89-thm-1`). -/
public theorem_wanted density_eq_gaussKuzmin_of_reverse_symmetric (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc 0 1)) (hf0 : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f x)
    (hf1 : ∫ x in (0 : ℝ)..1, f x = 1) (S : Set ℕ) (hS : S.Infinite)
    (hsym : ∀ a : List ℕ, (∀ x ∈ a, 0 < x) → a.length ∈ S →
      ∫ x in cfCylinder a, f x = ∫ x in cfCylinder a.reverse, f x) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, f x = 1 / (log 2 * (1 + x))

/-- **Symmetry up to a fixed length does not force the Gauss–Kuzmin density.** Write $I(a)$ for
the fundamental interval of a string $a$ and $\overleftarrow{a}$ for the reverse of $a$. For every
integer $N \ge 1$ there is a real function $f$, continuous and nonnegative on $[0, 1]$ with
$\int_0^1 f(x)\,dx = 1$, such that $\int_{I(a)} f(x)\,dx = \int_{I(\overleftarrow{a})} f(x)\,dx$
for every string $a$ of positive integers of length at most $N$, but
$f(x) \ne \frac{1}{\log 2 \cdot (1 + x)}$ for some $x \in [0, 1]$.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Theorem 2 (`integers-2025-A89-thm-2`). -/
public theorem_wanted exists_reverse_symmetric_density_ne_gaussKuzmin (N : ℕ) (hN : 1 ≤ N) :
    ∃ f : ℝ → ℝ, ContinuousOn f (Set.Icc 0 1) ∧ (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f x) ∧
      ∫ x in (0 : ℝ)..1, f x = 1 ∧
      (∀ a : List ℕ, (∀ x ∈ a, 0 < x) → a.length ≤ N →
        ∫ x in cfCylinder a, f x = ∫ x in cfCylinder a.reverse, f x) ∧
      ∃ x ∈ Set.Icc (0 : ℝ) 1, f x ≠ 1 / (log 2 * (1 + x))

/-- **Explicit Gauss–Kuzmin mass of a string.** Let $a$ be a string of $n$ positive integers, let
$p$, $q'$ and $q$ be the upper-right, lower-left and lower-right entries of its convergent matrix
$C(a)$, and let $\overleftarrow{a}$ be the reverse of $a$. Then the Gauss–Kuzmin masses satisfy
$P_{GK}(a) = P_{GK}(\overleftarrow{a})$ and
$P_{GK}(a) = \left|\log_2\left(1 + \frac{(-1)^n}{(p + q)(q' + q)}\right)\right|$.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Lemma 2.5 (`integers-2025-A89-lem-2-5`), equation (2.13). -/
public theorem_wanted gaussKuzminMass_eq_abs_logb (a : List ℕ) (ha : (∀ x ∈ a, 0 < x)) :
    gaussKuzminMass a = gaussKuzminMass a.reverse ∧
      gaussKuzminMass a = |logb 2 (1 + (-1) ^ a.length / (((convergentMatrix a 0 1 : ℝ) +
          (convergentMatrix a 1 1 : ℝ)) * ((convergentMatrix a 1 0 : ℝ) +
          (convergentMatrix a 1 1 : ℝ))))|

/-- **Symmetric one-digit extensions fix the density at a rational point.** Let $f$ be a real
function that is continuous and nonnegative on $[0, 1]$ with $\int_0^1 f(x)\,dx = 1$. Let
$a = (a_1, \dots, a_n)$ be a string of positive integers, let $p$ and $q$ be the upper-right and
lower-right entries of its convergent matrix $C(a)$, so that $p/q = [0; a_1, \dots, a_n]$, and let
$\overleftarrow{a}$ be the reverse of $a$. Write $I(b)$ for the fundamental interval of a string
$b$, $(a, t)$ for $a$ followed by $t$, and $(t, \overleftarrow{a})$ for $t$ followed by
$\overleftarrow{a}$. If $\int_{I(a, t)} f(x)\,dx = \int_{I(t, \overleftarrow{a})} f(x)\,dx$ for
every integer $t \ge 1$, then $f(p/q) = f(0)/(1 + p/q)$.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Lemma 3.1 (`integers-2025-A89-lem-3-1`). -/
public theorem_wanted density_cfValue_eq_of_append_symmetric (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc 0 1)) (hf0 : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f x)
    (hf1 : ∫ x in (0 : ℝ)..1, f x = 1) (a : List ℕ) (ha : (∀ x ∈ a, 0 < x))
    (hsym : ∀ t : ℕ, 1 ≤ t →
      ∫ x in cfCylinder (a ++ [t]), f x = ∫ x in cfCylinder (t :: a.reverse), f x) :
    f ((convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ)) = f 0 / (1 +
        (convergentMatrix a 0 1 : ℝ) / (convergentMatrix a 1 1 : ℝ))

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

/-- **Gauss–Kuzmin masses agree exactly when characteristic numbers do.** Write $P_{GK}$ for the
Gauss–Kuzmin mass and $\chi$ for the characteristic number of a string. If $a$ and $b$ are strings
of positive integers whose lengths have the same parity, then $P_{GK}(a) = P_{GK}(b)$ if and only
if $\chi(a) = \chi(b)$.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Lemma 5.2 (`integers-2025-A89-lem-5-2`). -/
public theorem_wanted gaussKuzminMass_eq_iff_characteristicNumber_eq (a b : List ℕ)
    (ha : (∀ x ∈ a, 0 < x)) (hb : ∀ x ∈ b, 0 < x) (hpar : a.length % 2 = b.length % 2) :
    gaussKuzminMass a = gaussKuzminMass b ↔ characteristicNumber a = characteristicNumber b

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

/-- **Nontrivial symmetries from stable strings.** Let $n \ge 1$ and let $a = (a_1, \dots, a_n)$ be
a stable string of positive integers. Put $a^+ = (2, 1, a_1, \dots, a_{n-1}, a_n + 1)$ and
$\sigma(a^+) = (2, a_n + 1, a_{n-1}, \dots, a_1, 1)$. Then $\sigma(a^+)$ is a rearrangement of
$a^+$, it differs both from $a^+$ and from the reverse of $a^+$, and
$P_{GK}(\sigma(a^+)) = P_{GK}(a^+)$, where $P_{GK}$ denotes the Gauss–Kuzmin measure of a string.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Lemma 5.7 (`integers-2025-A89-lem-5-7`), equations (5.12) and (5.13). -/
public theorem_wanted stable_plus_nontrivial_symmetry (a : List ℕ) (ha : (∀ x ∈ a, 0 < x)) (h : a ≠
    [])
    (hst : IsStableString a) :
    let ap := 2 :: 1 :: (a.dropLast ++ [a.getLast h + 1])
    let sg := 2 :: (a.getLast h + 1) :: (a.dropLast.reverse ++ [1])
    sg.Perm ap ∧ sg ≠ ap ∧ sg ≠ ap.reverse ∧ gaussKuzminMass sg = gaussKuzminMass ap

/-- **No nontrivial symmetries in length three, infinitely many from length four.** (i) No string
of three positive integers has a nontrivial symmetry. (ii) For every $n \ge 4$ there are infinitely
many strings of $n$ positive integers that have a nontrivial symmetry.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Theorem 3 (`integers-2025-A89-thm-3`). -/
public theorem_wanted nontrivialSymmetry_length_three_and_infinite :
    (∀ a : List ℕ, (∀ x ∈ a, 0 < x) → a.length = 3 → ¬ HasNontrivialSymmetry a) ∧
      ∀ n : ℕ, 4 ≤ n →
        {a : List ℕ | a.length = n ∧ (∀ x ∈ a, 0 < x) ∧ HasNontrivialSymmetry a}.Infinite

end

end MetaMathlibExt
