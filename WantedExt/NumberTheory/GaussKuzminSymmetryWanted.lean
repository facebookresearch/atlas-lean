/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.ContinuedFractions.Computation.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

namespace MetaMathlibExt

@[expose] public section

open MeasureTheory Filter Topology Real

/-- **Convergent matrix.** For a finite string $a = (a_1, \ldots, a_n)$ of natural numbers, the
convergent matrix $C(a)$ is the $2 \times 2$ integer matrix given by the ordered product
$C(a) = \begin{pmatrix} 0 & 1 \\ 1 & a_1 \end{pmatrix} \cdots
\begin{pmatrix} 0 & 1 \\ 1 & a_n \end{pmatrix}$ (the identity matrix when $n = 0$). Its entries
are written $C(a) = \begin{pmatrix} p' & p \\ q' & q \end{pmatrix}$.

When $n \ge 1$ and all $a_i$ are positive, $p/q = [0; a_1, \ldots, a_n]$ and $p'/q'$ is the
preceding convergent.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Definition 2.1 and equation (2.8). -/
def convergentMatrix (a : List ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  (a.map fun t => !![0, 1; 1, (t : ℤ)]).prod

/-- **Convergent matrix of the empty string.** The convergent matrix of the empty string is the
$2 \times 2$ identity matrix.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Section 2.2. -/
theorem convergentMatrix_nil : convergentMatrix [] = 1 := rfl

/-- **Prepending a digit to a string.** For every natural number $t$ and every finite string $a$
of natural numbers, the convergent matrix of the string $(t, a)$, obtained by prepending $t$ to
$a$, is $C(t, a) = \begin{pmatrix} 0 & 1 \\ 1 & t \end{pmatrix} C(a)$.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
equation (2.8). -/
theorem convergentMatrix_cons (t : ℕ) (a : List ℕ) :
    convergentMatrix (t :: a) = !![0, 1; 1, (t : ℤ)] * convergentMatrix a := by
  simp [convergentMatrix]

/-- **Fundamental interval of a string.** For a finite string $a = (a_1, \ldots, a_n)$ of natural
numbers, the fundamental interval $I(a)$ is the set of real numbers $x \in [0, 1)$ whose
continued fraction expansion $x = [0; a_1(x), a_2(x), \ldots]$ has at least $n$ digits, with
$a_i(x) = a_i$ for $1 \le i \le n$.

The digits are those produced by the continued fraction algorithm, so a rational $x$ uses the
finite expansion whose last digit is at least $2$ (the resolution in the paper's footnote 2).

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
equation (1.4). -/
def cfCylinder (a : List ℕ) : Set ℝ :=
  {x | x ∈ Set.Ico 0 1 ∧
    ∀ i (hi : i < a.length), (GenContFract.of x).partDens.get? i = some (a[i] : ℝ)}

/-- **Fundamental interval of the empty string.** The fundamental interval of the empty string is
the whole interval: $I(()) = [0, 1)$.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
equation (1.4). -/
theorem cfCylinder_nil : cfCylinder [] = Set.Ico 0 1 := by
  ext x
  simp [cfCylinder]

/-- **Half-open interval between two reals.** For real numbers $\alpha$ and $\beta$, the interval
$\langle \alpha, \beta \rangle$ is $[\alpha, \beta)$ if $\alpha < \beta$, and $(\beta, \alpha]$
otherwise.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Section 2.3 (interval notation). -/
def fundInterval (α β : ℝ) : Set ℝ :=
  if α < β then Set.Ico α β else Set.Ioc β α

/-- **Half-open interval between increasing endpoints.** For real numbers $\alpha$ and $\beta$,
write $\langle \alpha, \beta \rangle$ for $[\alpha, \beta)$ if $\alpha < \beta$ and for
$(\beta, \alpha]$ otherwise. If $\alpha < \beta$, then
$\langle \alpha, \beta \rangle = [\alpha, \beta)$.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Section 2.3. -/
theorem fundInterval_of_lt {α β : ℝ} (h : α < β) : fundInterval α β = Set.Ico α β := by
  simp [fundInterval, h]

/-- **Gauss–Kuzmin mass of a string.** For a finite string $a$ of natural numbers with
fundamental interval $I(a)$, the Gauss–Kuzmin mass of $a$ is
$P_{GK}(a) = \frac{1}{\log 2} \int_{I(a)} \frac{dx}{1 + x}$, the measure of $I(a)$ under the
Gauss–Kuzmin measure with density $\frac{1}{(1 + x) \log 2}$.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
equations (1.5) and (1.6). -/
noncomputable def gaussKuzminMass (a : List ℕ) : ℝ :=
  (∫ x in cfCylinder a, 1 / (1 + x)) / log 2

/-- **Gauss–Kuzmin mass of the empty string.** The Gauss–Kuzmin mass of the empty string is
$P_{GK}(()) = \frac{1}{\log 2} \int_{[0, 1)} \frac{dx}{1 + x}$.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
equation (1.6). -/
theorem gaussKuzminMass_nil :
    gaussKuzminMass [] = (∫ x in Set.Ico (0 : ℝ) 1, 1 / (1 + x)) / log 2 := by
  rw [gaussKuzminMass, cfCylinder_nil]

/-- **Characteristic number of a string.** For a finite string $a$ of natural numbers with
convergent matrix $C(a) = \begin{pmatrix} p' & p \\ q' & q \end{pmatrix}$, the characteristic
number of $a$ is the integer $\chi(a) = (p + q)(q' + q)$.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Definition 5.1, equation (5.2). -/
def characteristicNumber (a : List ℕ) : ℤ :=
  (convergentMatrix a 0 1 + convergentMatrix a 1 1) *
    (convergentMatrix a 1 0 + convergentMatrix a 1 1)

/-- **Characteristic number of the empty string.** The characteristic number of the empty string
is $\chi(()) = 1$.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Definition 5.1. -/
theorem characteristicNumber_nil : characteristicNumber [] = 1 := by
  simp [characteristicNumber, convergentMatrix_nil]

/-- **Stable strings.** For a finite string $a = (a_1, \dots, a_n)$ of natural numbers, let
$M(t) = \begin{pmatrix} 0 & 1 \\ 1 & t \end{pmatrix}$ and write the convergent matrix of $a$ as

$$C(a) = M(a_1) M(a_2) \cdots M(a_n) = \begin{pmatrix} p' & p \\ q' & q \end{pmatrix},$$

computed over the integers, with the empty product equal to the identity matrix. The string $a$ is
stable if $p = 2q'$.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Definition 5.4, equation (5.9). -/
def IsStableString (a : List ℕ) : Prop :=
  convergentMatrix a 0 1 = 2 * convergentMatrix a 1 0

/-- **The empty string is stable.** The empty string is a stable string.

Its convergent matrix is the identity matrix, so its top-right entry $p$ and its bottom-left entry
$q'$ are both $0$, and $p = 2q'$ holds.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Definition 5.4. -/
theorem isStableString_nil : IsStableString [] := by
  simp [IsStableString, convergentMatrix_nil]

/-- **Nontrivial symmetry of a string.** A finite string $a$ of natural numbers has a nontrivial
symmetry if there is a string $b$ that is a rearrangement of $a$ (the same entries with the same
multiplicities, in some order) such that $b \ne a$, $b$ is not the reverse of $a$, and
$P_{GK}(b) = P_{GK}(a)$, where $P_{GK}$ denotes the Gauss–Kuzmin measure of a string.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Definition 1.4. -/
def HasNontrivialSymmetry (a : List ℕ) : Prop :=
  ∃ b : List ℕ, b.Perm a ∧ b ≠ a ∧ b ≠ a.reverse ∧ gaussKuzminMass b = gaussKuzminMass a

/-- The empty string has no nontrivial symmetry.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Definition 1.4. -/
theorem not_hasNontrivialSymmetry_nil : ¬ HasNontrivialSymmetry [] := by
  rintro ⟨b, hb, hne, -⟩
  exact hne (List.perm_nil.mp hb)

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

/-- **Convergent matrices of reversed and extended strings.** Let $a = (a_1, \ldots, a_n)$ be a
finite string of positive integers with convergent matrix
$C(a) = \begin{pmatrix} p' & p \\ q' & q \end{pmatrix}$, let $t \ge 1$ be an integer, and write
$\overleftarrow{a} = (a_n, \ldots, a_1)$ for the reversed string. Then
(i) $C(\overleftarrow{a}) = \begin{pmatrix} p' & q' \\ p & q \end{pmatrix}$;
(ii) $C(a_1, \ldots, a_n, t) = \begin{pmatrix} p & p' + tp \\ q & q' + tq \end{pmatrix}$;
(iii) $C(t, a_1, \ldots, a_n) = \begin{pmatrix} q' & q \\ p' + tq' & p + tq \end{pmatrix}$;
(iv) $C(t, a_n, \ldots, a_1) = \begin{pmatrix} p & q \\ p' + tp & q' + tq \end{pmatrix}$.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Lemma 2.2 (`integers-2025-A89-lem-2-2`). -/
public theorem_wanted convergentMatrix_reverse_append_cons (a : List ℕ) (ha : (∀ x ∈ a, 0 < x))
    (t : ℕ) (ht : 1 ≤ t) :
    convergentMatrix a.reverse = !![convergentMatrix a 0 0,
        convergentMatrix a 1 0; convergentMatrix a 0 1, convergentMatrix a 1 1] ∧
      convergentMatrix (a ++ [t]) = !![convergentMatrix a 0 1, convergentMatrix a 0 0 + t *
          convergentMatrix a 0 1; convergentMatrix a 1 1, convergentMatrix a 1 0 + t *
          convergentMatrix a 1 1] ∧
      convergentMatrix (t :: a) = !![convergentMatrix a 1 0,
          convergentMatrix a 1 1; convergentMatrix a 0 0 + t *
          convergentMatrix a 1 0, convergentMatrix a 0 1 + t * convergentMatrix a 1 1] ∧
      convergentMatrix (t :: a.reverse) =
        !![convergentMatrix a 0 1, convergentMatrix a 1 1; convergentMatrix a 0 0 + t *
            convergentMatrix a 0 1, convergentMatrix a 1 0 + t * convergentMatrix a 1 1]

/-- **Fundamental intervals of reversed and extended strings.** Let $a = (a_1, \ldots, a_n)$ be a
finite string of positive integers with convergent matrix
$C(a) = \begin{pmatrix} p' & p \\ q' & q \end{pmatrix}$, let $t \ge 1$ be an integer, write
$\overleftarrow{a} = (a_n, \ldots, a_1)$ for the reversed string, and for real numbers $x$ and $y$
let $\langle x, y \rangle$ be $[x, y)$ if $x < y$ and $(y, x]$ otherwise. Write $I(b)$ for the
fundamental interval of a string $b$, and set $u = (p' + tp)/(q' + tq)$, $v = q/(p + tq)$ and
$w = q/(q' + tq)$. Then each of the following equalities holds up to a set of Lebesgue measure
zero:
(i) $I(\overleftarrow{a}) = \langle q'/q, \; q'/q + (-1)^n / (q(p + q)) \rangle$;
(ii) $I(a_1, \ldots, a_n, t) = \langle u, \; u + (-1)^{n+1} / ((q' + tq)(q' + (t + 1)q)) \rangle$;
(iii) $I(t, a_1, \ldots, a_n) = \langle v, \; v + (-1)^{n+1} / ((p + tq)(p' + p + t(q' + q)))
\rangle$;
(iv) $I(t, a_n, \ldots, a_1) = \langle w, \; w + (-1)^{n+1} / ((q' + tq)(p' + q' + t(p + q)))
\rangle$.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Lemma 2.4 (`integers-2025-A89-lem-2-4`). -/
public theorem_wanted cfCylinder_reverse_append_cons_ae_eq (a : List ℕ) (ha : (∀ x ∈ a, 0 < x))
    (t : ℕ) (ht : 1 ≤ t) :
    cfCylinder a.reverse =ᵐ[volume]
        fundInterval ((convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ))
          ((convergentMatrix a 1 0 : ℝ) / (convergentMatrix a 1 1 : ℝ) + (-1) ^ a.length /
              ((convergentMatrix a 1 1 : ℝ) * ((convergentMatrix a 0 1 : ℝ) +
              (convergentMatrix a 1 1 : ℝ)))) ∧
      cfCylinder (a ++ [t]) =ᵐ[volume]
        fundInterval (((convergentMatrix a 0 0 : ℝ) + t * (convergentMatrix a 0 1 : ℝ)) /
            ((convergentMatrix a 1 0 : ℝ) + t * (convergentMatrix a 1 1 : ℝ)))
          (((convergentMatrix a 0 0 : ℝ) + t * (convergentMatrix a 0 1 : ℝ)) /
              ((convergentMatrix a 1 0 : ℝ) + t * (convergentMatrix a 1 1 : ℝ)) +
            (-1) ^ (a.length + 1) / (((convergentMatrix a 1 0 : ℝ) + t *
                (convergentMatrix a 1 1 : ℝ)) * ((convergentMatrix a 1 0 : ℝ) + (t + 1) *
                (convergentMatrix a 1 1 : ℝ)))) ∧
      cfCylinder (t :: a) =ᵐ[volume]
        fundInterval ((convergentMatrix a 1 1 : ℝ) / ((convergentMatrix a 0 1 : ℝ) + t *
            (convergentMatrix a 1 1 : ℝ)))
          ((convergentMatrix a 1 1 : ℝ) / ((convergentMatrix a 0 1 : ℝ) + t *
              (convergentMatrix a 1 1 : ℝ)) +
            (-1) ^ (a.length + 1) / (((convergentMatrix a 0 1 : ℝ) + t *
                (convergentMatrix a 1 1 : ℝ)) * ((convergentMatrix a 0 0 : ℝ) +
                (convergentMatrix a 0 1 : ℝ) + t * ((convergentMatrix a 1 0 : ℝ) +
                (convergentMatrix a 1 1 : ℝ))))) ∧
      cfCylinder (t :: a.reverse) =ᵐ[volume]
        fundInterval ((convergentMatrix a 1 1 : ℝ) / ((convergentMatrix a 1 0 : ℝ) + t *
            (convergentMatrix a 1 1 : ℝ)))
          ((convergentMatrix a 1 1 : ℝ) / ((convergentMatrix a 1 0 : ℝ) + t *
              (convergentMatrix a 1 1 : ℝ)) +
            (-1) ^ (a.length + 1) / (((convergentMatrix a 1 0 : ℝ) + t *
                (convergentMatrix a 1 1 : ℝ)) * ((convergentMatrix a 0 0 : ℝ) +
                (convergentMatrix a 1 0 : ℝ) + t * ((convergentMatrix a 0 1 : ℝ) +
                (convergentMatrix a 1 1 : ℝ)))))

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

/-- **Swapping the first two of three digits changes the characteristic number.** For positive
integers $a$, $b$, $c$ with $a \ne b$, the strings $(a, b, c)$ and $(b, a, c)$ have different
characteristic numbers: $\chi(a, b, c) \ne \chi(b, a, c)$.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Lemma 5.3 (`integers-2025-A89-lem-5-3`). -/
public theorem_wanted characteristicNumber_swap_ne (a b c : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hab : a ≠ b) :
    characteristicNumber [a, b, c] ≠ characteristicNumber [b, a, c]

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
