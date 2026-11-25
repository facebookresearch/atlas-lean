/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.ContinuedFractions.Computation.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Gauss–Kuzmin masses and characteristic numbers

This module defines the Gauss–Kuzmin mass and characteristic number of a digit string and
proves the matrix formulas for reversal and one-digit extensions. It also proves that swapping
the first two distinct digits of a positive triple changes its characteristic number.
-/

namespace MetaMathlibExt

@[expose] public section

open MeasureTheory Real

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

set_option linter.unusedVariables false in
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
theorem convergentMatrix_reverse_append_cons (a : List ℕ) (ha : (∀ x ∈ a, 0 < x))
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
            convergentMatrix a 0 1, convergentMatrix a 1 0 + t * convergentMatrix a 1 1] := by
  have happend (b : List ℕ) (s : ℕ) :
      convergentMatrix (b ++ [s]) = convergentMatrix b * !![0, 1; 1, (s : ℤ)] := by
    simp [convergentMatrix]
  have hrev (b : List ℕ) : convergentMatrix b.reverse = (convergentMatrix b).transpose := by
    induction b with
    | nil => simp [convergentMatrix_nil]
    | cons s b ih =>
      have hsym : !![0, 1; 1, (s : ℤ)].transpose = !![0, 1; 1, (s : ℤ)] := Matrix.eta_fin_two _
      rw [List.reverse_cons, happend, convergentMatrix_cons, Matrix.transpose_mul, hsym, ih]
  simp only [happend, convergentMatrix_cons, hrev]
  refine ⟨Matrix.eta_fin_two _, ?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

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
noncomputable def fundInterval (α β : ℝ) : Set ℝ :=
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

/-- **Swapping the first two of three digits changes the characteristic number.** For positive
integers $a$, $b$, $c$ with $a \ne b$, the strings $(a, b, c)$ and $(b, a, c)$ have different
characteristic numbers: $\chi(a, b, c) \ne \chi(b, a, c)$.

Source: Shreyas Singh, Zhuo Zhang and AJ Hildebrand, *An Elementary Characterization of the
Gauss-Kuzmin Measure in the Theory of Continued Fractions*, INTEGERS 25 (2025), Article A89,
Lemma 5.3 (`integers-2025-A89-lem-5-3`). -/
theorem characteristicNumber_swap_ne (a b c : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hab : a ≠ b) :
    characteristicNumber [a, b, c] ≠ characteristicNumber [b, a, c] := by
  intro heq
  let S := (a : ℤ) * b * c + a + b + c + 1
  let T := ((a : ℤ) - 1) * ((b : ℤ) - 1)
  -- Factoring the difference gives equation (5.7) after cancelling the unequal digits.
  have hfactor :
      ((b : ℤ) - a) * (((c : ℤ) - 2) * S - (c - 1) * (1 - T)) =
        characteristicNumber [a, b, c] - characteristicNumber [b, a, c] := by
    simp [characteristicNumber, convergentMatrix, S, T]
    ring
  rw [heq, sub_self] at hfactor
  have h := (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr (by exact_mod_cast hab.symm))
  have hS : (c : ℤ) - 1 < S := by
    dsimp [S]
    linarith [show 0 ≤ (a : ℤ) * b * c by positivity]
  obtain h₁ | h₂ | h₃ : c = 1 ∨ c = 2 ∨ 3 ≤ c := by omega
  · subst c
    norm_num at h
    omega
  · subst c
    have hT : T = 1 := by
      norm_num at h
      omega
    have := Int.eq_of_mul_eq_one hT
    omega
  · have hT : 0 ≤ T := mul_nonneg (by omega) (by omega)
    have hleft : S ≤ ((c : ℤ) - 2) * S := le_mul_of_one_le_left (by omega) (by omega)
    have hright : ((c : ℤ) - 1) * (1 - T) ≤ c - 1 :=
      mul_le_of_le_one_right (by omega) (by omega)
    omega

end

end MetaMathlibExt
