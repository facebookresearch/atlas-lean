/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.LinearRecurrence
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Polynomial.Basic
public import MathlibExt.NumberTheory.Recurrences.CircuitArray

/-!
Statements from Evans and Hendel on recursions of the rows of the circuit array: Section 3
(annihilators). A polynomial `p = ∑ aᵢ Xⁱ` acts on a sequence `G : ℕ → K` through the translation
operator `E(G_s) = G_{s+1}` as `(p(E) G)_s = ∑ aᵢ G_{s+i}`.
-/

namespace MetaMathlibExt

@[expose] public section

open Polynomial

/-- **Annihilator of a sequence.** Let $K$ be a semiring, $p = \sum_i a_i X^i \in K[X]$ and
$G \colon \mathbb{N} \to K$ a sequence, and let $E$ be the translation operator
$E(G_s) = G_{s+1}$. The operator $p(E)$ annihilates $G$ when $\sum_i a_i G_{s+i} = 0$ for every
$s \ge 0$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Section 3 (definitions of the translation operator and of an annihilator). -/
def AnnihilatesSeq {K : Type*} [Semiring K] (p : K[X]) (G : ℕ → K) : Prop :=
  ∀ s : ℕ, p.sum (fun i a => a * G (s + i)) = 0

/-- **Every operator annihilates the zero sequence.** For every semiring $K$ and every polynomial
$p \in K[X]$, the operator $p(E)$ annihilates the zero sequence, where $E$ is the translation
operator $E(G_s) = G_{s+1}$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Section 3 (definition of an annihilator). -/
theorem annihilatesSeq_zero {K : Type*} [Semiring K] (p : K[X]) : AnnihilatesSeq p (0 : ℕ → K) := by
  intro s
  simp [Polynomial.sum]

/-- **The characteristic polynomial annihilates the solutions of its recurrence.** Let $K$ be a
field, $d \ge 0$ and $a_0, \dots, a_{d-1} \in K$. If a sequence $G \colon \mathbb{N} \to K$
satisfies $G_{n+d} = \sum_{i=0}^{d-1} a_i G_{n+i}$ for every $n \ge 0$, then the characteristic
polynomial $X^d - \sum_{i=0}^{d-1} a_i X^i$ of this recurrence annihilates $G$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Lemma 3.4 (`fq-2024-hendel08232024rev2-lem-3.4`). -/
public theorem_wanted annihilatesSeq_charPoly_of_isSolution {K : Type*} [Field K]
    (E : LinearRecurrence K) (G : ℕ → K) (hG : E.IsSolution G) :
    AnnihilatesSeq E.charPoly G

/-- **The operator $E - c$ annihilates the powers of $c$.** Let $K$ be a field, $c \in K$, and let
$E$ be the translation operator $E(G_s) = G_{s+1}$ on sequences $G \colon \mathbb{N} \to K$. Then
the operator $E - c$, that is, $p(E)$ for the polynomial $p = X - c \in K[X]$, annihilates the
sequence $s \mapsto c^s$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Lemma 3.7 (`fq-2024-hendel08232024rev2-lem-3.7`), part (i). -/
public theorem_wanted annihilatesSeq_X_sub_C_pow {K : Type*} [Field K] (c : K) :
    AnnihilatesSeq (X - C c) (fun s => c ^ s)

/-- **The Addition-Multiplication Lemma for annihilators.** Let $E$ be the translation operator
$E(G_s) = G_{s+1}$ on sequences. (i) Let $K$ be a field, $I$ a finite index set, and for each
$i \in I$ let $A_i \in K[X]$, $G_i \colon \mathbb{N} \to K$ and $c_i \in K$. If $A_i(E)$
annihilates $G_i$ for every $i \in I$, then $\prod_{i \in I} A_i(E)$ annihilates the sequence
$s \mapsto \sum_{i \in I} c_i G_i(s)$. (ii) Let $p_1, p_2 \in \mathbb{C}[X]$ be nonzero
polynomials and $G_1, G_2 \colon \mathbb{N} \to \mathbb{C}$ sequences such that $p_1(E)$
annihilates $G_1$ and $p_2(E)$ annihilates $G_2$. If $r_{1,1}, \dots, r_{1,m}$ and
$r_{2,1}, \dots, r_{2,n}$ are the complex roots of $p_1$ and $p_2$, listed with multiplicity,
then $\prod_{j=1}^{m} \prod_{j'=1}^{n} (E - r_{1,j} r_{2,j'})$ annihilates the termwise product
$s \mapsto G_1(s) G_2(s)$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Lemma 3.8 (`fq-2024-hendel08232024rev2-lem-3.8`); part (ii) quoted from Jarden. -/
public theorem_wanted annihilatesSeq_sum_prod_and_mul :
    (∀ {K : Type*} [Field K] {ι : Type*} (I : Finset ι) (A : ι → K[X]) (G : ι → ℕ → K)
        (c : ι → K), (∀ i ∈ I, AnnihilatesSeq (A i) (G i)) →
        AnnihilatesSeq (∏ i ∈ I, A i) (fun s => ∑ i ∈ I, c i * G i s)) ∧
      ∀ (p₁ p₂ : ℂ[X]) (G₁ G₂ : ℕ → ℂ), p₁ ≠ 0 → p₂ ≠ 0 →
        AnnihilatesSeq p₁ G₁ → AnnihilatesSeq p₂ G₂ →
        AnnihilatesSeq ((p₁.roots ×ˢ p₂.roots).map (fun r => X - C (r.1 * r.2))).prod
          (fun s => G₁ s * G₂ s)

/-! ### Section 2: the multivariable circuit array

The reduction of the triangular grid, the circuit array of a choice of boundary values, the circuit
array and the one-variable circuit array are defined in
`MathlibExt.NumberTheory.Recurrences.CircuitArray`. -/

/-- **Variables of the multivariable circuit array.** For a natural number $m$, $X_m$ is the
indeterminate $X_m$ regarded as an element of the field of fractions
$\mathbb{Q}(X_0, X_1, X_2, \dots)$ of the polynomial ring $\mathbb{Q}[X_0, X_1, X_2, \dots]$ in
countably many variables.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Definition 2.5 (the variables `X_i`). -/
noncomputable def circuitVar (m : ℕ) : FractionRing (MvPolynomial ℕ ℚ) :=
  algebraMap (MvPolynomial ℕ ℚ) (FractionRing (MvPolynomial ℕ ℚ)) (MvPolynomial.X m)

/-- **Multivariable circuit array.** Reduce the all-one triangular grid row by row as in Section 2,
and after the $m$-th reduction, for every $m \ge 1$, set every boundary edge (the left edges on the
first diagonal and the right edges on the last diagonal) to the variable $X_m$ of the field of
rational functions over $\mathbb{Q}$ in $X_0, X_1, \dots$. The multivariable circuit array
$C^M_{i,j}$ (Table 3) is the circuit array read off these grids: for $j \ge 1$ and
$0 \le i \le 2(j-1)$, it is the left edge for even $i$, or the right edge for odd $i$, of the
triangle in row $2j - 1$ and diagonal $j - \lfloor (i+1)/2 \rfloor$ of the $j$-times reduced
grid (other indices give junk values). In particular $C^M_{2(m-1),m} = X_m$ for every $m \ge 1$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Definition 2.5 and Table 3. -/
noncomputable def circuitArrayM (i j : ℕ) : FractionRing (MvPolynomial ℕ ℚ) :=
  circuitArrayOf (fun m => if m = 0 then none else some (circuitVar m)) i j

/-- **First entries of the left diagonal of the multivariable circuit array.** The multivariable
circuit array $C^M$, with values in the field of rational functions over $\mathbb{Q}$ in the
variables $X_0, X_1, \dots$, satisfies $C^M_{0,1} = X_1$ and $C^M_{2,2} = X_2$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Definition 2.5. -/
theorem circuitArrayM_diagonal :
    circuitArrayM 0 1 = circuitVar 1 ∧ circuitArrayM 2 2 = circuitVar 2 := by
  constructor <;> simp [circuitArrayM, circuitArrayOf, circuitGrid]

/-! ### Section 4 -/

/-- **Column recursion for the one-variable circuit array.** Extend the one-variable circuit array
$C^X$, with entries in the field $\mathbb{Q}(X)$ of rational functions over $\mathbb{Q}$, to integer
row indices by $C_{i,j} = C^X_{i,j}$ for $i \ge 0$ and $C_{i,j} = 1$ for $i < 0$. For an integer
$i$ and a natural number $j$, let $\tau_{i,j}$ be the triangle with left edge $C_{i,j}$ and right
and base edges $C_{i-1,j}$. Let $\mathcal{P}$, $\mathcal{L}$ and $\mathcal{R}$ be the
left-perimeter, left-edge and right-edge functions of the reduction. Then:
(i) $C_{2(c-1),c} = \mathcal{P}(\tau_{2(c-2),c-1}, \tau_{2(c-2),c-1})$ for every natural number
$c \ge 2$;
(ii) $C_{2(c-1),j} = \mathcal{L}(\tau_{2(c-1),j-1}, \tau_{2c-4,j-1}, \tau_{2c-4,j-1})$ for all
natural numbers $c$, $j$ with $2 \le c < j$;
(iii) $C_{2c-3,j} = \mathcal{R}(\tau_{2c-4,j-1}, \tau_{2c-6,j-1}, \tau_{2c-6,j-1})$ for all
natural numbers $c$, $j$ with $2 \le c \le j$;
(iv) $C^X_{0,1} = (X - 3)/X$.

Here $\mathcal{R}$ is the right-edge function of the reduction algorithm, not the misprinted
display (2.4), and the printed $C_{2(c-1-4),j-1}$ in (iii) is read as $C_{2(c-1)-4,j-1}$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Proposition 4.1 (`fq-2024-hendel08232024rev2-prop-4.1`). -/
public theorem_wanted circuitArrayX_inductive :
    let C : ℤ → ℕ → RatFunc ℚ := fun i j => if i < 0 then 1 else circuitArrayX i.toNat j
    let tri : ℤ → ℕ → CircuitEdge → RatFunc ℚ := fun i j e =>
      match e with
      | .left => C i j
      | .right => C (i - 1) j
      | .base => C (i - 1) j
    (∀ c : ℕ, 2 ≤ c →
        C (2 * ((c : ℤ) - 1)) c = circuitPerimeter (tri (2 * ((c : ℤ) - 2)) (c - 1))
          (tri (2 * ((c : ℤ) - 2)) (c - 1))) ∧
      (∀ c j : ℕ, 2 ≤ c → c < j →
        C (2 * ((c : ℤ) - 1)) j = circuitLeftEdge (tri (2 * ((c : ℤ) - 1)) (j - 1))
          (tri (2 * ((c : ℤ) - 1) - 2) (j - 1)) (tri (2 * ((c : ℤ) - 1) - 2) (j - 1))) ∧
      (∀ c j : ℕ, 2 ≤ c → c ≤ j →
        C (2 * ((c : ℤ) - 1) - 1) j = circuitRightEdge (tri (2 * ((c : ℤ) - 1) - 2) (j - 1))
          (tri (2 * ((c : ℤ) - 1) - 4) (j - 1)) (tri (2 * ((c : ℤ) - 1) - 4) (j - 1))) ∧
      circuitArrayX 0 1 = (RatFunc.X - 3) / RatFunc.X

/-- **Row one of the one-variable circuit array.** For every natural number $s \ge 2$, the
one-variable circuit array $C^X$, with entries in the field $\mathbb{Q}(X)$ of rational functions
over $\mathbb{Q}$, satisfies $C^X_{1,s} = (3 \cdot 9^{s-2} X - 1)/(3 \cdot 9^{s-2} X - 3)$.

The printed denominator $3 \cdot 9^{s-2} X$ is the row-zero formula; Table 2 has
$(3X - 1)/(3X - 3)$ at $s = 2$, which is $13/12$ at $X = 9$, not $26/27$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Corollary 4.5 (`fq-2024-hendel08232024rev2-cor-4.5`), denominator corrected from Table 2. -/
public theorem_wanted circuitArrayX_row_one (s : ℕ) (hs : 2 ≤ s) :
    circuitArrayX 1 s =
      (3 * 9 ^ ((s : ℤ) - 2) * RatFunc.X - 1) / (3 * 9 ^ ((s : ℤ) - 2) * RatFunc.X - 3)

/-- **Row two of the one-variable circuit array.** For every natural number $s \ge 2$, the
one-variable circuit array $C^X$, with entries in the field $\mathbb{Q}(X)$ of rational functions
over $\mathbb{Q}$, satisfies
$C^X_{2,s} = (c_{2,0}(s) - c_{2,1}(s) X + c_{2,2}(s) X^2)/(9^{s-2} X - 1)^2$, where
$c_{2,0}(s) = 27 \cdot 9^{s-3} - 1$, $c_{2,1}(s) = 24(2s - 3) \cdot 9^{s-3}$ and
$c_{2,2}(s) = 81 \cdot 81^{s-3} - 3 \cdot 9^{s-3}$, with integer exponents (so $9^{s-3} = 1/9$
and $81^{s-3} = 1/81$ when $s = 2$).

The printed $c_{2,2}(X^2)$ is read as $c_{2,2}(s) X^2$, as in Remark 4.7.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Corollary 4.6 (`fq-2024-hendel08232024rev2-cor-4.6`). -/
public theorem_wanted circuitArrayX_row_two (s : ℕ) (hs : 2 ≤ s) :
    circuitArrayX 2 s =
      ((27 * 9 ^ ((s : ℤ) - 3) - 1) - 24 * (2 * (s : RatFunc ℚ) - 3) * 9 ^ ((s : ℤ) - 3) * RatFunc.X +
          (81 * 81 ^ ((s : ℤ) - 3) - 3 * 9 ^ ((s : ℤ) - 3)) * RatFunc.X ^ 2) /
        (9 ^ ((s : ℤ) - 2) * RatFunc.X - 1) ^ 2

/-- **Row 0 of the multivariable circuit array.** Let $C^M$ be the multivariable circuit array, with
values in the field of rational functions over $\mathbb{Q}$ in the variables $X_0, X_1, \dots$.
For every integer $s \ge 1$, $C^M_{0,s} = (9^{s-1} - 1 + X_1)/9^{s-1}$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Corollary 4.8 (`fq-2024-hendel08232024rev2-cor-4.8`). -/
public theorem_wanted circuitArrayM_row_zero (s : ℕ) (hs : 1 ≤ s) :
    circuitArrayM 0 s = (9 ^ (s - 1) - 1 + circuitVar 1) / 9 ^ (s - 1)

/-- **Row 1 of the multivariable circuit array.** Let $C^M$ be the multivariable circuit array, with
values in the field of rational functions over $\mathbb{Q}$ in the variables $X_0, X_1, \dots$.
For every integer $s \ge 2$,
$C^M_{1,s} = (9^{s-1} - 1 + X_1)/\bigl(3(X_1 + 3 \cdot 9^{s-2} - 1)\bigr)$.

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Corollary 4.10 (`fq-2024-hendel08232024rev2-cor-4.10`). -/
public theorem_wanted circuitArrayM_row_one (s : ℕ) (hs : 2 ≤ s) :
    circuitArrayM 1 s = (9 ^ (s - 1) - 1 + circuitVar 1) / (3 * (circuitVar 1 + 3 * 9 ^ (s - 2) - 1))

/-- **Row 2 of the multivariable circuit array.** Let $C^M$ be the multivariable circuit array, with
values in the field of rational functions over $\mathbb{Q}$ in the variables $X_0, X_1, \dots$.
For every integer $s \ge 2$,
$$C^M_{2,s} = \frac{\sum_{i,j} c_{i,j}(s) X_1^i X_2^j}{(3 \cdot 9^{s-2} - 1 + X_1)^2},$$
where the sum runs over the six coefficients $c_{2,1}(s) = 9^{s-2}$, $c_{2,0}(s) = 9^{s-2} - 1$,
$c_{1,1}(s) = 4 \cdot 9^{s-2}$, $c_{1,0}(s) = 2 + (16(s-2) - 2) \cdot 9^{s-2}$,
$c_{0,1}(s) = 4 \cdot 9^{s-2}$ and
$c_{0,0}(s) = -1 + 9 \cdot 81^{s-2} - (8 + 16(s-2)) \cdot 9^{s-2}$.
Moreover, writing $E$ for the translation operator on rational sequences, the shifted coefficient
sequences $s \mapsto c_{i,j}(s+2)$, $s \ge 0$, are annihilated as in Table 4: $c_{0,0}$ by
$(E-81)(E-9)^2(E-1)$, $c_{0,1}$ by $(E-1)(E-9)$, $c_{1,0}$ by $(E-9)^2(E-1)$, $c_{1,1}$ by
$E-9$, $c_{2,0}$ by $(E-1)(E-9)$ and $c_{2,1}$ by $E-9$.

The paper's base case is $s = 3$; the identity also holds at $s = 2$. The recursions column of
Table 4 is omitted (its $X_1^0 X_2^1$ entry $G_s = 10G_{s-1} - G_{s-2}$ is misprinted for
$-9G_{s-2}$).

Source: Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the
Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2,
Corollary 4.12 (`fq-2024-hendel08232024rev2-cor-4.12`) and Table 4. -/
public theorem_wanted circuitArrayM_row_two :
    (∀ s : ℕ, 2 ≤ s →
      circuitArrayM 2 s =
        (9 ^ (s - 2) * circuitVar 1 ^ 2 * circuitVar 2 + (9 ^ (s - 2) - 1) * circuitVar 1 ^ 2 +
            4 * 9 ^ (s - 2) * circuitVar 1 * circuitVar 2 +
            (2 + (16 * ((s : FractionRing (MvPolynomial ℕ ℚ)) - 2) - 2) * 9 ^ (s - 2)) * circuitVar 1 +
            4 * 9 ^ (s - 2) * circuitVar 2 +
            (-1 + 9 * 81 ^ (s - 2) - (8 + 16 * ((s : FractionRing (MvPolynomial ℕ ℚ)) - 2)) * 9 ^ (s - 2))) /
          (3 * 9 ^ (s - 2) - 1 + circuitVar 1) ^ 2) ∧
      AnnihilatesSeq ((X - C 81) * (X - C 9) ^ 2 * (X - C 1))
        (fun s : ℕ => -1 + 9 * (81 : ℚ) ^ s - (8 + 16 * (s : ℚ)) * 9 ^ s) ∧
      AnnihilatesSeq ((X - C 1) * (X - C 9)) (fun s : ℕ => 4 * (9 : ℚ) ^ s) ∧
      AnnihilatesSeq ((X - C 9) ^ 2 * (X - C 1)) (fun s : ℕ => 2 + (16 * (s : ℚ) - 2) * 9 ^ s) ∧
      AnnihilatesSeq (X - C 9) (fun s : ℕ => 4 * (9 : ℚ) ^ s) ∧
      AnnihilatesSeq ((X - C 1) * (X - C 9)) (fun s : ℕ => (9 : ℚ) ^ s - 1) ∧
      AnnihilatesSeq (X - C 9) (fun s : ℕ => (9 : ℚ) ^ s)

end

end MetaMathlibExt
