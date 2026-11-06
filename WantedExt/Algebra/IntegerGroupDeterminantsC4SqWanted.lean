/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
import Mathlib.RingTheory.Int.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.LinearAlgebra.Matrix.Circulant
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# Integer group determinants for `C₄ × C₄` (Yamaguchi–Yamaguchi)

Statements from Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants
for C_4^2*, INTEGERS 24 (2024), Article A30 (arXiv:2211.01597). Labels follow the
journal numbering (Corollaries 1–3, Lemmas 1–22, Theorem 1); the arXiv version
numbers the same statements 2.1, 2.3, 2.11, 2.5–2.10, 3.1–3.2, 4.1–4.7, 5.1–5.6,
6.1–6.3 and 1.1.

Conventions. The cyclic group `C₄` is `Fin 4` under addition, so `C₄²` is
`Fin 4 × Fin 4`. For an abelian group written additively the group matrix
`(x_{g h⁻¹})` is represented by `Matrix.circulant x`, whose entry `(g, h)` is `x (h - g)`:
it is the transpose of the group matrix, so the determinants agree. The paper's
variable `a_j`, `j = r + 4 s`, is `a (r, s)`. The paper's complex numbers
`α_i = d_i + √-1 d_{i+4}`, `β`, `γ` are Gaussian integers, and `β β̄`, `γ γ̄`
are their norms `Zsqrtd.norm`.
-/

namespace MetaMathlibExt

@[expose] public section

open Matrix

/-- **Integer group determinants.** For a finite group $G$, written additively and not
necessarily commutative, $S(G)$ is the set of integers $\det(x_{g - h})_{g, h \in G}$, where $x$
ranges over all functions $G \to \mathbb{Z}$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Section 1 (definition of `S(G)`). -/
public def integerGroupDeterminants (G : Type*) [AddGroup G] [Fintype G] [DecidableEq G] :
    Set ℤ :=
  Set.range fun x : G → ℤ => (circulant x).det

/-- **$1$ is an integer group determinant.** For every finite group $G$, written additively,
$1 \in S(G)$, where $S(G)$ is the set of integer group determinants of $G$: the indicator
function of the identity element gives the identity matrix.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Section 1 (definition of `S(G)`). -/
public theorem one_mem_integerGroupDeterminants (G : Type*) [AddGroup G] [Fintype G]
    [DecidableEq G] : (1 : ℤ) ∈ integerGroupDeterminants G :=
  ⟨Pi.single 0 1, by simp⟩

/-- **The group determinant of $C_4$.** For a commutative ring $R$ and
$x = (x_0, x_1, x_2, x_3) \in R^4$, $D_4(x_0, x_1, x_2, x_3)$ is the determinant of the
$4 \times 4$ circulant matrix whose $(i, j)$ entry is $x_{i - j}$, indices taken mod $4$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Section 2 (definition of `D_n`). -/
public def circulantDetFour {R : Type*} [CommRing R] (x : Fin 4 → R) : R :=
  (circulant x).det

/-- **The 4 × 4 circulant determinant of (1, 0, 0, 0).** Over every commutative ring $R$, the
$4 \times 4$ circulant determinant satisfies $D_4(1, 0, 0, 0) = 1$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Section 2 (definition of `D_n`). -/
public theorem circulantDetFour_single_one {R : Type*} [CommRing R] :
    circulantDetFour (Pi.single 0 1 : Fin 4 → R) = 1 := by
  simp [circulantDetFour]

/-- **The sums $b_i$.** For $a \colon \mathbb{Z}/4 \times \mathbb{Z}/4 \to \mathbb{Z}$ and
$i \in \mathbb{Z}/4$, $b_i = \bigl(a(i, 0) + a(i, 2)\bigr) + \bigl(a(i, 1) + a(i, 3)\bigr)$. In the
paper's indexing $a_{r + 4s} = a(r, s)$ this is $b_i = (a_i + a_{i+8}) + (a_{i+4} + a_{i+12})$
for $0 \le i \le 3$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Section 2 (notation after Corollary 2). -/
public def c4SqB (a : Fin 4 × Fin 4 → ℤ) (i : Fin 4) : ℤ :=
  a (i, 0) + a (i, 2) + (a (i, 1) + a (i, 3))

/-- **The alternating sums $c_i$.** For $a \colon \mathbb{Z}/4 \times \mathbb{Z}/4 \to \mathbb{Z}$
and $i \in \mathbb{Z}/4$, $c_i = \bigl(a(i, 0) + a(i, 2)\bigr) - \bigl(a(i, 1) + a(i, 3)\bigr)$. In
the paper's indexing $a_{r + 4s} = a(r, s)$ this is $c_i = (a_i + a_{i+8}) - (a_{i+4} + a_{i+12})$
for $0 \le i \le 3$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Section 2 (notation after Corollary 2). -/
public def c4SqC (a : Fin 4 × Fin 4 → ℤ) (i : Fin 4) : ℤ :=
  a (i, 0) + a (i, 2) - (a (i, 1) + a (i, 3))

/-- **The differences $d_i$ of a function on $C_4^2$.** For
$a \colon \mathbb{Z}/4 \times \mathbb{Z}/4 \to \mathbb{Z}$, the integers $d_0, \dots, d_7$ are
$d_i = a(i, 0) - a(i, 2)$ and $d_{i+4} = a(i, 1) - a(i, 3)$ for $0 \le i \le 3$. Writing
$a_{r + 4s}$ for $a(r, s)$, this is the paper's $d_i = a_i - a_{i+8}$ for $0 \le i \le 7$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Section 2 (notation after Corollary 2). -/
public def c4SqD (a : Fin 4 × Fin 4 → ℤ) : Fin 8 → ℤ :=
  ![a (0, 0) - a (0, 2), a (1, 0) - a (1, 2), a (2, 0) - a (2, 2), a (3, 0) - a (3, 2),
    a (0, 1) - a (0, 3), a (1, 1) - a (1, 3), a (2, 1) - a (2, 3), a (3, 1) - a (3, 3)]

/-- **The Gaussian integers $\alpha_i$.** For
$a \colon \mathbb{Z}/4 \times \mathbb{Z}/4 \to \mathbb{Z}$ with differences $d_0, \dots, d_7$ (so
$d_i = a(i, 0) - a(i, 2)$ and $d_{i+4} = a(i, 1) - a(i, 3)$ for $0 \le i \le 3$), the Gaussian
integers $\alpha_0, \dots, \alpha_3 \in \mathbb{Z}[\sqrt{-1}]$ are
$\alpha_i = d_i + d_{i+4} \sqrt{-1}$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Section 2 (notation after Corollary 2). -/
public def c4SqAlpha (a : Fin 4 × Fin 4 → ℤ) : Fin 4 → GaussianInt :=
  ![⟨c4SqD a 0, c4SqD a 4⟩, ⟨c4SqD a 1, c4SqD a 5⟩, ⟨c4SqD a 2, c4SqD a 6⟩,
    ⟨c4SqD a 3, c4SqD a 7⟩]

/-- **The Gaussian integer $\beta$.** For $a \colon \mathbb{Z}/4 \times \mathbb{Z}/4 \to \mathbb{Z}$
with Gaussian integers $\alpha_0, \dots, \alpha_3$,
$\beta = (\alpha_0 + \alpha_2)^2 - (\alpha_1 + \alpha_3)^2 \in \mathbb{Z}[\sqrt{-1}]$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Section 2 (definition before Lemma 1). -/
public def c4SqBeta (a : Fin 4 × Fin 4 → ℤ) : GaussianInt :=
  (c4SqAlpha a 0 + c4SqAlpha a 2) ^ 2 - (c4SqAlpha a 1 + c4SqAlpha a 3) ^ 2

/-- **The Gaussian integer $\gamma$ of a function on $C_4^2$.** For
$a \colon \mathbb{Z}/4 \times \mathbb{Z}/4 \to \mathbb{Z}$, let
$\alpha_i = (a(i, 0) - a(i, 2)) + (a(i, 1) - a(i, 3))\sqrt{-1} \in \mathbb{Z}[\sqrt{-1}]$
for $0 \le i \le 3$. Then
$\gamma = (\alpha_0 - \alpha_2)^2 + (\alpha_1 - \alpha_3)^2 \in \mathbb{Z}[\sqrt{-1}]$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Section 2 (definition before Lemma 1). -/
public def c4SqGamma (a : Fin 4 × Fin 4 → ℤ) : GaussianInt :=
  (c4SqAlpha a 0 - c4SqAlpha a 2) ^ 2 + (c4SqAlpha a 1 - c4SqAlpha a 3) ^ 2

/-- **The C₄² notation at the indicator of the identity.** Let $\delta$ be the integer-valued
function on $C_4^2 = \mathbb{Z}/4 \times \mathbb{Z}/4$ that is $1$ at $(0, 0)$ and $0$ elsewhere.
For $a = \delta$ the associated integers are $b = c = (1, 0, 0, 0)$ and
$d = (1, 0, 0, 0, 0, 0, 0, 0)$, and the associated Gaussian integers are $\beta = \gamma = 1$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Section 2 (notation after Corollary 2). -/
public theorem c4Sq_notation_single :
    c4SqB (Pi.single (0, 0) 1) = Pi.single 0 1 ∧ c4SqC (Pi.single (0, 0) 1) = Pi.single 0 1 ∧
      c4SqD (Pi.single (0, 0) 1) = Pi.single 0 1 ∧ c4SqBeta (Pi.single (0, 0) 1) = 1 ∧
      c4SqGamma (Pi.single (0, 0) 1) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext i; fin_cases i <;> simp [c4SqB]
  · funext i; fin_cases i <;> simp [c4SqC]
  · funext i; fin_cases i <;> simp [c4SqD]
  · ext <;> simp [c4SqBeta, c4SqAlpha, c4SqD, sq]
  · ext <;> simp [c4SqGamma, c4SqAlpha, c4SqD, sq]

/-- **Primes congruent to $-3$ modulo $8$.** $P$ is the set of positive prime integers $p$
with $p \equiv -3 \pmod 8$, that is, $p \equiv 5 \pmod 8$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Theorem 1 (definition of `P`). -/
public def primesFiveModEight : Set ℤ :=
  {p | 0 < p ∧ Prime p ∧ p % 8 = 5}

/-- **$5$ and $13$ lie in $P$.** The integers $5$ and $13$ both belong to the set $P$ of
positive primes $p \equiv -3 \pmod 8$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Theorem 1 (definition of `P`). -/
public theorem five_thirteen_mem_primesFiveModEight :
    (5 : ℤ) ∈ primesFiveModEight ∧ (13 : ℤ) ∈ primesFiveModEight :=
  ⟨⟨by norm_num, Int.prime_iff_natAbs_prime.2 (by decide), by norm_num⟩,
    ⟨by norm_num, Int.prime_iff_natAbs_prime.2 (by decide), by norm_num⟩⟩

/-- **The exceptional set $A$ for $C_4^2$.** Let $P$ be the set of positive primes
$p \equiv 5 \pmod 8$. The set $A \subseteq \mathbb{Z}$ consists of all products
$(8k - 3)(8l - 3)(8m - 3)(8n - 3)$ with $k, l, m, n \in \mathbb{Z}$ such that $8l - 3$,
$8m - 3$ and $8n - 3$ lie in $P$ and $k + l \not\equiv m + n \pmod 2$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Theorem 1 (definition of `A`). -/
public def c4SqExceptionalSet : Set ℤ :=
  {z | ∃ k l m n : ℤ, 8 * l - 3 ∈ primesFiveModEight ∧ 8 * m - 3 ∈ primesFiveModEight ∧
    8 * n - 3 ∈ primesFiveModEight ∧ ¬ k + l ≡ m + n [ZMOD 2] ∧
    z = (8 * k - 3) * (8 * l - 3) * (8 * m - 3) * (8 * n - 3)}

/-- **The exceptional set $A$ contains $1625$.** Let $P$ be the set of positive primes
$p \equiv -3 \pmod 8$ and $A$ the set of products $(8k-3)(8l-3)(8m-3)(8n-3)$ with
$k, l, m, n \in \mathbb{Z}$, $8l-3, 8m-3, 8n-3 \in P$ and $k + l \not\equiv m + n \pmod 2$.
Then $1625 \in A$: take $k = l = m = 1$ and $n = 2$, so that $1625 = 5 \cdot 5 \cdot 5 \cdot 13$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Theorem 1 (definition of `A`). -/
public theorem mem_c4SqExceptionalSet_1625 : (1625 : ℤ) ∈ c4SqExceptionalSet :=
  ⟨1, 1, 1, 2, five_thirteen_mem_primesFiveModEight.1, five_thirteen_mem_primesFiveModEight.1,
    five_thirteen_mem_primesFiveModEight.2, by decide, by norm_num⟩

/-- **Factorization of the 4 × 4 circulant determinant.** For every commutative ring $R$ and all
$x_0, x_1, x_2, x_3 \in R$, the $4 \times 4$ circulant determinant $D_4$ satisfies

$$D_4(x_0, x_1, x_2, x_3) =
\bigl((x_0 + x_2)^2 - (x_1 + x_3)^2\bigr)\bigl((x_0 - x_2)^2 + (x_1 - x_3)^2\bigr).$$

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Corollary 1 (`integers-2024-A30-cor-1`). -/
public theorem_wanted circulantDetFour_eq {R : Type*} [CommRing R] (x₀ x₁ x₂ x₃ : R) :
    circulantDetFour ![x₀, x₁, x₂, x₃] =
      ((x₀ + x₂) ^ 2 - (x₁ + x₃) ^ 2) * ((x₀ - x₂) ^ 2 + (x₁ - x₃) ^ 2)

/-- **Factorization of the complex group determinant of $C_4^2$.** For every
$y \colon \mathbb{Z}/4 \times \mathbb{Z}/4 \to \mathbb{C}$,

$$
\det\bigl(y(h - g)\bigr)_{g, h \in \mathbb{Z}/4 \times \mathbb{Z}/4} =
\prod_{k=0}^{3} D_4\bigl(z_k(0), z_k(1), z_k(2), z_k(3)\bigr), \qquad
z_k(r) = \sum_{s=0}^{3} i^{ks} y(r, s),
$$

where $i = \sqrt{-1}$ and $D_4(x_0, x_1, x_2, x_3)$ is the determinant of the $4 \times 4$
circulant matrix with first row $(x_0, x_1, x_2, x_3)$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Corollary 2 (`integers-2024-A30-cor-2`). -/
public theorem_wanted c4Sq_groupDet_eq_prod_circulantDetFour (y : Fin 4 × Fin 4 → ℂ) :
    (circulant y).det =
      ∏ k : Fin 4, circulantDetFour fun r : Fin 4 =>
        ∑ s : Fin 4, Complex.I ^ (k.val * s.val) * y (r, s)

/-- **Sums of two squares congruent to −3 modulo 8.** Let $a$ and $b$ be integers with
$a^2 + b^2 \equiv -3 \pmod 8$. Then there are integers $k$ and $l$ such that $8l - 3$ lies in
the set $P$ of positive primes congruent to $5$ modulo $8$, and $a^2 + b^2 = (8k + 1)(8l - 3)$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Corollary 3 (`integers-2024-A30-cor-3`). -/
public theorem_wanted sq_add_sq_eq_mul_of_mod_eight (a b : ℤ) (h : a ^ 2 + b ^ 2 ≡ -3 [ZMOD 8]) :
    ∃ k l : ℤ, 8 * l - 3 ∈ primesFiveModEight ∧ a ^ 2 + b ^ 2 = (8 * k + 1) * (8 * l - 3)

/-- **Norms of β and γ as products of sums of two squares (C₄²).** Let $a$ be an integer-valued
function on $C_4^2 = \mathbb{Z}/4 \times \mathbb{Z}/4$, with associated integers $d_0, \dots, d_7$
and Gaussian integers $\beta$, $\gamma$, and write $\beta\bar\beta$, $\gamma\bar\gamma$ for the
norms of $\beta$ and $\gamma$. Then

$$\beta\bar\beta = \bigl((d_0 + d_2 + d_1 + d_3)^2 + (d_4 + d_6 + d_5 + d_7)^2\bigr)
\bigl((d_0 + d_2 - d_1 - d_3)^2 + (d_4 + d_6 - d_5 - d_7)^2\bigr)$$

and

$$\gamma\bar\gamma = \bigl((d_0 - d_2 - d_5 + d_7)^2 + (d_4 - d_6 + d_1 - d_3)^2\bigr)
\bigl((d_0 - d_2 + d_5 - d_7)^2 + (d_4 - d_6 - d_1 + d_3)^2\bigr).$$

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 1 (`integers-2024-A30-lem-1`). -/
public theorem_wanted c4Sq_norm_beta_gamma_eq (a : Fin 4 × Fin 4 → ℤ) :
    let d := c4SqD a
    Zsqrtd.norm (c4SqBeta a) =
        ((d 0 + d 2 + d 1 + d 3) ^ 2 + (d 4 + d 6 + d 5 + d 7) ^ 2) *
          ((d 0 + d 2 - d 1 - d 3) ^ 2 + (d 4 + d 6 - d 5 - d 7) ^ 2) ∧
      Zsqrtd.norm (c4SqGamma a) =
        ((d 0 - d 2 - d 5 + d 7) ^ 2 + (d 4 - d 6 + d 1 - d 3) ^ 2) *
          ((d 0 - d 2 + d 5 - d 7) ^ 2 + (d 4 - d 6 - d 1 + d 3) ^ 2)

/-- **The group determinant of $C_4^2$ modulo $2$.**
Let $a \colon \mathbb{Z}/4 \times \mathbb{Z}/4 \to \mathbb{Z}$. For $0 \le i \le 3$ let
$b_i = a(i, 0) + a(i, 2) + a(i, 1) + a(i, 3)$, $c_i = a(i, 0) + a(i, 2) - a(i, 1) - a(i, 3)$
and $\alpha_i = (a(i, 0) - a(i, 2)) + (a(i, 1) - a(i, 3))\sqrt{-1} \in \mathbb{Z}[\sqrt{-1}]$,
and let $\beta = (\alpha_0 + \alpha_2)^2 - (\alpha_1 + \alpha_3)^2$ and
$\gamma = (\alpha_0 - \alpha_2)^2 + (\alpha_1 - \alpha_3)^2$, with complex conjugates $\bar\beta$
and $\bar\gamma$. Let $D_4(x_0, x_1, x_2, x_3)$ be the determinant of the $4 \times 4$
circulant matrix with first row $(x_0, x_1, x_2, x_3)$.
Then the group determinant $D_{4 \times 4}(a) = \det\bigl(a(h - g)\bigr)_{g, h}$, with $g, h$
ranging over $\mathbb{Z}/4 \times \mathbb{Z}/4$, satisfies
$D_{4 \times 4}(a) \equiv D_4(b) \equiv D_4(c) \equiv \beta\bar\beta \equiv \gamma\bar\gamma
\pmod 2$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 2 (`integers-2024-A30-lem-2`). -/
public theorem_wanted c4Sq_groupDet_congr_mod_two (a : Fin 4 × Fin 4 → ℤ) :
    (circulant a).det ≡ circulantDetFour (c4SqB a) [ZMOD 2] ∧
      circulantDetFour (c4SqB a) ≡ circulantDetFour (c4SqC a) [ZMOD 2] ∧
      circulantDetFour (c4SqC a) ≡ Zsqrtd.norm (c4SqBeta a) [ZMOD 2] ∧
      Zsqrtd.norm (c4SqBeta a) ≡ Zsqrtd.norm (c4SqGamma a) [ZMOD 2]

/-- **Norms of β and γ as differences of squares (C₄²).** Let $a$ be an integer-valued function
on $C_4^2 = \mathbb{Z}/4 \times \mathbb{Z}/4$, with associated integers $d_0, \dots, d_7$ and
Gaussian integers $\beta$, $\gamma$, and write $\beta\bar\beta$, $\gamma\bar\gamma$ for the norms of
$\beta$ and $\gamma$. Then

$$\beta\bar\beta = \bigl((d_0 + d_2)^2 + (d_4 + d_6)^2 + (d_1 + d_3)^2 + (d_5 + d_7)^2\bigr)^2 -
4\bigl((d_0 + d_2)(d_1 + d_3) + (d_4 + d_6)(d_5 + d_7)\bigr)^2$$

and

$$\gamma\bar\gamma = \bigl((d_0 - d_2)^2 + (d_4 - d_6)^2 + (d_1 - d_3)^2 + (d_5 - d_7)^2\bigr)^2 -
4\bigl((d_0 - d_2)(d_5 - d_7) - (d_4 - d_6)(d_1 - d_3)\bigr)^2.$$

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 3 (`integers-2024-A30-lem-3`). -/
public theorem_wanted c4Sq_norm_beta_gamma_eq_sq_sub (a : Fin 4 × Fin 4 → ℤ) :
    let d := c4SqD a
    Zsqrtd.norm (c4SqBeta a) =
        ((d 0 + d 2) ^ 2 + (d 4 + d 6) ^ 2 + (d 1 + d 3) ^ 2 + (d 5 + d 7) ^ 2) ^ 2 -
          4 * ((d 0 + d 2) * (d 1 + d 3) + (d 4 + d 6) * (d 5 + d 7)) ^ 2 ∧
      Zsqrtd.norm (c4SqGamma a) =
        ((d 0 - d 2) ^ 2 + (d 4 - d 6) ^ 2 + (d 1 - d 3) ^ 2 + (d 5 - d 7) ^ 2) ^ 2 -
          4 * ((d 0 - d 2) * (d 5 - d 7) - (d 4 - d 6) * (d 1 - d 3)) ^ 2

/-- **Difference of the squared sums of squares of the $d_i$.** Let
$a \colon \mathbb{Z}/4 \times \mathbb{Z}/4 \to \mathbb{Z}$, and let $d_i = a(i, 0) - a(i, 2)$ and
$d_{i+4} = a(i, 1) - a(i, 3)$ for $0 \le i \le 3$. Then

$$
\bigl((d_0 + d_2)^2 + (d_4 + d_6)^2 + (d_1 + d_3)^2 + (d_5 + d_7)^2\bigr)^2 -
\bigl((d_0 - d_2)^2 + (d_4 - d_6)^2 + (d_1 - d_3)^2 + (d_5 - d_7)^2\bigr)^2 =
8 \Bigl(\sum_{i=0}^{7} d_i^2\Bigr)(d_0 d_2 + d_4 d_6 + d_1 d_3 + d_5 d_7).
$$

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 4 (`integers-2024-A30-lem-4`). -/
public theorem_wanted c4SqD_sum_sq_sq_sub_sq (a : Fin 4 × Fin 4 → ℤ) :
    let d := c4SqD a
    ((d 0 + d 2) ^ 2 + (d 4 + d 6) ^ 2 + (d 1 + d 3) ^ 2 + (d 5 + d 7) ^ 2) ^ 2 -
        ((d 0 - d 2) ^ 2 + (d 4 - d 6) ^ 2 + (d 1 - d 3) ^ 2 + (d 5 - d 7) ^ 2) ^ 2 =
      8 * (d 0 ^ 2 + d 2 ^ 2 + d 4 ^ 2 + d 6 ^ 2 + d 1 ^ 2 + d 3 ^ 2 + d 5 ^ 2 + d 7 ^ 2) *
        (d 0 * d 2 + d 4 * d 6 + d 1 * d 3 + d 5 * d 7)

/-- **Cross terms of the $d_i$ modulo $4$.** Let
$a \colon \mathbb{Z}/4 \times \mathbb{Z}/4 \to \mathbb{Z}$ have sums $b_i$, alternating sums
$c_i$ and differences $d_0, \dots, d_7$. Then the following five congruences hold modulo $4$:
$2(d_0 d_2 + d_4 d_6 + d_1 d_3 + d_5 d_7) \equiv b_0 b_2 + b_1 b_3 + c_0 c_2 + c_1 c_3$;
$2(d_0 d_7 + d_2 d_5 + d_4 d_3 + d_6 d_1) \equiv b_0 b_3 + b_2 b_1 - c_0 c_3 - c_2 c_1$;
$2(d_0 d_3 + d_2 d_1 + d_4 d_7 + d_6 d_5) \equiv b_0 b_3 + b_2 b_1 + c_0 c_3 + c_2 c_1$;
$2(d_0 d_5 + d_2 d_7 + d_4 d_1 + d_6 d_3) \equiv b_0 b_1 + b_2 b_3 - c_0 c_1 - c_2 c_3$;
$2(d_0 d_1 + d_2 d_3 + d_4 d_5 + d_6 d_7) \equiv b_0 b_1 + b_2 b_3 + c_0 c_1 + c_2 c_3$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 5 (`integers-2024-A30-lem-5`). -/
public theorem_wanted c4SqD_cross_terms_mod_four (a : Fin 4 × Fin 4 → ℤ) :
    let b := c4SqB a
    let c := c4SqC a
    let d := c4SqD a
    2 * (d 0 * d 2 + d 4 * d 6 + d 1 * d 3 + d 5 * d 7) ≡
        b 0 * b 2 + b 1 * b 3 + c 0 * c 2 + c 1 * c 3 [ZMOD 4] ∧
      2 * (d 0 * d 7 + d 2 * d 5 + d 4 * d 3 + d 6 * d 1) ≡
        b 0 * b 3 + b 2 * b 1 - c 0 * c 3 - c 2 * c 1 [ZMOD 4] ∧
      2 * (d 0 * d 3 + d 2 * d 1 + d 4 * d 7 + d 6 * d 5) ≡
        b 0 * b 3 + b 2 * b 1 + c 0 * c 3 + c 2 * c 1 [ZMOD 4] ∧
      2 * (d 0 * d 5 + d 2 * d 7 + d 4 * d 1 + d 6 * d 3) ≡
        b 0 * b 1 + b 2 * b 3 - c 0 * c 1 - c 2 * c 3 [ZMOD 4] ∧
      2 * (d 0 * d 1 + d 2 * d 3 + d 4 * d 5 + d 6 * d 7) ≡
        b 0 * b 1 + b 2 * b 3 + c 0 * c 1 + c 2 * c 3 [ZMOD 4]

/-- **The 4 × 4 circulant determinant modulo 16 at two parity patterns.** For all integers
$k$, $l$, $m$, $n$, the $4 \times 4$ circulant determinant $D_4$ satisfies
$D_4(2k + 1, 2l, 2m, 2n) \equiv 8m + 1 \pmod{16}$ and
$D_4(2k, 2l + 1, 2m + 1, 2n + 1) \equiv 8(k + l + n) - 3 \pmod{16}$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 6 (`integers-2024-A30-lem-6`). -/
public theorem_wanted circulantDetFour_mod_sixteen (k l m n : ℤ) :
    circulantDetFour ![2 * k + 1, 2 * l, 2 * m, 2 * n] ≡ 8 * m + 1 [ZMOD 16] ∧
      circulantDetFour ![2 * k, 2 * l + 1, 2 * m + 1, 2 * n + 1] ≡ 8 * (k + l + n) - 3 [ZMOD 16]

/-- **Powers of $2$ dividing the $C_4$ group determinant at four parity patterns.** Let
$D(x_0, x_1, x_2, x_3)$ be the group determinant of $C_4$, that is the determinant of the
$4 \times 4$ circulant matrix with $(i, j)$ entry $x_{i - j}$ (indices mod $4$). For integers
$k, l, m, n$ put $D_1 = D(2k, 2l, 2m, 2n)$, $D_2 = D(2k+1, 2l+1, 2m+1, 2n+1)$,
$D_3 = D(2k, 2l+1, 2m, 2n+1)$, $D_4 = D(2k, 2l, 2m+1, 2n+1)$,
$w_3 = (2k+2l+1)(2m+2n+1)$ and $w_4 = (2k+2m+1)(2l+2n+1)$, and write $2^e \mathbb{Z}_{odd}$
for the set of integers $2^e(2t+1)$ with $t \in \mathbb{Z}$. Then:

* if $k + m \not\equiv l + n \pmod 2$ then $D_1 \in 2^4 \mathbb{Z}_{odd}$, and if
  $k + m \equiv l + n \pmod 2$ then $2^8 \mid D_1$;
* if $k + m \not\equiv l + n \pmod 2$ then $D_2 \in 2^4 \mathbb{Z}_{odd}$; if
  $(k + m)(l + n) \equiv -1 \pmod 4$ then $D_2 \in 2^7 \mathbb{Z}_{odd}$; and if
  $k + m \equiv l + n \pmod 2$ and $(k + m)(l + n) \not\equiv -1 \pmod 4$ then $2^9 \mid D_2$;
* if $k - m$ and $l - n$ are both odd then $D_3 \in 2^5 \mathbb{Z}_{odd}$; if
  $k \equiv m \pmod 2$ and $w_3 \equiv \pm 3 \pmod 8$ then $D_3 \in 2^6 \mathbb{Z}_{odd}$; and if
  neither of these two conditions holds then $2^7 \mid D_3$;
* if $w_4 \equiv \pm 3 \pmod 8$ then $D_4 \in 2^4 \mathbb{Z}_{odd}$, and if
  $w_4 \equiv \pm 1 \pmod 8$ then $2^5 \mid D_4$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 7 (`integers-2024-A30-lem-7`). -/
public theorem_wanted circulantDetFour_two_power_cases (k l m n : ℤ) :
    let D₁ := circulantDetFour ![2 * k, 2 * l, 2 * m, 2 * n]
    let D₂ := circulantDetFour ![2 * k + 1, 2 * l + 1, 2 * m + 1, 2 * n + 1]
    let D₃ := circulantDetFour ![2 * k, 2 * l + 1, 2 * m, 2 * n + 1]
    let D₄ := circulantDetFour ![2 * k, 2 * l, 2 * m + 1, 2 * n + 1]
    let w₃ := (2 * k + 2 * l + 1) * (2 * m + 2 * n + 1)
    let w₄ := (2 * k + 2 * m + 1) * (2 * l + 2 * n + 1)
    ((¬ k + m ≡ l + n [ZMOD 2] → ∃ t, D₁ = 2 ^ 4 * (2 * t + 1)) ∧
        (k + m ≡ l + n [ZMOD 2] → 2 ^ 8 ∣ D₁)) ∧
      ((¬ k + m ≡ l + n [ZMOD 2] → ∃ t, D₂ = 2 ^ 4 * (2 * t + 1)) ∧
        ((k + m) * (l + n) ≡ -1 [ZMOD 4] → ∃ t, D₂ = 2 ^ 7 * (2 * t + 1)) ∧
        (k + m ≡ l + n [ZMOD 2] → ¬ (k + m) * (l + n) ≡ -1 [ZMOD 4] → 2 ^ 9 ∣ D₂)) ∧
      ((k - m ≡ 1 [ZMOD 2] ∧ l - n ≡ 1 [ZMOD 2] → ∃ t, D₃ = 2 ^ 5 * (2 * t + 1)) ∧
        (k ≡ m [ZMOD 2] ∧ (w₃ ≡ 3 [ZMOD 8] ∨ w₃ ≡ -3 [ZMOD 8]) →
          ∃ t, D₃ = 2 ^ 6 * (2 * t + 1)) ∧
        (¬ (k - m ≡ 1 [ZMOD 2] ∧ l - n ≡ 1 [ZMOD 2]) →
          ¬ (k ≡ m [ZMOD 2] ∧ (w₃ ≡ 3 [ZMOD 8] ∨ w₃ ≡ -3 [ZMOD 8])) → 2 ^ 7 ∣ D₃)) ∧
      ((w₄ ≡ 3 [ZMOD 8] ∨ w₄ ≡ -3 [ZMOD 8] → ∃ t, D₄ = 2 ^ 4 * (2 * t + 1)) ∧
        (w₄ ≡ 1 [ZMOD 8] ∨ w₄ ≡ -1 [ZMOD 8] → 2 ^ 5 ∣ D₄))

/-- **Odd integer group determinants of $C_4 \times C_4$.** Let $C_4$ be the cyclic group of
order $4$, $S(C_4^2)$ the set of integer group determinants of $C_4 \times C_4$ and $P$ the set
of positive primes $p \equiv -3 \pmod 8$, and let $A$ be the set of products
$(8k-3)(8l-3)(8m-3)(8n-3)$ with $k, l, m, n \in \mathbb{Z}$, $8l-3, 8m-3, 8n-3 \in P$ and
$k + l \not\equiv m + n \pmod 2$. Every odd $z \in S(C_4^2)$ is of the form $16m + 1$ for some
integer $m$ or lies in $A$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 8 (`integers-2024-A30-lem-8`). -/
public theorem_wanted odd_mem_integerGroupDeterminants_c4Sq {z : ℤ}
    (hz : z ∈ integerGroupDeterminants (Fin 4 × Fin 4)) (hodd : Odd z) :
    (∃ m : ℤ, z = 16 * m + 1) ∨ z ∈ c4SqExceptionalSet

/-- **Factorization shapes of $D_4(b) D_4(c)$.** Let
$a \colon \mathbb{Z}/4 \times \mathbb{Z}/4 \to \mathbb{Z}$ have sums $b_i$ and alternating sums
$c_i$, let $D_4$ be the $4 \times 4$ circulant determinant, and suppose
$b_0 + b_2 \not\equiv b_1 + b_3 \pmod 2$. Put $x = b_0 b_2 + b_1 b_3$, $y = c_0 c_2 + c_1 c_3$
and $D = D_4(b) D_4(c)$. If $(x, y) \equiv (0, 0)$ or $(2, 2) \pmod 4$, then
$D = (8k + 1)(8l + 1)$ for some integers $k \equiv l \pmod 2$. If
$(x, y) \equiv (0, 2)$ or $(2, 0) \pmod 4$, then $D = (8k + 1)(8l + 1)$ for some integers
$k \not\equiv l \pmod 2$. If $(x, y) \equiv (1, 1)$ or $(-1, -1) \pmod 4$, then
$D = (8k - 3)(8l - 3)$ for some integers $k \equiv l \pmod 2$. If
$(x, y) \equiv (1, -1)$ or $(-1, 1) \pmod 4$, then $D = (8k - 3)(8l - 3)$ for some integers
$k \not\equiv l \pmod 2$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 9 (`integers-2024-A30-lem-9`). -/
public theorem_wanted c4Sq_circulantDetFour_product_classes (a : Fin 4 × Fin 4 → ℤ)
    (h : ¬ c4SqB a 0 + c4SqB a 2 ≡ c4SqB a 1 + c4SqB a 3 [ZMOD 2]) :
    let x := c4SqB a 0 * c4SqB a 2 + c4SqB a 1 * c4SqB a 3
    let y := c4SqC a 0 * c4SqC a 2 + c4SqC a 1 * c4SqC a 3
    let D := circulantDetFour (c4SqB a) * circulantDetFour (c4SqC a)
    ((x ≡ 0 [ZMOD 4] ∧ y ≡ 0 [ZMOD 4]) ∨ (x ≡ 2 [ZMOD 4] ∧ y ≡ 2 [ZMOD 4]) →
        ∃ k l : ℤ, k ≡ l [ZMOD 2] ∧ D = (8 * k + 1) * (8 * l + 1)) ∧
      ((x ≡ 0 [ZMOD 4] ∧ y ≡ 2 [ZMOD 4]) ∨ (x ≡ 2 [ZMOD 4] ∧ y ≡ 0 [ZMOD 4]) →
        ∃ k l : ℤ, ¬ k ≡ l [ZMOD 2] ∧ D = (8 * k + 1) * (8 * l + 1)) ∧
      ((x ≡ 1 [ZMOD 4] ∧ y ≡ 1 [ZMOD 4]) ∨ (x ≡ -1 [ZMOD 4] ∧ y ≡ -1 [ZMOD 4]) →
        ∃ k l : ℤ, k ≡ l [ZMOD 2] ∧ D = (8 * k - 3) * (8 * l - 3)) ∧
      ((x ≡ 1 [ZMOD 4] ∧ y ≡ -1 [ZMOD 4]) ∨ (x ≡ -1 [ZMOD 4] ∧ y ≡ 1 [ZMOD 4]) →
        ∃ k l : ℤ, ¬ k ≡ l [ZMOD 2] ∧ D = (8 * k - 3) * (8 * l - 3))

/-- **$D_4(b) D_4(c)$ modulo $16$.** Let
$a \colon \mathbb{Z}/4 \times \mathbb{Z}/4 \to \mathbb{Z}$ have sums $b_i$ and alternating sums
$c_i$, and let $D_4$ be the $4 \times 4$ circulant determinant. If
$b_0 + b_2 \not\equiv b_1 + b_3 \pmod 2$, then
$D_4(b) D_4(c) \equiv 1 - 4(b_0 b_2 + b_1 b_3 + c_0 c_2 + c_1 c_3) \pmod{16}$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 10 (`integers-2024-A30-lem-10`). -/
public theorem_wanted c4Sq_circulantDetFour_product_mod_sixteen (a : Fin 4 × Fin 4 → ℤ)
    (h : ¬ c4SqB a 0 + c4SqB a 2 ≡ c4SqB a 1 + c4SqB a 3 [ZMOD 2]) :
    circulantDetFour (c4SqB a) * circulantDetFour (c4SqC a) ≡
      1 - 4 * (c4SqB a 0 * c4SqB a 2 + c4SqB a 1 * c4SqB a 3 +
        c4SqC a 0 * c4SqC a 2 + c4SqC a 1 * c4SqC a 3) [ZMOD 16]

/-- **A prime factor $8l - 3$ of $D_4(b) D_4(c)$.** Let
$a \colon \mathbb{Z}/4 \times \mathbb{Z}/4 \to \mathbb{Z}$ have sums $b_i$, alternating sums
$c_i$ and Gaussian integer $\beta$, let $D_4$ be the $4 \times 4$ circulant determinant, and let
$P$ be the set of positive primes $p \equiv 5 \pmod 8$. Suppose
$b_0 + b_2 \not\equiv b_1 + b_3 \pmod 2$ and that the norm $\beta \bar\beta \equiv -3 \pmod 8$,
and put $Q = b_0 b_2 + b_1 b_3 + c_0 c_2 + c_1 c_3$. If $Q \equiv 0 \pmod 4$, then
$D_4(b) D_4(c) = (8k - 3)(8l - 3)$ for some integers $k \not\equiv l \pmod 2$ with
$8l - 3 \in P$. If $Q \equiv 2 \pmod 4$, then $D_4(b) D_4(c) = (8k - 3)(8l - 3)$ for some
integers $k \equiv l \pmod 2$ with $8l - 3 \in P$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 11 (`integers-2024-A30-lem-11`). -/
public theorem_wanted c4Sq_circulantDetFour_product_prime_factor (a : Fin 4 × Fin 4 → ℤ)
    (h : ¬ c4SqB a 0 + c4SqB a 2 ≡ c4SqB a 1 + c4SqB a 3 [ZMOD 2])
    (hβ : Zsqrtd.norm (c4SqBeta a) ≡ -3 [ZMOD 8]) :
    let Q := c4SqB a 0 * c4SqB a 2 + c4SqB a 1 * c4SqB a 3 +
      c4SqC a 0 * c4SqC a 2 + c4SqC a 1 * c4SqC a 3
    let D := circulantDetFour (c4SqB a) * circulantDetFour (c4SqC a)
    (Q ≡ 0 [ZMOD 4] → ∃ k l : ℤ, 8 * l - 3 ∈ primesFiveModEight ∧ ¬ k ≡ l [ZMOD 2] ∧
        D = (8 * k - 3) * (8 * l - 3)) ∧
      (Q ≡ 2 [ZMOD 4] → ∃ k l : ℤ, 8 * l - 3 ∈ primesFiveModEight ∧ k ≡ l [ZMOD 2] ∧
        D = (8 * k - 3) * (8 * l - 3))

/-- **The difference of the norms of β and γ modulo 16 (C₄²).** Let $a$ be an integer-valued
function on $C_4^2 = \mathbb{Z}/4 \times \mathbb{Z}/4$, with associated integers $b_i$, $c_i$
$(0 \le i \le 3)$ and Gaussian integers $\beta$, $\gamma$, and write $\beta\bar\beta$,
$\gamma\bar\gamma$ for the norms of $\beta$ and $\gamma$. If
$b_0 + b_2 \not\equiv b_1 + b_3 \pmod 2$, then
$\beta\bar\beta - \gamma\bar\gamma \equiv 4(b_0b_2 + b_1b_3 + c_0c_2 + c_1c_3) \pmod{16}$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 12 (`integers-2024-A30-lem-12`). -/
public theorem_wanted c4Sq_norm_beta_sub_norm_gamma_mod_sixteen (a : Fin 4 × Fin 4 → ℤ)
    (h : ¬ c4SqB a 0 + c4SqB a 2 ≡ c4SqB a 1 + c4SqB a 3 [ZMOD 2]) :
    Zsqrtd.norm (c4SqBeta a) - Zsqrtd.norm (c4SqGamma a) ≡
      4 * (c4SqB a 0 * c4SqB a 2 + c4SqB a 1 * c4SqB a 3 +
        c4SqC a 0 * c4SqC a 2 + c4SqC a 1 * c4SqC a 3) [ZMOD 16]

/-- **Two prime factors ≡ −3 mod 8 of ββ̄γγ̄ (C₄²).** Let $a$ be an integer-valued function on
$C_4^2 = \mathbb{Z}/4 \times \mathbb{Z}/4$, with associated integers $b_i$, $c_i$ $(0 \le i \le 3)$
and Gaussian integers $\beta$, $\gamma$, write $\beta\bar\beta$, $\gamma\bar\gamma$ for the norms of
$\beta$ and $\gamma$, let $P$ be the set of primes $p \equiv -3 \pmod 8$, and put
$Q = b_0b_2 + b_1b_3 + c_0c_2 + c_1c_3$. Suppose that $b_0 + b_2 \not\equiv b_1 + b_3 \pmod 2$ and
$\beta\bar\beta \equiv -3 \pmod 8$. If $Q \equiv 0 \pmod 4$, there are integers $j$, $m$, $n$ with
$8m - 3 \in P$, $8n - 3 \in P$, $j \equiv m + n \pmod 2$ and
$\beta\bar\beta\gamma\bar\gamma = (8j + 1)(8m - 3)(8n - 3)$. If $Q \equiv 2 \pmod 4$, the same holds
with $j \not\equiv m + n \pmod 2$ in place of $j \equiv m + n \pmod 2$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 13 (`integers-2024-A30-lem-13`). -/
public theorem_wanted c4Sq_norm_beta_gamma_prime_factors (a : Fin 4 × Fin 4 → ℤ)
    (h : ¬ c4SqB a 0 + c4SqB a 2 ≡ c4SqB a 1 + c4SqB a 3 [ZMOD 2])
    (hβ : Zsqrtd.norm (c4SqBeta a) ≡ -3 [ZMOD 8]) :
    let Q := c4SqB a 0 * c4SqB a 2 + c4SqB a 1 * c4SqB a 3 +
      c4SqC a 0 * c4SqC a 2 + c4SqC a 1 * c4SqC a 3
    let N := Zsqrtd.norm (c4SqBeta a) * Zsqrtd.norm (c4SqGamma a)
    (Q ≡ 0 [ZMOD 4] → ∃ j m n : ℤ, 8 * m - 3 ∈ primesFiveModEight ∧
        8 * n - 3 ∈ primesFiveModEight ∧ j ≡ m + n [ZMOD 2] ∧
        N = (8 * j + 1) * (8 * m - 3) * (8 * n - 3)) ∧
      (Q ≡ 2 [ZMOD 4] → ∃ j m n : ℤ, 8 * m - 3 ∈ primesFiveModEight ∧
        8 * n - 3 ∈ primesFiveModEight ∧ ¬ j ≡ m + n [ZMOD 2] ∧
        N = (8 * j + 1) * (8 * m - 3) * (8 * n - 3))

/-- **Even integer group determinants of $C_4 \times C_4$.** Let $C_4$ be the cyclic group of
order $4$, $S(C_4^2)$ the set of integer group determinants of $C_4 \times C_4$ and $P$ the set
of positive primes $p \equiv -3 \pmod 8$, and let $z \in S(C_4^2)$. If $z$ is even, then
$2^{15} \mid z$. If $z = 2^{15}(2t + 1)$ for some integer $t$, then $z = 2^{15} p (2m + 1)$ for
some $p \in P$ and some integer $m$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 14 (`integers-2024-A30-lem-14`). -/
public theorem_wanted even_mem_integerGroupDeterminants_c4Sq {z : ℤ}
    (hz : z ∈ integerGroupDeterminants (Fin 4 × Fin 4)) :
    (2 ∣ z → 2 ^ 15 ∣ z) ∧
      ((∃ t : ℤ, z = 2 ^ 15 * (2 * t + 1)) →
        ∃ p ∈ primesFiveModEight, ∃ m : ℤ, z = 2 ^ 15 * p * (2 * m + 1))

/-- **The power of $2$ in $D_4(b) D_4(c)$.** Let
$a \colon \mathbb{Z}/4 \times \mathbb{Z}/4 \to \mathbb{Z}$ have sums $b_i$ and alternating sums
$c_i$, let $D_4$ be the $4 \times 4$ circulant determinant, put $D = D_4(b) D_4(c)$, and say
that $D \in 2^e \mathbb{Z}_{\mathrm{odd}}$ when $D = 2^e (2t + 1)$ for some integer $t$.
If every $b_i$ is even, then $D \in 2^8 \mathbb{Z}_{\mathrm{odd}}$ when
$b_0 + b_1 + b_2 + b_3 \equiv c_0 + c_1 + c_2 + c_3 \equiv 2 \pmod 4$, and $2^{12} \mid D$
otherwise. If every $b_i$ is odd, then $D \in 2^8 \mathbb{Z}_{\mathrm{odd}}$ under the same
condition, and $2^{11} \mid D$ otherwise. If $b_0 \equiv b_2$, $b_1 \equiv b_3$ and
$b_0 \not\equiv b_1 \pmod 2$, then $D \in 2^{10} \mathbb{Z}_{\mathrm{odd}}$ when
$b_0 - b_2 \equiv b_1 - b_3 \equiv c_0 - c_2 \equiv c_1 - c_3 \equiv 2 \pmod 4$, and
$2^{11} \mid D$ otherwise. If $b_0 + b_2$ and $b_1 + b_3$ are both odd, put
$u = (b_0 + b_2)(b_1 + b_3)$ and $v = (c_0 + c_2)(c_1 + c_3)$; then
$D \in 2^8 \mathbb{Z}_{\mathrm{odd}}$ when $u \equiv \pm 3$ and $v \equiv \pm 3 \pmod 8$, and
$2^9 \mid D$ otherwise.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 15 (`integers-2024-A30-lem-15`). -/
public theorem_wanted c4Sq_circulantDetFour_product_two_power (a : Fin 4 × Fin 4 → ℤ) :
    let b := c4SqB a
    let c := c4SqC a
    let D := circulantDetFour b * circulantDetFour c
    ((∀ i, b i ≡ 0 [ZMOD 2]) →
      (b 0 + b 1 + b 2 + b 3 ≡ 2 [ZMOD 4] ∧ c 0 + c 1 + c 2 + c 3 ≡ 2 [ZMOD 4] →
          ∃ t, D = 2 ^ 8 * (2 * t + 1)) ∧
        (¬ (b 0 + b 1 + b 2 + b 3 ≡ 2 [ZMOD 4] ∧ c 0 + c 1 + c 2 + c 3 ≡ 2 [ZMOD 4]) →
          2 ^ 12 ∣ D)) ∧
    ((∀ i, b i ≡ 1 [ZMOD 2]) →
      (b 0 + b 1 + b 2 + b 3 ≡ 2 [ZMOD 4] ∧ c 0 + c 1 + c 2 + c 3 ≡ 2 [ZMOD 4] →
          ∃ t, D = 2 ^ 8 * (2 * t + 1)) ∧
        (¬ (b 0 + b 1 + b 2 + b 3 ≡ 2 [ZMOD 4] ∧ c 0 + c 1 + c 2 + c 3 ≡ 2 [ZMOD 4]) →
          2 ^ 11 ∣ D)) ∧
    (b 0 ≡ b 2 [ZMOD 2] → b 1 ≡ b 3 [ZMOD 2] → ¬ b 0 ≡ b 1 [ZMOD 2] →
      (b 0 - b 2 ≡ 2 [ZMOD 4] ∧ b 1 - b 3 ≡ 2 [ZMOD 4] ∧ c 0 - c 2 ≡ 2 [ZMOD 4] ∧
          c 1 - c 3 ≡ 2 [ZMOD 4] → ∃ t, D = 2 ^ 10 * (2 * t + 1)) ∧
        (¬ (b 0 - b 2 ≡ 2 [ZMOD 4] ∧ b 1 - b 3 ≡ 2 [ZMOD 4] ∧ c 0 - c 2 ≡ 2 [ZMOD 4] ∧
          c 1 - c 3 ≡ 2 [ZMOD 4]) → 2 ^ 11 ∣ D)) ∧
    (b 0 + b 2 ≡ 1 [ZMOD 2] → b 1 + b 3 ≡ 1 [ZMOD 2] →
      let u := (b 0 + b 2) * (b 1 + b 3)
      let v := (c 0 + c 2) * (c 1 + c 3)
      ((u ≡ 3 [ZMOD 8] ∨ u ≡ -3 [ZMOD 8]) ∧ (v ≡ 3 [ZMOD 8] ∨ v ≡ -3 [ZMOD 8]) →
          ∃ t, D = 2 ^ 8 * (2 * t + 1)) ∧
        (¬ ((u ≡ 3 [ZMOD 8] ∨ u ≡ -3 [ZMOD 8]) ∧ (v ≡ 3 [ZMOD 8] ∨ v ≡ -3 [ZMOD 8])) →
          2 ^ 9 ∣ D))

/-- **The power of $2$ in $\beta\bar\beta\gamma\bar\gamma$.** Let
$a \colon \mathbb{Z}/4 \times \mathbb{Z}/4 \to \mathbb{Z}$ have sums $b_i$, alternating sums
$c_i$, differences $d_0, \dots, d_7$ and Gaussian integers $\beta$, $\gamma$, and put
$N = \beta \bar\beta \gamma \bar\gamma$, the product of the norms of $\beta$ and $\gamma$. If
$b_0 + b_2$ and $b_1 + b_3$ are both even, then $N = 2^4 (2t + 1)$ for some integer $t$ when
$b_0 + b_1 + b_2 + b_3 \not\equiv c_0 + c_1 + c_2 + c_3 \pmod 4$, and $2^8 \mid N$ when
$b_0 + b_1 + b_2 + b_3 \equiv c_0 + c_1 + c_2 + c_3 \pmod 4$. If $b_0 + b_2$ and $b_1 + b_3$
are both odd, put
$d = \bigl((d_0 + d_2)(d_5 + d_7) + (d_4 + d_6)(d_1 + d_3)\bigr)
\bigl((d_0 - d_2)(d_1 - d_3) + (d_4 - d_6)(d_5 - d_7)\bigr)$; then $N = 2^7 (2t + 1)$ for
some integer $t$ when $d \equiv 2 \pmod 4$, and $2^8 \mid N$ when $d \equiv 0 \pmod 4$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 16 (`integers-2024-A30-lem-16`). -/
public theorem_wanted c4Sq_norm_beta_gamma_two_power (a : Fin 4 × Fin 4 → ℤ) :
    let b := c4SqB a
    let c := c4SqC a
    let e := c4SqD a
    let N := Zsqrtd.norm (c4SqBeta a) * Zsqrtd.norm (c4SqGamma a)
    let d := ((e 0 + e 2) * (e 5 + e 7) + (e 4 + e 6) * (e 1 + e 3)) *
      ((e 0 - e 2) * (e 1 - e 3) + (e 4 - e 6) * (e 5 - e 7))
    (b 0 + b 2 ≡ 0 [ZMOD 2] → b 1 + b 3 ≡ 0 [ZMOD 2] →
      (¬ b 0 + b 1 + b 2 + b 3 ≡ c 0 + c 1 + c 2 + c 3 [ZMOD 4] →
          ∃ t, N = 2 ^ 4 * (2 * t + 1)) ∧
        (b 0 + b 1 + b 2 + b 3 ≡ c 0 + c 1 + c 2 + c 3 [ZMOD 4] → 2 ^ 8 ∣ N)) ∧
    (b 0 + b 2 ≡ 1 [ZMOD 2] → b 1 + b 3 ≡ 1 [ZMOD 2] →
      (d ≡ 2 [ZMOD 4] → ∃ t, N = 2 ^ 7 * (2 * t + 1)) ∧ (d ≡ 0 [ZMOD 4] → 2 ^ 8 ∣ N))

/-- **Two conditions forcing $b_0 b_2 + b_1 b_3 + c_0 c_2 + c_1 c_3 \equiv 2 \pmod 4$.** Let
$a \colon \mathbb{Z}/4 \times \mathbb{Z}/4 \to \mathbb{Z}$ have sums $b_i$, alternating sums
$c_i$ and Gaussian integers $\beta$, $\gamma$; let $D_4$ be the $4 \times 4$ circulant
determinant, and put $D = D_4(b) D_4(c)$, $N = \beta \bar\beta \gamma \bar\gamma$ and
$Q = b_0 b_2 + b_1 b_3 + c_0 c_2 + c_1 c_3$. If every $b_i$ is odd and $D = 2^{11} (2t + 1)$
for some integer $t$, then $Q \equiv 2 \pmod 4$. If $b_0 \equiv b_2$, $b_1 \equiv b_3$ and
$b_0 \not\equiv b_1 \pmod 2$, and $D = 2^{11} (2t + 1)$ and $N = 2^4 (2s + 1)$ for some
integers $t$ and $s$, then $Q \equiv 2 \pmod 4$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 17 (`integers-2024-A30-lem-17`). -/
public theorem_wanted c4Sq_cross_sum_mod_four_of_two_power (a : Fin 4 × Fin 4 → ℤ) :
    let b := c4SqB a
    let c := c4SqC a
    let D := circulantDetFour b * circulantDetFour c
    let N := Zsqrtd.norm (c4SqBeta a) * Zsqrtd.norm (c4SqGamma a)
    let Q := b 0 * b 2 + b 1 * b 3 + c 0 * c 2 + c 1 * c 3
    ((∀ i, b i ≡ 1 [ZMOD 2]) → (∃ t, D = 2 ^ 11 * (2 * t + 1)) → Q ≡ 2 [ZMOD 4]) ∧
      (b 0 ≡ b 2 [ZMOD 2] → b 1 ≡ b 3 [ZMOD 2] → ¬ b 0 ≡ b 1 [ZMOD 2] →
        (∃ t, D = 2 ^ 11 * (2 * t + 1)) → (∃ t, N = 2 ^ 4 * (2 * t + 1)) → Q ≡ 2 [ZMOD 4])

/-- **A prime factor p ≡ −3 mod 8 of ββ̄γγ̄ in the even case (C₄²).** Let $a$ be an integer-valued
function on $C_4^2 = \mathbb{Z}/4 \times \mathbb{Z}/4$, with associated integers $b_i$, $c_i$
$(0 \le i \le 3)$ and Gaussian integers $\beta$, $\gamma$, write $\beta\bar\beta$ and
$\gamma\bar\gamma$ for the norms of $\beta$ and $\gamma$, and let $P$ be the set of primes
$p \equiv -3 \pmod 8$. Suppose that $b_0 + b_2 \equiv b_1 + b_3 \equiv 0 \pmod 2$, that
$\beta\bar\beta\gamma\bar\gamma = 2^4(2t + 1)$ for some integer $t$, and that
$b_0b_2 + b_1b_3 + c_0c_2 + c_1c_3 \equiv 2 \pmod 4$. Then
$\beta\bar\beta\gamma\bar\gamma = 2^4 p(2m + 1)$ for some $p \in P$ and some integer $m$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 18 (`integers-2024-A30-lem-18`). -/
public theorem_wanted c4Sq_norm_beta_gamma_prime_factor (a : Fin 4 × Fin 4 → ℤ)
    (h₀ : c4SqB a 0 + c4SqB a 2 ≡ 0 [ZMOD 2]) (h₁ : c4SqB a 1 + c4SqB a 3 ≡ 0 [ZMOD 2])
    (hN : ∃ t, Zsqrtd.norm (c4SqBeta a) * Zsqrtd.norm (c4SqGamma a) = 2 ^ 4 * (2 * t + 1))
    (hQ : c4SqB a 0 * c4SqB a 2 + c4SqB a 1 * c4SqB a 3 +
      c4SqC a 0 * c4SqC a 2 + c4SqC a 1 * c4SqC a 3 ≡ 2 [ZMOD 4]) :
    ∃ p ∈ primesFiveModEight, ∃ m : ℤ,
      Zsqrtd.norm (c4SqBeta a) * Zsqrtd.norm (c4SqGamma a) = 2 ^ 4 * p * (2 * m + 1)

/-- **A prime factor $p \equiv 5 \pmod 8$ of $D_4(b) D_4(c) \beta\bar\beta \gamma\bar\gamma$.**
Let $a \colon \mathbb{Z}/4 \times \mathbb{Z}/4 \to \mathbb{Z}$. For $0 \le i \le 3$ let
$b_i = a(i, 0) + a(i, 2) + a(i, 1) + a(i, 3)$, $c_i = a(i, 0) + a(i, 2) - a(i, 1) - a(i, 3)$
and $\alpha_i = (a(i, 0) - a(i, 2)) + (a(i, 1) - a(i, 3))\sqrt{-1} \in \mathbb{Z}[\sqrt{-1}]$,
and let $\beta = (\alpha_0 + \alpha_2)^2 - (\alpha_1 + \alpha_3)^2$ and
$\gamma = (\alpha_0 - \alpha_2)^2 + (\alpha_1 - \alpha_3)^2$, with complex conjugates $\bar\beta$
and $\bar\gamma$. Let $D_4(x_0, x_1, x_2, x_3)$ be the determinant of the $4 \times 4$
circulant matrix with first row $(x_0, x_1, x_2, x_3)$.
Let $P$ be the set of positive primes $p \equiv 5 \pmod 8$. Suppose that $b_0 + b_2$ and
$b_1 + b_3$ are odd, that $D_4(b) D_4(c) = 2^8 (2t + 1)$ for some integer $t$, and that
$\beta\bar\beta \gamma\bar\gamma = 2^7 (2t' + 1)$ for some integer $t'$. Then there are $p \in P$
and $m \in \mathbb{Z}$ with $D_4(b) D_4(c) \beta\bar\beta \gamma\bar\gamma = 2^{15} p (2m + 1)$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 19 (`integers-2024-A30-lem-19`). -/
public theorem_wanted c4Sq_groupDet_factors_prime_factor (a : Fin 4 × Fin 4 → ℤ)
    (h₀ : c4SqB a 0 + c4SqB a 2 ≡ 1 [ZMOD 2]) (h₁ : c4SqB a 1 + c4SqB a 3 ≡ 1 [ZMOD 2])
    (hD : ∃ t, circulantDetFour (c4SqB a) * circulantDetFour (c4SqC a) = 2 ^ 8 * (2 * t + 1))
    (hN : ∃ t, Zsqrtd.norm (c4SqBeta a) * Zsqrtd.norm (c4SqGamma a) = 2 ^ 7 * (2 * t + 1)) :
    ∃ p ∈ primesFiveModEight, ∃ m : ℤ,
      circulantDetFour (c4SqB a) * circulantDetFour (c4SqC a) *
        (Zsqrtd.norm (c4SqBeta a) * Zsqrtd.norm (c4SqGamma a)) = 2 ^ 15 * p * (2 * m + 1)

/-- **Basic integer group determinants of $C_4^2$.** For every integer $m$, the integers
$16m + 1$, $2^{16} (4m + 1)$, $2^{16} (4m - 1)$ and $2^{16} \cdot 2m$ all lie in the set
$S(C_4^2)$ of integer group determinants of $C_4^2 = \mathbb{Z}/4 \times \mathbb{Z}/4$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 20 (`integers-2024-A30-lem-20`). -/
public theorem_wanted c4Sq_integerGroupDeterminants_basic_members (m : ℤ) :
    16 * m + 1 ∈ integerGroupDeterminants (Fin 4 × Fin 4) ∧
      2 ^ 16 * (4 * m + 1) ∈ integerGroupDeterminants (Fin 4 × Fin 4) ∧
      2 ^ 16 * (4 * m - 1) ∈ integerGroupDeterminants (Fin 4 × Fin 4) ∧
      2 ^ 16 * (2 * m) ∈ integerGroupDeterminants (Fin 4 × Fin 4)

/-- **Four-factor integer group determinants of $C_4^2$.** Let
$P$ be the set of positive primes $p \equiv 5 \pmod 8$, and let $k, l, m, n$ be integers such
that $16l - 3$, $16l + 5$, $16m - 3$, $16m + 5$, $16n - 3$ and $16n + 5$ all lie in $P$. Then
the four integers $(16k - 3)(16l + 5)(16m - 3)(16n - 3)$,
$(16k - 3)(16l + 5)(16m + 5)(16n + 5)$, $(16k + 5)(16l - 3)(16m - 3)(16n - 3)$ and
$(16k + 5)(16l - 3)(16m + 5)(16n + 5)$ all lie in the set $S(C_4^2)$ of integer group
determinants of $C_4^2 = \mathbb{Z}/4 \times \mathbb{Z}/4$.

All six membership hypotheses are assumed for each of the four conclusions, as in the paper's
shared hypothesis list.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 21 (`integers-2024-A30-lem-21`). -/
public theorem_wanted c4Sq_integerGroupDeterminants_four_factor_members (k l m n : ℤ)
    (hl₃ : 16 * l - 3 ∈ primesFiveModEight) (hl₅ : 16 * l + 5 ∈ primesFiveModEight)
    (hm₃ : 16 * m - 3 ∈ primesFiveModEight) (hm₅ : 16 * m + 5 ∈ primesFiveModEight)
    (hn₃ : 16 * n - 3 ∈ primesFiveModEight) (hn₅ : 16 * n + 5 ∈ primesFiveModEight) :
    (16 * k - 3) * (16 * l + 5) * (16 * m - 3) * (16 * n - 3) ∈
        integerGroupDeterminants (Fin 4 × Fin 4) ∧
      (16 * k - 3) * (16 * l + 5) * (16 * m + 5) * (16 * n + 5) ∈
        integerGroupDeterminants (Fin 4 × Fin 4) ∧
      (16 * k + 5) * (16 * l - 3) * (16 * m - 3) * (16 * n - 3) ∈
        integerGroupDeterminants (Fin 4 × Fin 4) ∧
      (16 * k + 5) * (16 * l - 3) * (16 * m + 5) * (16 * n + 5) ∈
        integerGroupDeterminants (Fin 4 × Fin 4)

/-- **Integer group determinants of $C_4^2$ of the form $2^{15} p (2m + 1)$.** Let $P$ be
the set of positive primes $p \equiv 5 \pmod 8$. For every integer $m$ and every $p \in P$, the
integer $2^{15} p (2m + 1)$ lies in the set $S(C_4^2)$ of integer group determinants of
$C_4^2 = \mathbb{Z}/4 \times \mathbb{Z}/4$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 22 (`integers-2024-A30-lem-22`). -/
public theorem_wanted c4Sq_integerGroupDeterminants_two_pow_fifteen (m p : ℤ)
    (hp : p ∈ primesFiveModEight) :
    2 ^ 15 * p * (2 * m + 1) ∈ integerGroupDeterminants (Fin 4 × Fin 4)

/-- **Integer group determinants of $C_4 \times C_4$.** Let $C_4$ be the cyclic group of order
$4$, let $S(C_4^2)$ be the set of integer group determinants of $C_4 \times C_4$, let $P$ be the
set of positive primes $p \equiv -3 \pmod 8$, and let $A$ be the set of products
$(8k-3)(8l-3)(8m-3)(8n-3)$ with $k, l, m, n \in \mathbb{Z}$, $8l-3, 8m-3, 8n-3 \in P$ and
$k + l \not\equiv m + n \pmod 2$. Then $A$ is a proper subset of
$\{16m - 7 \mid m \in \mathbb{Z}\}$, and

$$S(C_4^2) = \{16m + 1 \mid m \in \mathbb{Z}\} \cup
\{2^{15} p (2m + 1) \mid p \in P, m \in \mathbb{Z}\} \cup
\{2^{16} m \mid m \in \mathbb{Z}\} \cup A.$$

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Theorem 1 (`integers-2024-A30-thm-1`). -/
public theorem_wanted integerGroupDeterminants_c4Sq :
    c4SqExceptionalSet ⊂ {z | ∃ m : ℤ, z = 16 * m - 7} ∧
      integerGroupDeterminants (Fin 4 × Fin 4) =
        {z | ∃ m : ℤ, z = 16 * m + 1} ∪
          {z | ∃ p ∈ primesFiveModEight, ∃ m : ℤ, z = 2 ^ 15 * p * (2 * m + 1)} ∪
          {z | ∃ m : ℤ, z = 2 ^ 16 * m} ∪ c4SqExceptionalSet

end

end MetaMathlibExt
