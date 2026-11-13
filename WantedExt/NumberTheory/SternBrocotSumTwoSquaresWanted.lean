/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Binary trees, continued fractions and sums of two squares

Statements from Hongshen Chua, *Binary Trees and Sum of Two Squares*, INTEGERS 26 (2026),
Article A76. A path in the matrix binary tree is a product of the moves
`R = !![1, 1; 0, 1]` and `L = !![1, 0; 1, 1]` (post-multiplication, starting from the identity);
the Stern–Brocot fraction of a path matrix `P` is the column vector `P (1, 1)ᵀ`. A finite
continued fraction `[q₀; q₁, …, q_m]` is evaluated as the right fold
`q₀ + (q₁ + ⋯ + (q_m + 0⁻¹)⁻¹ ⋯)⁻¹` (with `0⁻¹ = 0`). Theorem 2 (Fermat's two squares theorem)
is Mathlib's `Nat.Prime.sq_add_sq`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Continued fraction convergents as matrix paths.** Let
$R = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$ and
$L = \begin{pmatrix} 1 & 0 \\ 1 & 1 \end{pmatrix}$, as matrices over $\mathbb{N}$. Let
$q_0, q_1, q_2, \dots$ be natural numbers, and define natural numbers $A_k$, $B_k$ for $k \ge -1$
by $A_{-1} = 1$, $A_0 = q_0$, $B_{-1} = 0$, $B_0 = 1$ and, for $k \ge 1$,
$A_k = q_k A_{k-1} + A_{k-2}$ and $B_k = q_k B_{k-1} + B_{k-2}$. For $n \ge 0$ let
$W_n = M_0^{q_0} M_1^{q_1} \cdots M_n^{q_n}$, where $M_i = R$ for even $i$ and $M_i = L$ for odd
$i$. Then $W_n = \begin{pmatrix} A_{n-1} & A_n \\ B_{n-1} & B_n \end{pmatrix}$ when $n$ is even,
and $W_n = \begin{pmatrix} A_n & A_{n-1} \\ B_n & B_{n-1} \end{pmatrix}$ when $n$ is odd.

When every $q_i$ is positive, $A_k / B_k$ is the $k$-th convergent of $[q_0; q_1, q_2, \dots]$,
and the parity of $n$ says whether the path $W_n$ ends with an $R$-move or an $L$-move, which is
the paper's case split; the identity holds for all $q_i \ge 0$.

Source: Hongshen Chua, *Binary Trees and Sum of Two Squares*, INTEGERS 26 (2026), Article A76,
Theorem 1 (`integers-2026-A76-thm-1`). -/
public theorem_wanted continuedFraction_path_eq_convergents (q A B : ℕ → ℕ)
    (hA₀ : A 0 = 1) (hA₁ : A 1 = q 0) (hA : ∀ k, A (k + 2) = q (k + 1) * A (k + 1) + A k)
    (hB₀ : B 0 = 0) (hB₁ : B 1 = 1) (hB : ∀ k, B (k + 2) = q (k + 1) * B (k + 1) + B k)
    (n : ℕ) :
    ((List.range (n + 1)).map fun i =>
        (if Even i then !![1, 1; 0, 1] else !![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℕ) ^ q i).prod =
      if Even n then !![A n, A (n + 1); B n, B (n + 1)]
      else !![A (n + 1), A n; B (n + 1), B n]

/-- **Perron's lemma.** Let $p$ be a prime with $p \equiv 1 \pmod 4$, and let $x_0$ be an integer
with $0 < x_0 < p/2$ and $x_0^2 \equiv -1 \pmod p$. Then there are positive integers
$q_0, q_1, \dots, q_m$ with $m + 1$ even and $q_i = q_{m-i}$ for every $i$ such that
$p / x_0 = [q_0; q_1, \dots, q_m] = q_0 + 1/(q_1 + 1/(\cdots + 1/q_m))$.

Since $x_0 < p/2$ forces $q_0 \ge 2$, such an expansion is the canonical continued fraction of
$p / x_0$ (the other expansion ends in $1$): the continued fraction of $p / x_0$ has an even
number of terms and is palindromic.

Source: Hongshen Chua, *Binary Trees and Sum of Two Squares*, INTEGERS 26 (2026), Article A76,
Lemma 1 (Perron) (`integers-2026-A76-lem-1`). -/
public theorem_wanted exists_palindrome_continuedFraction_div {p x₀ : ℕ} (hp : p.Prime)
    (hp4 : p % 4 = 1) (hx : (x₀ ^ 2 + 1) % p = 0) (hx₀ : 0 < x₀) (hxp : 2 * x₀ < p) :
    ∃ qs : List ℕ, Even qs.length ∧ qs.reverse = qs ∧ (∀ a ∈ qs, 1 ≤ a) ∧
      (p : ℚ) / x₀ = qs.foldr (fun a acc => (a : ℚ) + acc⁻¹) 0

/-- **Sums of two squares from the Stern–Brocot tree.** Let $p$ be a prime with
$p \equiv 1 \pmod 4$, and let $x_0$ be an integer with $0 < x_0 < p/2$ and
$x_0^2 \equiv -1 \pmod p$. Let $n \ge 0$ and let $q_0, q_1, \dots, q_n$ be positive integers with
$p / x_0 = [q_0; q_1, \dots, q_n, q_n, \dots, q_1, q_0]$, where
$[a_0; a_1, \dots, a_m] = a_0 + 1/(a_1 + 1/(\cdots + 1/a_m))$. With
$R = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$ and
$L = \begin{pmatrix} 1 & 0 \\ 1 & 1 \end{pmatrix}$, let
$M = R^{q_0 - 1} M_1^{q_1} M_2^{q_2} \cdots M_n^{q_n}$, where $M_i = R$ for even $i$ and
$M_i = L$ for odd $i$. If $(x, y)^{\mathsf T} = M^{\mathsf T} (1, 1)^{\mathsf T}$, then
$p = x^2 + y^2$.

The fraction $x / y$ is the label of the path $M^{\mathsf T}$ in the Stern–Brocot tree.

Source: Hongshen Chua, *Binary Trees and Sum of Two Squares*, INTEGERS 26 (2026), Article A76,
Theorem 3 (`integers-2026-A76-thm-3`). -/
public theorem_wanted sq_add_sq_of_sternBrocot_path {p x₀ : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1)
    (hx : (x₀ ^ 2 + 1) % p = 0) (hx₀ : 0 < x₀) (hxp : 2 * x₀ < p) (n : ℕ) (q : ℕ → ℕ)
    (hq : ∀ i ≤ n, 1 ≤ q i)
    (hcf : (p : ℚ) / x₀ = ((List.range (2 * n + 2)).map fun i => q (min i (2 * n + 1 - i))).foldr
      (fun a acc => (a : ℚ) + acc⁻¹) 0) :
    let M : Matrix (Fin 2) (Fin 2) ℕ := !![1, 1; 0, 1] ^ (q 0 - 1) *
      ((List.range n).map fun i =>
        (if Even (i + 1) then !![1, 1; 0, 1] else !![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℕ) ^
          q (i + 1)).prod
    p = (M.transpose.mulVec ![1, 1] 0) ^ 2 + (M.transpose.mulVec ![1, 1] 1) ^ 2

end

end MetaMathlibExt
