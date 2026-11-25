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
public import MathlibExt.NumberTheory.PerronPalindrome
public import MathlibExt.NumberTheory.SternBrocotSumTwoSquares

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
