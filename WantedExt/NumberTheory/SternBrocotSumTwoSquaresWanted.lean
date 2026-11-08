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

/-- Convergents as paths. Let `A_n / B_n` be the convergents of `[q₀; q₁, q₂, …]`, with
`A_n = q_n A_{n-1} + A_{n-2}`, `B_n = q_n B_{n-1} + B_{n-2}`, `A_{-1} = 1`, `A_0 = q₀`,
`B_{-1} = 0`, `B_0 = 1`; here `A k`, `B k` stand for `A_{k-1}`, `B_{k-1}`. The path
`W_n = R^{q₀} L^{q₁} ⋯` (alternating, `n + 1` blocks) equals `!![A_{n-1}, A_n; B_{n-1}, B_n]`
when it ends with an `R`-move (`n` even) and `!![A_n, A_{n-1}; B_n, B_{n-1}]` when it ends with an
`L`-move (`n` odd). The last move is read off the parity of `n`, which is the paper's case split
when every `q_i ≥ 1`; the identity is stated for all `q_i ∈ ℕ`.

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

/-- Perron's lemma. Let `p ≡ 1 (mod 4)` be prime and `0 < x₀ < p/2` with `x₀² ≡ -1 (mod p)`.
Then the continued fraction of `p / x₀` has an even number of terms and is palindromic. Stated
as the existence of a palindromic expansion of even length with positive terms; since
`x₀ < p/2` forces `q₀ ≥ 2`, such an expansion is the canonical one (the other expansion ends
in `1`).

Source: Hongshen Chua, *Binary Trees and Sum of Two Squares*, INTEGERS 26 (2026), Article A76,
Lemma 1 (Perron) (`integers-2026-A76-lem-1`). -/
public theorem_wanted exists_palindrome_continuedFraction_div {p x₀ : ℕ} (hp : p.Prime)
    (hp4 : p % 4 = 1) (hx : (x₀ ^ 2 + 1) % p = 0) (hx₀ : 0 < x₀) (hxp : 2 * x₀ < p) :
    ∃ qs : List ℕ, Even qs.length ∧ qs.reverse = qs ∧ (∀ a ∈ qs, 1 ≤ a) ∧
      (p : ℚ) / x₀ = qs.foldr (fun a acc => (a : ℚ) + acc⁻¹) 0

/-- The two squares from the Stern–Brocot tree. With `p`, `x₀` as in Lemma 1, let
`p / x₀ = [q₀, q₁, …, q_n, q_n, …, q₁, q₀]` (all `q_i ≥ 1`) and
`M = R^{q₀ - 1} L^{q₁} ⋯ S^{q_n}` (alternating moves, `S = R` for even `n`, `L` for odd `n`).
If `x / y` is the fraction of the path `Mᵀ` in the Stern–Brocot tree, i.e.
`(x, y) = Mᵀ (1, 1)ᵀ`, then `p = x² + y²`.

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
