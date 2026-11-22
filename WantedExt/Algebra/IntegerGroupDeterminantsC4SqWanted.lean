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

/-- The set `S(G)` of integer group determinants of a finite abelian group `G`
(written additively): all values `det (x_{g - h})_{g,h ∈ G}` with `x : G → ℤ`.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Section 1 (definition of `S(G)`). -/
public def integerGroupDeterminants (G : Type*) [AddGroup G] [Fintype G] [DecidableEq G] :
    Set ℤ :=
  Set.range fun x : G → ℤ => (circulant x).det

/-- `1 ∈ S(G)`: the indicator of the identity gives the identity matrix.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Section 1 (definition of `S(G)`). -/
public theorem one_mem_integerGroupDeterminants (G : Type*) [AddGroup G] [Fintype G]
    [DecidableEq G] : (1 : ℤ) ∈ integerGroupDeterminants G :=
  ⟨Pi.single 0 1, by simp⟩

/-- The group determinant `D₄(x₀, x₁, x₂, x₃)` of the cyclic group `C₄`, i.e. the
`4 × 4` circulant determinant, over any commutative ring.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Section 2 (definition of `D_n`). -/
public def circulantDetFour {R : Type*} [CommRing R] (x : Fin 4 → R) : R :=
  (circulant x).det

/-- `D₄(1, 0, 0, 0) = 1`.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Section 2 (definition of `D_n`). -/
public theorem circulantDetFour_single_one {R : Type*} [CommRing R] :
    circulantDetFour (Pi.single 0 1 : Fin 4 → R) = 1 := by
  simp [circulantDetFour]

/-- The paper's `b_i = (a_i + a_{i+8}) + (a_{i+4} + a_{i+12})`, `0 ≤ i ≤ 3`.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Section 2 (notation after Corollary 2). -/
public def c4SqB (a : Fin 4 × Fin 4 → ℤ) (i : Fin 4) : ℤ :=
  a (i, 0) + a (i, 2) + (a (i, 1) + a (i, 3))

/-- The paper's `c_i = (a_i + a_{i+8}) - (a_{i+4} + a_{i+12})`, `0 ≤ i ≤ 3`.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Section 2 (notation after Corollary 2). -/
public def c4SqC (a : Fin 4 × Fin 4 → ℤ) (i : Fin 4) : ℤ :=
  a (i, 0) + a (i, 2) - (a (i, 1) + a (i, 3))

/-- The paper's `d_i = a_i - a_{i+8}`, `0 ≤ i ≤ 7` (so `d_i = a (i, 0) - a (i, 2)`
and `d_{i+4} = a (i, 1) - a (i, 3)` for `i ≤ 3`).

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Section 2 (notation after Corollary 2). -/
public def c4SqD (a : Fin 4 × Fin 4 → ℤ) : Fin 8 → ℤ :=
  ![a (0, 0) - a (0, 2), a (1, 0) - a (1, 2), a (2, 0) - a (2, 2), a (3, 0) - a (3, 2),
    a (0, 1) - a (0, 3), a (1, 1) - a (1, 3), a (2, 1) - a (2, 3), a (3, 1) - a (3, 3)]

/-- The paper's `α_i = d_i + √-1 d_{i+4}`, `0 ≤ i ≤ 3`, as a Gaussian integer.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Section 2 (notation after Corollary 2). -/
public def c4SqAlpha (a : Fin 4 × Fin 4 → ℤ) : Fin 4 → GaussianInt :=
  ![⟨c4SqD a 0, c4SqD a 4⟩, ⟨c4SqD a 1, c4SqD a 5⟩, ⟨c4SqD a 2, c4SqD a 6⟩,
    ⟨c4SqD a 3, c4SqD a 7⟩]

/-- The paper's `β = (α₀ + α₂)² - (α₁ + α₃)²`.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Section 2 (definition before Lemma 1). -/
public def c4SqBeta (a : Fin 4 × Fin 4 → ℤ) : GaussianInt :=
  (c4SqAlpha a 0 + c4SqAlpha a 2) ^ 2 - (c4SqAlpha a 1 + c4SqAlpha a 3) ^ 2

/-- The paper's `γ = (α₀ - α₂)² + (α₁ - α₃)²`.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Section 2 (definition before Lemma 1). -/
public def c4SqGamma (a : Fin 4 × Fin 4 → ℤ) : GaussianInt :=
  (c4SqAlpha a 0 - c4SqAlpha a 2) ^ 2 + (c4SqAlpha a 1 - c4SqAlpha a 3) ^ 2

/-- For the identity indicator `a = δ_{(0,0)}` one has `b = c = (1, 0, 0, 0)`,
`d = (1, 0, …, 0)` and `β = γ = 1`.

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

/-- The set `P` of (positive) primes `p ≡ -3 (mod 8)`.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Theorem 1 (definition of `P`). -/
public def primesFiveModEight : Set ℤ :=
  {p | 0 < p ∧ Prime p ∧ p % 8 = 5}

/-- `5 ∈ P` and `13 ∈ P`.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Theorem 1 (definition of `P`). -/
public theorem five_thirteen_mem_primesFiveModEight :
    (5 : ℤ) ∈ primesFiveModEight ∧ (13 : ℤ) ∈ primesFiveModEight :=
  ⟨⟨by norm_num, Int.prime_iff_natAbs_prime.2 (by decide), by norm_num⟩,
    ⟨by norm_num, Int.prime_iff_natAbs_prime.2 (by decide), by norm_num⟩⟩

/-- The paper's set
`A = {(8k-3)(8l-3)(8m-3)(8n-3) | k ∈ ℤ, 8l-3, 8m-3, 8n-3 ∈ P, k + l ≢ m + n (mod 2)}`.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Theorem 1 (definition of `A`). -/
public def c4SqExceptionalSet : Set ℤ :=
  {z | ∃ k l m n : ℤ, 8 * l - 3 ∈ primesFiveModEight ∧ 8 * m - 3 ∈ primesFiveModEight ∧
    8 * n - 3 ∈ primesFiveModEight ∧ ¬ k + l ≡ m + n [ZMOD 2] ∧
    z = (8 * k - 3) * (8 * l - 3) * (8 * m - 3) * (8 * n - 3)}

/-- `1625 = 5 · 5 · 5 · 13 ∈ A` (`k = l = m = 1`, `n = 2`).

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Theorem 1 (definition of `A`). -/
public theorem mem_c4SqExceptionalSet_1625 : (1625 : ℤ) ∈ c4SqExceptionalSet :=
  ⟨1, 1, 1, 2, five_thirteen_mem_primesFiveModEight.1, five_thirteen_mem_primesFiveModEight.1,
    five_thirteen_mem_primesFiveModEight.2, by decide, by norm_num⟩

/-- **Corollary 1.** `D₄(x₀, x₁, x₂, x₃) = {(x₀ + x₂)² - (x₁ + x₃)²}{(x₀ - x₂)² + (x₁ - x₃)²}`
over any commutative ring. The paper's intermediate factorization through `D₂` is
omitted.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Corollary 1 (`integers-2024-A30-cor-1`). -/
public theorem_wanted circulantDetFour_eq {R : Type*} [CommRing R] (x₀ x₁ x₂ x₃ : R) :
    circulantDetFour ![x₀, x₁, x₂, x₃] =
      ((x₀ + x₂) ^ 2 - (x₁ + x₃) ^ 2) * ((x₀ - x₂) ^ 2 + (x₁ - x₃) ^ 2)

/-- **Corollary 2.** For complex variables `y`, the `C₄²` group determinant factors as
`∏_{k=0}^{3} D₄(∑_s i^{ks} y_{4s}, ∑_s i^{ks} y_{1+4s}, ∑_s i^{ks} y_{2+4s}, ∑_s i^{ks} y_{3+4s})`.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Corollary 2 (`integers-2024-A30-cor-2`). -/
public theorem_wanted c4Sq_groupDet_eq_prod_circulantDetFour (y : Fin 4 × Fin 4 → ℂ) :
    (circulant y).det =
      ∏ k : Fin 4, circulantDetFour fun r : Fin 4 =>
        ∑ s : Fin 4, Complex.I ^ (k.val * s.val) * y (r, s)

/-- **Corollary 3.** If `a² + b² ≡ -3 (mod 8)`, then `a² + b² = (8k + 1)(8l - 3)` for some
`k ∈ ℤ` and `8l - 3 ∈ P`.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Corollary 3 (`integers-2024-A30-cor-3`). -/
public theorem_wanted sq_add_sq_eq_mul_of_mod_eight (a b : ℤ) (h : a ^ 2 + b ^ 2 ≡ -3 [ZMOD 8]) :
    ∃ k l : ℤ, 8 * l - 3 ∈ primesFiveModEight ∧ a ^ 2 + b ^ 2 = (8 * k + 1) * (8 * l - 3)

/-- **Lemma 1.** The norms `β β̄` and `γ γ̄` as products of two sums of two squares in the `d_i`.

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

/-- **Lemma 2.** `D_{4×4}(a) ≡ D₄(b) ≡ D₄(c) ≡ β β̄ ≡ γ γ̄ (mod 2)`.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 2 (`integers-2024-A30-lem-2`). -/
public theorem_wanted c4Sq_groupDet_congr_mod_two (a : Fin 4 × Fin 4 → ℤ) :
    (circulant a).det ≡ circulantDetFour (c4SqB a) [ZMOD 2] ∧
      circulantDetFour (c4SqB a) ≡ circulantDetFour (c4SqC a) [ZMOD 2] ∧
      circulantDetFour (c4SqC a) ≡ Zsqrtd.norm (c4SqBeta a) [ZMOD 2] ∧
      Zsqrtd.norm (c4SqBeta a) ≡ Zsqrtd.norm (c4SqGamma a) [ZMOD 2]

/-- **Lemma 3.** `β β̄ = {∑ (d_i + d_{i+2})²}² - 4{…}²` and the analogous formula for `γ γ̄`.

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

/-- **Lemma 4.** The difference of the squared sums of squares in Lemma 3 equals
`8 (∑ d_i²)(d₀d₂ + d₄d₆ + d₁d₃ + d₅d₇)`.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 4 (`integers-2024-A30-lem-4`). -/
public theorem_wanted c4SqD_sum_sq_sq_sub_sq (a : Fin 4 × Fin 4 → ℤ) :
    let d := c4SqD a
    ((d 0 + d 2) ^ 2 + (d 4 + d 6) ^ 2 + (d 1 + d 3) ^ 2 + (d 5 + d 7) ^ 2) ^ 2 -
        ((d 0 - d 2) ^ 2 + (d 4 - d 6) ^ 2 + (d 1 - d 3) ^ 2 + (d 5 - d 7) ^ 2) ^ 2 =
      8 * (d 0 ^ 2 + d 2 ^ 2 + d 4 ^ 2 + d 6 ^ 2 + d 1 ^ 2 + d 3 ^ 2 + d 5 ^ 2 + d 7 ^ 2) *
        (d 0 * d 2 + d 4 * d 6 + d 1 * d 3 + d 5 * d 7)

/-- **Lemma 5.** Five congruences mod 4 between doubled cross terms in the `d_i` and
cross terms in the `b_i`, `c_i`.

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

/-- **Lemma 6.** `D₄(2k+1, 2l, 2m, 2n) ≡ 8m + 1` and
`D₄(2k, 2l+1, 2m+1, 2n+1) ≡ 8(k + l + n) - 3 (mod 16)`.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 6 (`integers-2024-A30-lem-6`). -/
public theorem_wanted circulantDetFour_mod_sixteen (k l m n : ℤ) :
    circulantDetFour ![2 * k + 1, 2 * l, 2 * m, 2 * n] ≡ 8 * m + 1 [ZMOD 16] ∧
      circulantDetFour ![2 * k, 2 * l + 1, 2 * m + 1, 2 * n + 1] ≡ 8 * (k + l + n) - 3 [ZMOD 16]

/-- **Lemma 7.** Powers of `2` dividing `D₄` at the four parity patterns of the arguments
(`2^e ℤ_odd` is written `∃ t, x = 2^e (2t + 1)`; "otherwise" is the negation of the
earlier cases).

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

/-- **Lemma 8.** `S(C₄²) ∩ ℤ_odd ⊆ {16m + 1 | m ∈ ℤ} ∪ A`.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 8 (`integers-2024-A30-lem-8`). -/
public theorem_wanted odd_mem_integerGroupDeterminants_c4Sq {z : ℤ}
    (hz : z ∈ integerGroupDeterminants (Fin 4 × Fin 4)) (hodd : Odd z) :
    (∃ m : ℤ, z = 16 * m + 1) ∨ z ∈ c4SqExceptionalSet

/-- **Lemma 9.** If `b₀ + b₂ ≢ b₁ + b₃ (mod 2)`, the residues of
`(b₀b₂ + b₁b₃, c₀c₂ + c₁c₃) (mod 4)` determine the shape of `D₄(b) D₄(c)`.

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

/-- **Lemma 10.** If `b₀ + b₂ ≢ b₁ + b₃ (mod 2)`, then
`D₄(b) D₄(c) ≡ 1 - 4(b₀b₂ + b₁b₃ + c₀c₂ + c₁c₃) (mod 16)`.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 10 (`integers-2024-A30-lem-10`). -/
public theorem_wanted c4Sq_circulantDetFour_product_mod_sixteen (a : Fin 4 × Fin 4 → ℤ)
    (h : ¬ c4SqB a 0 + c4SqB a 2 ≡ c4SqB a 1 + c4SqB a 3 [ZMOD 2]) :
    circulantDetFour (c4SqB a) * circulantDetFour (c4SqC a) ≡
      1 - 4 * (c4SqB a 0 * c4SqB a 2 + c4SqB a 1 * c4SqB a 3 +
        c4SqC a 0 * c4SqC a 2 + c4SqC a 1 * c4SqC a 3) [ZMOD 16]

/-- **Lemma 11.** If `b₀ + b₂ ≢ b₁ + b₃ (mod 2)` and `β β̄ ≡ -3 (mod 8)`, then
`D₄(b) D₄(c) = (8k - 3)(8l - 3)` with `8l - 3 ∈ P`, where `k ≢ l` or `k ≡ l (mod 2)`
according as `b₀b₂ + b₁b₃ + c₀c₂ + c₁c₃ ≡ 0` or `2 (mod 4)`.

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

/-- **Lemma 12.** If `b₀ + b₂ ≢ b₁ + b₃ (mod 2)`, then
`β β̄ - γ γ̄ ≡ 4(b₀b₂ + b₁b₃ + c₀c₂ + c₁c₃) (mod 16)`.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 12 (`integers-2024-A30-lem-12`). -/
public theorem_wanted c4Sq_norm_beta_sub_norm_gamma_mod_sixteen (a : Fin 4 × Fin 4 → ℤ)
    (h : ¬ c4SqB a 0 + c4SqB a 2 ≡ c4SqB a 1 + c4SqB a 3 [ZMOD 2]) :
    Zsqrtd.norm (c4SqBeta a) - Zsqrtd.norm (c4SqGamma a) ≡
      4 * (c4SqB a 0 * c4SqB a 2 + c4SqB a 1 * c4SqB a 3 +
        c4SqC a 0 * c4SqC a 2 + c4SqC a 1 * c4SqC a 3) [ZMOD 16]

/-- **Lemma 13.** If `b₀ + b₂ ≢ b₁ + b₃ (mod 2)` and `β β̄ ≡ -3 (mod 8)`, then
`β β̄ γ γ̄ = (8j + 1)(8m - 3)(8n - 3)` with `8m - 3, 8n - 3 ∈ P`, where `j ≡ m + n` or
`j ≢ m + n (mod 2)` according as `b₀b₂ + b₁b₃ + c₀c₂ + c₁c₃ ≡ 0` or `2 (mod 4)`.

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

/-- **Lemma 14.** `S(C₄²) ∩ 2ℤ ⊆ 2^15 ℤ` and
`S(C₄²) ∩ 2^15 ℤ_odd ⊆ {2^15 p (2m + 1) | p ∈ P, m ∈ ℤ}`.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 14 (`integers-2024-A30-lem-14`). -/
public theorem_wanted even_mem_integerGroupDeterminants_c4Sq {z : ℤ}
    (hz : z ∈ integerGroupDeterminants (Fin 4 × Fin 4)) :
    (2 ∣ z → 2 ^ 15 ∣ z) ∧
      ((∃ t : ℤ, z = 2 ^ 15 * (2 * t + 1)) →
        ∃ p ∈ primesFiveModEight, ∃ m : ℤ, z = 2 ^ 15 * p * (2 * m + 1))

/-- **Lemma 15.** Powers of `2` dividing `D₄(b) D₄(c)` according to the parities of the
`b_i` (`2^e ℤ_odd` is written `∃ t, x = 2^e (2t + 1)`).

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

/-- **Lemma 16.** Powers of `2` dividing `β β̄ γ γ̄` according to the parities of
`b₀ + b₂` and `b₁ + b₃`, with
`d = {(d₀+d₂)(d₅+d₇) + (d₄+d₆)(d₁+d₃)}{(d₀-d₂)(d₁-d₃) + (d₄-d₆)(d₅-d₇)}` in the odd case.

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

/-- **Lemma 17.** Two situations in which `b₀b₂ + b₁b₃ + c₀c₂ + c₁c₃ ≡ 2 (mod 4)`.

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

/-- **Lemma 18.** If `b₀ + b₂ ≡ b₁ + b₃ ≡ 0 (mod 2)`, `β β̄ γ γ̄ ∈ 2^4 ℤ_odd` and
`b₀b₂ + b₁b₃ + c₀c₂ + c₁c₃ ≡ 2 (mod 4)`, then `β β̄ γ γ̄ = 2^4 p (2m + 1)` with `p ∈ P`.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 18 (`integers-2024-A30-lem-18`). -/
public theorem_wanted c4Sq_norm_beta_gamma_prime_factor (a : Fin 4 × Fin 4 → ℤ)
    (h₀ : c4SqB a 0 + c4SqB a 2 ≡ 0 [ZMOD 2]) (h₁ : c4SqB a 1 + c4SqB a 3 ≡ 0 [ZMOD 2])
    (hN : ∃ t, Zsqrtd.norm (c4SqBeta a) * Zsqrtd.norm (c4SqGamma a) = 2 ^ 4 * (2 * t + 1))
    (hQ : c4SqB a 0 * c4SqB a 2 + c4SqB a 1 * c4SqB a 3 +
      c4SqC a 0 * c4SqC a 2 + c4SqC a 1 * c4SqC a 3 ≡ 2 [ZMOD 4]) :
    ∃ p ∈ primesFiveModEight, ∃ m : ℤ,
      Zsqrtd.norm (c4SqBeta a) * Zsqrtd.norm (c4SqGamma a) = 2 ^ 4 * p * (2 * m + 1)

/-- **Lemma 19.** If `b₀ + b₂ ≡ b₁ + b₃ ≡ 1 (mod 2)`, `D₄(b) D₄(c) ∈ 2^8 ℤ_odd` and
`β β̄ γ γ̄ ∈ 2^7 ℤ_odd`, then `D₄(b) D₄(c) β β̄ γ γ̄ = 2^15 p (2m + 1)` with `p ∈ P`.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 19 (`integers-2024-A30-lem-19`). -/
public theorem_wanted c4Sq_groupDet_factors_prime_factor (a : Fin 4 × Fin 4 → ℤ)
    (h₀ : c4SqB a 0 + c4SqB a 2 ≡ 1 [ZMOD 2]) (h₁ : c4SqB a 1 + c4SqB a 3 ≡ 1 [ZMOD 2])
    (hD : ∃ t, circulantDetFour (c4SqB a) * circulantDetFour (c4SqC a) = 2 ^ 8 * (2 * t + 1))
    (hN : ∃ t, Zsqrtd.norm (c4SqBeta a) * Zsqrtd.norm (c4SqGamma a) = 2 ^ 7 * (2 * t + 1)) :
    ∃ p ∈ primesFiveModEight, ∃ m : ℤ,
      circulantDetFour (c4SqB a) * circulantDetFour (c4SqC a) *
        (Zsqrtd.norm (c4SqBeta a) * Zsqrtd.norm (c4SqGamma a)) = 2 ^ 15 * p * (2 * m + 1)

/-- **Lemma 20.** For every `m ∈ ℤ`, `16m + 1`, `2^16 (4m + 1)`, `2^16 (4m - 1)` and
`2^16 (2m)` lie in `S(C₄²)`.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 20 (`integers-2024-A30-lem-20`). -/
public theorem_wanted c4Sq_integerGroupDeterminants_basic_members (m : ℤ) :
    16 * m + 1 ∈ integerGroupDeterminants (Fin 4 × Fin 4) ∧
      2 ^ 16 * (4 * m + 1) ∈ integerGroupDeterminants (Fin 4 × Fin 4) ∧
      2 ^ 16 * (4 * m - 1) ∈ integerGroupDeterminants (Fin 4 × Fin 4) ∧
      2 ^ 16 * (2 * m) ∈ integerGroupDeterminants (Fin 4 × Fin 4)

/-- **Lemma 21.** If `16l - 3, 16l + 5, 16m - 3, 16m + 5, 16n - 3, 16n + 5 ∈ P`, then for
every `k ∈ ℤ` the four products of one factor `16k - 3` or `16k + 5` with three of these primes
in the displayed residue patterns mod 16 lie in `S(C₄²)` (the paper's shared hypothesis list).

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

/-- **Lemma 22.** For every `m ∈ ℤ` and `p ∈ P`, `2^15 p (2m + 1) ∈ S(C₄²)`.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 22 (`integers-2024-A30-lem-22`). -/
public theorem_wanted c4Sq_integerGroupDeterminants_two_pow_fifteen (m p : ℤ)
    (hp : p ∈ primesFiveModEight) :
    2 ^ 15 * p * (2 * m + 1) ∈ integerGroupDeterminants (Fin 4 × Fin 4)

/-- **Theorem 1.** `S(C₄²) = {16m + 1, 2^15 p (2m + 1), 2^16 m | m ∈ ℤ, p ∈ P} ∪ A`, and
`A ⊊ {16m - 7 | m ∈ ℤ}`.

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
