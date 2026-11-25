/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.BinomialModTwoRunLength

/-!
# Linear representation of the run length transform

The run length transform of a linear recurrence is computed by a product of two matrices
indexed by the binary digits of the input, as in Rampersad and Wiebe's Theorem 1.
-/

namespace MetaMathlibExt

open Matrix

/-- **Run length transform of a linear recurrence (Rampersad–Wiebe Theorem 1).** Let $r \ge 0$, let
$d_0, \dots, d_r$ be integers, and let $S : \mathbb{N} \to \mathbb{Z}$ satisfy $S(0) = 1$ and
$S(m + 1) = d_0 S(m) + d_1 S(m - 1) + \dots + d_r S(m - r)$ for all $m \ge r$. Let $T$ be the run
length transform of $S$, let $v = (1, 0, \dots, 0)$ and $w = (S(0), \dots, S(r))^\top$, let
$\gamma(0)$ be the $(r + 1) \times (r + 1)$ matrix with first column $w$ and zeros elsewhere, and
let $\gamma(1)$ be the $(r + 1) \times (r + 1)$ companion matrix with ones on the superdiagonal,
last row $(d_r, \dots, d_0)$ and zeros elsewhere. Then for every natural number $n$ with binary
digits $b_1 b_2 \cdots b_t$, most significant first,
$T(n) = v \, \gamma(b_1) \gamma(b_2) \cdots \gamma(b_t) \, w$, where for $n = 0$ the product of
matrices is empty and equals the identity.

Source: Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and
2-Regular Sequences*, INTEGERS 24 (2024), Article A73, Theorem 1. -/
public theorem runLengthTransform_linearRecurrence_eq_linearRep (r : ℕ)
    (d : Fin (r + 1) → ℤ) (S : ℕ → ℤ) (hS0 : S 0 = 1)
    (hrec : ∀ m, r ≤ m → S (m + 1) = ∑ i : Fin (r + 1), d i * S (m - i)) (n : ℕ) :
    runLengthTransform S n = Pi.single 0 1 ⬝ᵥ
      ((((Nat.digits 2 n).reverse.map fun b =>
          if b = 0 then Matrix.of fun i j : Fin (r + 1) => if j = 0 then S i else 0
          else Matrix.of fun i j : Fin (r + 1) =>
            if (i : ℕ) < r then (if (j : ℕ) = i + 1 then 1 else 0) else d (Fin.rev j)).prod) *ᵥ
        fun i => S i) := by
  let A := Matrix.of fun i j : Fin (r + 1) =>
    if (i : ℕ) < r then (if (j : ℕ) = i + 1 then 1 else 0) else d (Fin.rev j)
  let w : Fin (r + 1) → ℤ := fun i => S i
  let Z := Matrix.of fun i j : Fin (r + 1) => if j = 0 then w i else 0
  let γ (b : ℕ) := if b = 0 then Z else A
  have hpow (c : ℕ) : (A ^ c *ᵥ w) 0 = S c := by
    simpa only [single_one_dotProduct] using
      (linearRecurrence_eq_companion_pow r d S hS0 hrec c).symm
  have hreset (x : Fin (r + 1) → ℤ) : Z *ᵥ x = x 0 • w := by
    funext i
    simp [Z, mulVec_apply_eq_sum, mul_comm]
  -- The current run of c ones is already represented by the column A ^ c *ᵥ w.
  have eval (bs : List ℕ) (hbs : ∀ b ∈ bs, b < 2) (c : ℕ) :
      ((bitRunLengths bs c).map S).prod = ((bs.reverse.map γ).prod *ᵥ (A ^ c *ᵥ w)) 0 := by
    induction bs generalizing c with
    | nil =>
      by_cases hc : c = 0 <;> simp [bitRunLengths, hc, hpow, w, hS0]
    | cons b bs ih =>
      have htail (t : ℕ) (ht : t ∈ bs) := hbs t (List.mem_cons_of_mem b ht)
      have hb := hbs b List.mem_cons_self
      simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.prod_append, List.prod_cons, List.prod_nil, mul_one, ← mulVec_mulVec]
      rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
      · rw [show γ 0 = Z from rfl, hreset, hpow, mulVec_smul]
        have ih0 := ih htail 0
        simp only [pow_zero, one_mulVec] at ih0
        by_cases hc : c = 0 <;> simp [bitRunLengths, hc, hS0, ih0]
      · rw [show γ 1 = A from rfl]
        simpa only [bitRunLengths, ↓reduceIte, pow_succ', ← mulVec_mulVec] using ih htail (c + 1)
  simpa only [runLengthTransform, binaryRunLengths, single_one_dotProduct, pow_zero, one_mulVec,
    γ, Z, A, w] using
    eval (Nat.digits 2 n) (fun _ hb => Nat.digits_lt_base (by decide) hb) 0

end MetaMathlibExt
