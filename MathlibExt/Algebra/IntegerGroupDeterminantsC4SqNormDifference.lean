/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import MathlibExt.Algebra.IntegerGroupDeterminantsC4SqSums
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# The difference of two Gaussian norms for `C₄ × C₄`

For the Gaussian integers `c4SqBeta a` and `c4SqGamma a` of Yamaguchi and Yamaguchi,
`c4Sq_norm_beta_sub_norm_gamma_mod_sixteen` computes their norm difference modulo 16
when the even-indexed and odd-indexed sums have opposite parity.
-/

namespace MetaMathlibExt

@[expose] public section

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

namespace C4SqNormDifference

private theorem norm_sq_sub_sq (u v : GaussianInt) :
    (u ^ 2 - v ^ 2).norm = (u.re ^ 2 + u.im ^ 2 + v.re ^ 2 + v.im ^ 2) ^ 2 -
      4 * (u.re * v.re + u.im * v.im) ^ 2 := by
  simp [Zsqrtd.norm, sq]
  ring

private theorem norm_sq_add_sq (u v : GaussianInt) :
    (u ^ 2 + v ^ 2).norm = (u.re ^ 2 + u.im ^ 2 + v.re ^ 2 + v.im ^ 2) ^ 2 -
      4 * (u.re * v.im - u.im * v.re) ^ 2 := by
  simp [Zsqrtd.norm, sq]
  ring

end C4SqNormDifference

open C4SqNormDifference in
/-- **The difference of the norms of β and γ modulo 16 (C₄²).** Let $a$ be an integer-valued
function on $C_4^2 = \mathbb{Z}/4 \times \mathbb{Z}/4$, with associated integers $b_i$, $c_i$
$(0 \le i \le 3)$ and Gaussian integers $\beta$, $\gamma$, and write $\beta\bar\beta$,
$\gamma\bar\gamma$ for the norms of $\beta$ and $\gamma$. If
$b_0 + b_2 \not\equiv b_1 + b_3 \pmod 2$, then
$\beta\bar\beta - \gamma\bar\gamma \equiv 4(b_0b_2 + b_1b_3 + c_0c_2 + c_1c_3) \pmod{16}$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 12 (`integers-2024-A30-lem-12`). -/
public theorem c4Sq_norm_beta_sub_norm_gamma_mod_sixteen (a : Fin 4 × Fin 4 → ℤ)
    (h : ¬ c4SqB a 0 + c4SqB a 2 ≡ c4SqB a 1 + c4SqB a 3 [ZMOD 2]) :
    Zsqrtd.norm (c4SqBeta a) - Zsqrtd.norm (c4SqGamma a) ≡
      4 * (c4SqB a 0 * c4SqB a 2 + c4SqB a 1 * c4SqB a 3 +
        c4SqC a 0 * c4SqC a 2 + c4SqC a 1 * c4SqC a 3) [ZMOD 16] := by
  let d := c4SqD a
  let sumSq := d 0 ^ 2 + d 2 ^ 2 + d 4 ^ 2 + d 6 ^ 2 + d 1 ^ 2 + d 3 ^ 2 + d 5 ^ 2 + d 7 ^ 2
  let cross := d 0 * d 2 + d 4 * d 6 + d 1 * d 3 + d 5 * d 7
  let dot := (d 0 + d 2) * (d 1 + d 3) + (d 4 + d 6) * (d 5 + d 7)
  let skew := (d 0 - d 2) * (d 5 - d 7) - (d 4 - d 6) * (d 1 - d 3)
  have hnorm : (c4SqBeta a).norm - (c4SqGamma a).norm =
      8 * sumSq * cross - 4 * (dot ^ 2 - skew ^ 2) := by
    rw [c4SqBeta, c4SqGamma, norm_sq_sub_sq, norm_sq_add_sq, mul_sub]
    dsimp only [sumSq, cross, d]
    rw [← c4SqD_sum_sq_sq_sub_sq a]
    dsimp [c4SqAlpha, dot, skew, d]
    omega
  -- Modulo two, each row sum is also the sum of the two differences in that row.
  have hpar : (d 0 : ZMod 2) + d 2 + (d 4 + (d 6 : ZMod 2)) ≠
      (d 1 : ZMod 2) + d 3 + (d 5 + (d 7 : ZMod 2)) := by
    have hb := h ∘ (ZMod.intCast_eq_intCast_iff _ _ 2).mp
    simpa [d, c4SqD, c4SqB, ZModModule.sub_eq_add, add_assoc, add_comm, add_left_comm] using hb
  have hsum : sumSq ≡ 1 [ZMOD 2] := by
    apply (ZMod.intCast_eq_intCast_iff _ _ 2).mp
    have sq_self : ∀ x : ZMod 2, x ^ 2 = x := by decide
    have add_one : ∀ x y : ZMod 2, x ≠ y → x + y = 1 := by decide
    simpa [sumSq, sq_self, add_assoc] using add_one _ _ hpar
  have hsquares : dot ^ 2 ≡ skew ^ 2 [ZMOD 4] := by
    simp only [Int.ModEq, Int.sq_emod_four]
    apply (ZMod.intCast_eq_intCast_iff _ _ 2).mp
    have cross_eq : ∀ x y z w : ZMod 2, x + y ≠ z + w → x * z + y * w = x * w + y * z := by
      decide
    simpa [dot, skew, ZModModule.sub_eq_add] using cross_eq _ _ _ _ hpar
  -- Multiplication by eight or four lifts these congruences to modulus sixteen.
  have hmain : 8 * sumSq * cross ≡ 8 * cross [ZMOD 16] := by
    simpa using (hsum.mul_left' (c := 8)).mul_right cross
  have hcancel : 4 * (dot ^ 2 - skew ^ 2) ≡ 0 [ZMOD 16] := by
    exact Int.modEq_zero_iff_dvd.mpr (mul_dvd_mul_left 4 hsquares.symm.dvd)
  calc
    _ = 8 * sumSq * cross - 4 * (dot ^ 2 - skew ^ 2) := hnorm
    _ ≡ 8 * cross [ZMOD 16] := by simpa only [sub_zero] using hmain.sub hcancel
    _ ≡ _ [ZMOD 16] := by
      apply (ZMod.intCast_eq_intCast_iff _ _ 16).mp
      simp [cross, d, c4SqD, c4SqB, c4SqC]
      grind only

end

end MetaMathlibExt
