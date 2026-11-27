/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
public import MathlibExt.Algebra.IntegerGroupDeterminantsC4SqSums
public import MathlibExt.LinearAlgebra.Matrix.CirculantDetFour
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# A circulant determinant product congruence for `C₄ × C₄`

The factorization of the four-by-four circulant determinant gives its residue modulo 16 as a
signed linear expression in the two opposite-pair products. The signs agree for `b` and `c`.

## References

* Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for C_4^2*,
  INTEGERS 24 (2024), Article A30, pp. 1–21, Lemma 10. Instead of using the paper's
  Lemma 9, the proof uses Corollary 1 and the coordinate parity in Remark 2 (1).
* Naoya Yamaguchi and Yuka Yamaguchi,
  *Generalized Dedekind's theorem and its application to integer group determinants*,
  Journal of the Mathematical Society of Japan 76 (4) (2024), pp. 1123–1138.
  The source of the determinant factorization is its Theorem 1.1 specialized to `C₄`
  and the subgroup of order two, as noted before Corollary 1 of the first reference.
-/

namespace MetaMathlibExt

private theorem sq_mod_four (n : ℤ) : n ^ 2 ≡ n % 2 [ZMOD 4] := by
  change n ^ 2 % 4 = (n % 2) % 4
  rw [Int.sq_emod_four]
  omega

private theorem fourth_pow_mod_sixteen (n : ℤ) : n ^ 4 ≡ n % 2 [ZMOD 16] := by
  rcases Int.even_or_odd n with he | ho
  · rw [Int.even_iff.mp he, Int.modEq_iff_dvd]
    obtain ⟨k, hk⟩ := he
    refine ⟨-k ^ 4, ?_⟩
    rw [hk]
    ring
  · rw [Int.odd_iff.mp ho, Int.modEq_iff_dvd]
    obtain ⟨k, hk⟩ := Int.eight_dvd_sq_sub_one_of_odd ho
    have hs : n ^ 2 = 1 + 8 * k := by omega
    rw [show n ^ 4 = (n ^ 2) ^ 2 by ring, hs]
    refine ⟨-k - 4 * k ^ 2, ?_⟩
    ring

private theorem circulantDetFour_mod_sixteen_signed (v : Fin 4 → ℤ) :
    let p := v 0 + v 2
    let q := v 1 + v 3
    let t := v 0 * v 2 + v 1 * v 3
    circulantDetFour v ≡ (p % 2 - q % 2) * (1 - 4 * t) [ZMOD 16] := by
  intro p q t
  have hv : ![v 0, v 1, v 2, v 3] = v := by
    funext i
    fin_cases i <;> rfl
  have hs := (sq_mod_four p).sub (sq_mod_four q)
  have hf := (fourth_pow_mod_sixteen p).sub (fourth_pow_mod_sixteen q)
  calc
    circulantDetFour v = p ^ 4 - q ^ 4 - (4 * (p ^ 2 - q ^ 2)) * t := by
      rw [← hv, circulantDetFour_eq]
      dsimp only [p, q, t]
      ring
    _ ≡ (p % 2 - q % 2) - (4 * (p % 2 - q % 2)) * t [ZMOD 16] :=
      hf.sub ((Int.ModEq.mul_left' (c := 4) hs).mul_right t)
    _ = _ := by ring

/-- **$D_4(b) D_4(c)$ modulo $16$.** Let
$a \colon \mathbb{Z}/4 \times \mathbb{Z}/4 \to \mathbb{Z}$ have sums $b_i$ and alternating sums
$c_i$, and let $D_4$ be the $4 \times 4$ circulant determinant. If
$b_0 + b_2 \not\equiv b_1 + b_3 \pmod 2$, then
$D_4(b) D_4(c) \equiv 1 - 4(b_0 b_2 + b_1 b_3 + c_0 c_2 + c_1 c_3) \pmod{16}$.

Source: Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for
C_4^2*, INTEGERS 24 (2024), Article A30, Lemma 10 (`integers-2024-A30-lem-10`). -/
public theorem c4Sq_circulantDetFour_product_mod_sixteen (a : Fin 4 × Fin 4 → ℤ)
    (h : ¬ c4SqB a 0 + c4SqB a 2 ≡ c4SqB a 1 + c4SqB a 3 [ZMOD 2]) :
    circulantDetFour (c4SqB a) * circulantDetFour (c4SqC a) ≡
      1 - 4 * (c4SqB a 0 * c4SqB a 2 + c4SqB a 1 * c4SqB a 3 +
        c4SqC a 0 * c4SqC a 2 + c4SqC a 1 * c4SqC a 3) [ZMOD 16] := by
  let b := c4SqB a
  let c := c4SqC a
  let x := b 0 * b 2 + b 1 * b 3
  let y := c 0 * c 2 + c 1 * c 3
  let s := (b 0 + b 2) % 2 - (b 1 + b 3) % 2
  have hbc (i : Fin 4) : b i ≡ c i [ZMOD 2] := by
    change c4SqB a i ≡ c4SqC a i [ZMOD 2]
    rw [Int.modEq_iff_dvd, c4SqB, c4SqC]
    exact ⟨-(a (i, 1) + a (i, 3)), by ring⟩
  have hp : (b 0 + b 2) % 2 = (c 0 + c 2) % 2 := (hbc 0).add (hbc 2)
  have hq : (b 1 + b 3) % 2 = (c 1 + c 3) % 2 := (hbc 1).add (hbc 3)
  have hs : s ^ 2 = 1 := by
    have hne : (b 0 + b 2) % 2 ≠ (b 1 + b 3) % 2 := h
    have hsign : s = 1 ∨ s = -1 := by
      dsimp only [s]
      omega
    rcases hsign with hsign | hsign <;> rw [hsign] <;> decide
  have hc := circulantDetFour_mod_sixteen_signed c
  dsimp only at hc
  rw [← hp, ← hq] at hc
  calc
    circulantDetFour b * circulantDetFour c ≡
        (s * (1 - 4 * x)) * (s * (1 - 4 * y)) [ZMOD 16] :=
      (circulantDetFour_mod_sixteen_signed b).mul hc
    _ = (1 - 4 * (x + y)) + (x * y) * 16 := by
      calc
        _ = s ^ 2 * ((1 - 4 * x) * (1 - 4 * y)) := by ring
        _ = _ := by rw [hs]; ring
    _ ≡ 1 - 4 * (x + y) [ZMOD 16] := Int.add_mul_modulus_modEq_iff.mpr Int.ModEq.rfl
    _ = _ := by simp only [x, y, b, c, add_assoc]

end MetaMathlibExt
