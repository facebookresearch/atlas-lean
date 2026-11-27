/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
public import MathlibExt.LinearAlgebra.Matrix.CirculantDetFour
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.Ring

/-!
# Powers of two in the four-by-four circulant determinant

After the determinant is factored, the four entry-parity patterns reduce to congruences for
sums and differences of squares.

## References

* Yuka Yamaguchi and Naoya Yamaguchi, *Integer Group Determinants for $C_4^2$*, INTEGERS 24
  (2024), Article A30, pp. 1–21, Lemma 7 and Remark 4.
* Yuka Yamaguchi and Naoya Yamaguchi, *Integer group determinants for $C_2^4$*,
  The Ramanujan Journal 62 (2023), pp. 983–995, Remark 3.5 (cited for the congruences in Remark 4).
-/

namespace MetaMathlibExt

private theorem odd_quotient_of_modEq {x c : ℤ} (h : x ≡ c [ZMOD 2 * c]) :
    ∃ t, x = c * (2 * t + 1) := by
  obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp h.symm
  exact ⟨t, by calc
    x = c + (x - c) := by ring
    _ = c * (2 * t + 1) := by rw [ht]; ring⟩

private theorem odd_sq_mod_eight {x : ℤ} (hx : x % 2 = 1) : x ^ 2 ≡ 1 [ZMOD 8] :=
  (Int.modEq_iff_dvd.mpr (Int.eight_dvd_sq_sub_one_of_odd (Int.odd_iff.mpr hx))).symm

private theorem even_sq_mod_eight {x : ℤ} (hx : x % 2 = 0) : x ^ 2 ≡ 2 * x [ZMOD 8] := by
  obtain ⟨a, rfl⟩ := Int.dvd_iff_emod_eq_zero.mpr hx
  have h : a ^ 2 ≡ a [ZMOD 2] := Int.sq_emod_two a
  calc
    (2 * a) ^ 2 = 4 * a ^ 2 := by ring
    _ ≡ 4 * a [ZMOD 8] := h.mul_left' (c := 4)
    _ = 2 * (2 * a) := by ring

private theorem even_sq_mod_four {x : ℤ} (hx : x % 2 = 0) : x ^ 2 ≡ 0 [ZMOD 4] :=
  (Int.sq_emod_four x).trans hx

private theorem sq_sum_mod_two (x y : ℤ) : x ^ 2 + y ^ 2 ≡ x + y [ZMOD 2] :=
  (show x ^ 2 ≡ x [ZMOD 2] from Int.sq_emod_two x).add (Int.sq_emod_two y)

private theorem sq_sub_mod_two (x y : ℤ) : x ^ 2 - y ^ 2 ≡ x - y [ZMOD 2] :=
  (show x ^ 2 ≡ x [ZMOD 2] from Int.sq_emod_two x).sub (Int.sq_emod_two y)

private theorem mul_odd_mod_double {x y c : ℤ} (hx : c ∣ x) (hy : y ≡ 1 [ZMOD 2]) :
    x * y ≡ x [ZMOD 2 * c] := by
  obtain ⟨a, rfl⟩ := hx
  simpa only [mul_one, mul_assoc, mul_comm 2 c] using (hy.mul_left a).mul_left' (c := c)

-- A signed residue of `1 - 2 * r` modulo 8 detects the residue of `r` modulo 4.
private theorem mod_four_of_signed_residue {w r : ℤ} (hr : r % 2 = 0)
    (hw : w ≡ 1 - 2 * r [ZMOD 8] ∨ -w ≡ 1 - 2 * r [ZMOD 8]) :
    ((w ≡ 3 [ZMOD 8] ∨ w ≡ -3 [ZMOD 8]) ↔ r ≡ 2 [ZMOD 4]) ∧
      ((w ≡ 1 [ZMOD 8] ∨ w ≡ -1 [ZMOD 8]) ↔ r ≡ 0 [ZMOD 4]) := by
  change ((w % 8 = 3 ∨ w % 8 = 5) ↔ r % 4 = 2) ∧
    ((w % 8 = 1 ∨ w % 8 = 7) ↔ r % 4 = 0)
  rcases hw with hw | hw
  · have hw' := hw.eq
    exact ⟨⟨by rintro (h | h) <;> omega, fun h ↦ Or.inr (by omega)⟩,
      ⟨by rintro (h | h) <;> omega, fun h ↦ Or.inl (by omega)⟩⟩
  · have hw' := hw.eq
    exact ⟨⟨by rintro (h | h) <;> omega, fun h ↦ Or.inl (by omega)⟩,
      ⟨by rintro (h | h) <;> omega, fun h ↦ Or.inr (by omega)⟩⟩

-- For odd `s` and `t`, the product condition detects opposite parities of the half-sums.
private theorem shifted_sq_sub_of_odd {s t : ℤ} (hs : s % 2 = 1) (ht : t % 2 = 1) :
    ∃ a b : ℤ, (s + 1) ^ 2 - (t + 1) ^ 2 = 4 * (a ^ 2 - b ^ 2) ∧
      ((s * t ≡ -1 [ZMOD 4]) ↔ a % 2 ≠ b % 2) := by
  let a := (s + 1) / 2
  let b := (t + 1) / 2
  have ha : s + 1 = 2 * a := by dsimp [a]; omega
  have hb : t + 1 = 2 * b := by dsimp [b]; omega
  have hp : s * t ≡ 1 - 2 * (a + b) [ZMOD 4] := by
    rw [Int.modEq_iff_dvd, show s = 2 * a - 1 by omega, show t = 2 * b - 1 by omega]
    exact ⟨-a * b, by ring⟩
  refine ⟨a, b, by rw [ha, hb]; ring, ?_⟩
  rw [show (s * t ≡ -1 [ZMOD 4]) ↔ 1 - 2 * (a + b) ≡ -1 [ZMOD 4] from
    ⟨fun h ↦ hp.symm.trans h, hp.trans⟩]
  change (1 - 2 * (a + b)) % 4 = 3 ↔ a % 2 ≠ b % 2
  omega

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
public theorem circulantDetFour_two_power_cases (k l m n : ℤ) :
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
        (w₄ ≡ 1 [ZMOD 8] ∨ w₄ ≡ -1 [ZMOD 8] → 2 ^ 5 ∣ D₄)) := by
  dsimp only
  let s := k + m
  let t := l + n
  let u := k - m
  let v := l - n
  let g := u ^ 2 + v ^ 2
  let f := s ^ 2 - (t + 1) ^ 2
  have hsu : s % 2 = u % 2 := by dsimp [s, u]; omega
  have htv : t % 2 = v % 2 := by dsimp [t, v]; omega
  have hk : k ≡ m [ZMOD 2] ↔ s % 2 = 0 := by simp only [Int.ModEq, s]; omega
  have hd₁ : circulantDetFour ![2 * k, 2 * l, 2 * m, 2 * n] = 16 * ((s ^ 2 - t ^ 2) * g) := by
    rw [circulantDetFour_eq]
    dsimp [s, t, u, v, g]
    ring
  have hd₂ : circulantDetFour ![2 * k + 1, 2 * l + 1, 2 * m + 1, 2 * n + 1] =
      16 * (((s + 1) ^ 2 - (t + 1) ^ 2) * g) := by
    rw [circulantDetFour_eq]
    dsimp [s, t, u, v, g]
    ring
  have hd₃ : circulantDetFour ![2 * k, 2 * l + 1, 2 * m, 2 * n + 1] = 16 * (f * g) := by
    rw [circulantDetFour_eq]
    dsimp [s, t, u, v, f, g]
    ring
  let p := s - t
  let q := s + t + 1
  let z := 2 * (u ^ 2 - u + v ^ 2 - v) + 1
  have hd₄ : circulantDetFour ![2 * k, 2 * l, 2 * m + 1, 2 * n + 1] = 8 * (p * q * z) := by
    rw [circulantDetFour_eq]
    dsimp [s, t, u, v, p, q, z]
    ring
  have hg := sq_sum_mod_two u v
  have hMixed (h : ¬ s ≡ t [ZMOD 2]) : g ≡ 1 [ZMOD 2] := by
    apply hg.trans
    simp only [Int.ModEq] at h ⊢
    omega
  have hgEven (hs : s % 2 = 0) (ht : t % 2 = 0) : 4 ∣ g :=
    Int.modEq_zero_iff_dvd.mp ((even_sq_mod_four (hsu ▸ hs)).add (even_sq_mod_four (htv ▸ ht)))
  have hgOdd (hs : s % 2 = 1) (ht : t % 2 = 1) : g ≡ 2 [ZMOD 8] :=
    (odd_sq_mod_eight (hsu ▸ hs)).add (odd_sq_mod_eight (htv ▸ ht))
  have hgDvd (h : s % 2 = t % 2) : 2 ∣ g :=
    Int.modEq_zero_iff_dvd.mp (hg.trans (by simp only [Int.ModEq]; omega))
  rw [hd₁, hd₂, hd₃, hd₄]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  -- All entries even.
  · intro h
    have hF : s ^ 2 - t ^ 2 ≡ 1 [ZMOD 2] := (sq_sub_mod_two s t).trans (by
      simp only [Int.ModEq] at h ⊢
      omega)
    exact odd_quotient_of_modEq ((hF.mul (hMixed h)).mul_left' (c := 16))
  · intro h
    have hst : s % 2 = t % 2 := h
    by_cases hs : s % 2 = 0
    · have ht := hst ▸ hs
      have hF : 4 ∣ s ^ 2 - t ^ 2 := Int.modEq_zero_iff_dvd.mp
        ((even_sq_mod_four hs).sub (even_sq_mod_four ht))
      exact mul_dvd_mul_left 16 (mul_dvd_mul hF (hgEven hs ht))
    · have hs₁ : s % 2 = 1 := by omega
      have ht₁ := hst ▸ hs₁
      have hF : 8 ∣ s ^ 2 - t ^ 2 := Int.modEq_zero_iff_dvd.mp
        ((odd_sq_mod_eight hs₁).sub (odd_sq_mod_eight ht₁))
      exact mul_dvd_mul_left 16 (mul_dvd_mul hF (hgDvd hst))
  -- All entries odd. When `s` and `t` are odd, halve the shifted sums.
  · intro h
    have hF : (s + 1) ^ 2 - (t + 1) ^ 2 ≡ 1 [ZMOD 2] :=
      (sq_sub_mod_two (s + 1) (t + 1)).trans (by simp only [Int.ModEq] at h ⊢; omega)
    exact odd_quotient_of_modEq ((hF.mul (hMixed h)).mul_left' (c := 16))
  · intro h
    have hst : s * t ≡ 1 [ZMOD 2] :=
      (h.of_dvd (by decide : (2 : ℤ) ∣ 4) : s * t ≡ -1 [ZMOD 2])
    obtain ⟨hs, ht⟩ := Int.odd_mul.mp (Int.odd_iff.mpr hst)
    obtain ⟨a, b, hDiff, hParity⟩ := shifted_sq_sub_of_odd (Int.odd_iff.mp hs) (Int.odd_iff.mp ht)
    have hF : a ^ 2 - b ^ 2 ≡ 1 [ZMOD 2] := (sq_sub_mod_two a b).trans (by
      have hab := hParity.mp h
      simp only [Int.ModEq]
      omega)
    have hG := (hgOdd (Int.odd_iff.mp hs) (Int.odd_iff.mp ht)).of_dvd (by decide : 4 ∣ (8 : ℤ))
    obtain ⟨j, hj⟩ := odd_quotient_of_modEq (c := 2) hG
    have hJ : (2 * j + 1) ≡ 1 [ZMOD 2] := by simp only [Int.ModEq]; omega
    rw [hDiff, hj, show 16 * (4 * (a ^ 2 - b ^ 2) * (2 * (2 * j + 1))) =
      128 * ((a ^ 2 - b ^ 2) * (2 * j + 1)) by ring]
    exact odd_quotient_of_modEq ((hF.mul hJ).mul_left' (c := 128))
  · intro h hne
    have hst : s % 2 = t % 2 := h
    by_cases hs : s % 2 = 0
    · have ht := hst ▸ hs
      have hF : 8 ∣ (s + 1) ^ 2 - (t + 1) ^ 2 := Int.modEq_zero_iff_dvd.mp
        ((odd_sq_mod_eight (by omega : (s + 1) % 2 = 1)).sub (odd_sq_mod_eight (by omega)))
      exact mul_dvd_mul_left 16 (mul_dvd_mul hF (hgEven hs ht))
    · have hs₁ : s % 2 = 1 := by omega
      have ht₁ := hst ▸ hs₁
      obtain ⟨a, b, hDiff, hParity⟩ := shifted_sq_sub_of_odd hs₁ ht₁
      have hab : a % 2 = b % 2 := not_ne_iff.mp (fun h ↦ hne (hParity.mpr h))
      have hSq : a ^ 2 ≡ b ^ 2 [ZMOD 4] :=
        (Int.sq_emod_four a).trans (hab.trans (Int.sq_emod_four b).symm)
      rw [hDiff]
      exact mul_dvd_mul_left 16 (mul_dvd_mul (mul_dvd_mul_left 4 hSq.symm.dvd) (hgDvd hst))
  -- Alternate odd entries. With `s` even, one factor is odd and the other a multiple of four.
  · let w := (2 * k + 2 * l + 1) * (2 * m + 2 * n + 1)
    have hw : w = q ^ 2 - (u + v) ^ 2 := by dsimp [w, q, s, t, u, v]; ring
    have hEven (hs : s % 2 = 0) : ∃ r : ℤ, r % 2 = 0 ∧
        (w ≡ 1 - 2 * r [ZMOD 8] ∨ -w ≡ 1 - 2 * r [ZMOD 8]) ∧ f * g ≡ 2 * r [ZMOD 8] := by
      have hu : u % 2 = 0 := hsu ▸ hs
      by_cases ht : t % 2 = 0
      · have hv : v % 2 = 0 := htv ▸ ht
        have huv : (u + v) % 2 = 0 := by omega
        have hq : q % 2 = 1 := by dsimp [q]; omega
        have hF : f ≡ 1 [ZMOD 2] := (sq_sub_mod_two s (t + 1)).trans (by
          simp only [Int.ModEq]
          omega)
        refine ⟨u + v, huv, Or.inl ?_, ?_⟩
        · rw [hw]
          exact (odd_sq_mod_eight hq).sub (even_sq_mod_eight huv)
        · rw [mul_comm f]
          refine (mul_odd_mod_double (hgEven hs ht) hF).trans ?_
          change u ^ 2 + v ^ 2 ≡ 2 * (u + v) [ZMOD 8]
          rw [mul_add]
          exact (even_sq_mod_eight hu).add (even_sq_mod_eight hv)
      · have hq : q % 2 = 0 := by dsimp [q]; omega
        have huv : (u + v) % 2 = 1 := by omega
        have ht' : (t + 1) % 2 = 0 := by omega
        have hF : f ≡ 2 * q [ZMOD 8] :=
          ((even_sq_mod_eight hs).sub (even_sq_mod_eight ht')).trans (by
            simp only [Int.ModEq, q]
            omega)
        have hFd : 4 ∣ f := Int.modEq_zero_iff_dvd.mp
          ((even_sq_mod_four hs).sub (even_sq_mod_four ht'))
        have hG : g ≡ 1 [ZMOD 2] := hg.trans (by simp only [Int.ModEq]; omega)
        refine ⟨q, hq, Or.inr ?_, (mul_odd_mod_double hFd hG).trans hF⟩
        rw [hw, neg_sub]
        exact (odd_sq_mod_eight huv).sub (even_sq_mod_eight hq)
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨hu, hv⟩
      have hu₁ : u % 2 = 1 := hu
      have hv₁ : v % 2 = 1 := hv
      have hs : s % 2 = 1 := hsu.symm ▸ hu₁
      have ht : t % 2 = 1 := htv.symm ▸ hv₁
      have hF : f ≡ 1 [ZMOD 2] := (sq_sub_mod_two s (t + 1)).trans (by
        simp only [Int.ModEq]
        omega)
      have hG := (hgOdd hs ht).of_dvd (by decide : 4 ∣ (8 : ℤ))
      have hR : f * g ≡ 2 [ZMOD 4] := by
        rw [mul_comm f]
        exact (mul_odd_mod_double (hgDvd (hs.trans ht.symm)) hF).trans hG
      exact odd_quotient_of_modEq (hR.mul_left' (c := 16))
    · rintro ⟨hkm, hW⟩
      obtain ⟨r, hr₀, hw', hR⟩ := hEven (hk.mp hkm)
      have hr := (mod_four_of_signed_residue hr₀ hw').1.mp hW
      exact odd_quotient_of_modEq ((hR.trans (hr.mul_left' (c := 2))).mul_left' (c := 16))
    · intro hNotOdd hNotW
      change 16 * 8 ∣ 16 * (f * g)
      apply mul_dvd_mul_left 16
      apply Int.modEq_zero_iff_dvd.mp
      by_cases hs : s % 2 = 0
      · obtain ⟨r, hr, hw', hR⟩ := hEven hs
        have hr₂ : ¬ r ≡ 2 [ZMOD 4] := fun h₂ ↦
          hNotW ⟨hk.mpr hs, (mod_four_of_signed_residue hr hw').1.mpr h₂⟩
        have hr₀ : r ≡ 0 [ZMOD 4] := by simp only [Int.ModEq] at hr₂ ⊢; omega
        exact hR.trans (hr₀.mul_left' (c := 2))
      · have hu : u % 2 = 1 := by omega
        have hv : ¬ v ≡ 1 [ZMOD 2] := fun h ↦ hNotOdd ⟨hu, h⟩
        have hF : f ≡ 0 [ZMOD 8] := (odd_sq_mod_eight (by omega : s % 2 = 1)).sub
          (odd_sq_mod_eight (by simp only [Int.ModEq] at hv; omega))
        simpa only [zero_mul] using hF.mul_right g
  -- Adjacent odd entries. Exactly one of the two linear factors `p` and `q` is even.
  · let w := (2 * k + 2 * m + 1) * (2 * l + 2 * n + 1)
    have hw : w = q ^ 2 - p ^ 2 := by dsimp [w, p, q, s, t]; ring
    have hz : z ≡ 1 [ZMOD 2] := by simp only [Int.ModEq, z]; omega
    have hParity : (p + q) % 2 = 1 := by dsimp [p, q]; omega
    have hR : ∃ r : ℤ, r % 2 = 0 ∧
        (w ≡ 1 - 2 * r [ZMOD 8] ∨ -w ≡ 1 - 2 * r [ZMOD 8]) ∧ p * q * z ≡ r [ZMOD 4] := by
      by_cases hp : p % 2 = 0
      · have hq : q % 2 = 1 := by omega
        have hqz : q * z ≡ 1 [ZMOD 2] := (show q ≡ 1 [ZMOD 2] from hq).mul hz
        refine ⟨p, hp, Or.inl ?_, ?_⟩
        · rw [hw]
          exact (odd_sq_mod_eight hq).sub (even_sq_mod_eight hp)
        · rw [mul_assoc]
          exact mul_odd_mod_double (Int.dvd_iff_emod_eq_zero.mpr hp) hqz
      · have hp₁ : p % 2 = 1 := by omega
        have hq : q % 2 = 0 := by omega
        have hpz : p * z ≡ 1 [ZMOD 2] := (show p ≡ 1 [ZMOD 2] from hp₁).mul hz
        refine ⟨q, hq, Or.inr ?_, ?_⟩
        · rw [hw, neg_sub]
          exact (odd_sq_mod_eight hp₁).sub (even_sq_mod_eight hq)
        · rw [mul_comm p q, mul_assoc]
          exact mul_odd_mod_double (Int.dvd_iff_emod_eq_zero.mpr hq) hpz
    obtain ⟨r, hr, hw', hR⟩ := hR
    have hCases := mod_four_of_signed_residue hr hw'
    refine ⟨?_, ?_⟩
    · intro h
      exact odd_quotient_of_modEq ((hR.trans (hCases.1.mp h)).mul_left' (c := 8))
    · intro h
      exact mul_dvd_mul_left 8 (Int.modEq_zero_iff_dvd.mp (hR.trans (hCases.2.mp h)))

end MetaMathlibExt
