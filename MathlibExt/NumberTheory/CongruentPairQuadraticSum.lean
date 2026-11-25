/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A quadratic sum over congruent pairs modulo a prime

We prove the evaluation in Brahim Mittou, *Explicit Evaluation of a Quadratic Sum Over
Congruent Pairs Modulo a Prime*, INTEGERS 25 (2025), Article A85.

For a prime `p` and a positive integer `l` coprime to `p`,
`F(p, l) = ∑_{1 ≤ a, b ≤ p-1, b ≡ a l (mod p)} (a/p - 1/2)(b/p - 1/2)`, and
`s(p, l) = (1/(4l)) ∑_{a=1}^{l-1} cot(πa/l) cot(πap/l)` is the Dedekind sum.

Summing the quadratic polynomial `x² - x` over a rectangular grid gives Dedekind reciprocity.
The discrete Fourier transform of the centered residues gives the cotangent expression.
-/

namespace MetaMathlibExt

namespace congruentPairQuadraticSum_eq_sub_dedekindSum

open Finset

private noncomputable def grid (n i : ℕ) : ℝ := i / (n : ℝ)

-- Include the zero residue for the moment calculations. Its contribution is 1/4.
private noncomputable def rawSum (n m : ℕ) : ℝ :=
  ∑ a ∈ range n, (grid n a - 1 / 2) * (grid n (a * m % n) - 1 / 2)

private lemma grid_moments {n : ℕ} (hn : 0 < n) :
    (∑ i ∈ range n, grid n i) = (n - 1 : ℝ) / 2 ∧
    (∑ i ∈ range n, (grid n i) ^ 2) = (n - 1 : ℝ) * (2 * n - 1) / (6 * n) := by
  have first (k : ℕ) : (∑ i ∈ range k, (i : ℝ)) = k * (k - 1) / 2 := by
    induction k with
    | zero => simp
    | succ k ih => rw [sum_range_succ, ih, Nat.cast_succ]; ring
  have second (k : ℕ) : (∑ i ∈ range k, (i : ℝ) ^ 2) =
      k * (k - 1) * (2 * k - 1) / 6 := by
    induction k with
    | zero => simp
    | succ k ih => rw [sum_range_succ, ih, Nat.cast_succ]; ring
  simp only [grid, div_pow, ← sum_div, first, second]
  constructor <;> field_simp

-- The grid (a/n, b/m) visits each residue of a*m + b*n modulo n*m exactly once.
private lemma grid_residues {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (h : n.Coprime m)
    (f : ℕ → ℝ) :
    (∑ a ∈ range n, ∑ b ∈ range m, f ((a * m + b * n) % (n * m))) =
      ∑ i ∈ range (n * m), f i := by
  let e (x : Fin n × Fin m) : Fin (n * m) :=
    ⟨(x.1.val * m + x.2.val * n) % (n * m), Nat.mod_lt _ (Nat.mul_pos hn hm)⟩
  have inj : Function.Injective e := by
    intro ⟨a, b⟩ ⟨c, d⟩ he
    have he' : a.val * m + b.val * n ≡ c.val * m + d.val * n [MOD n * m] :=
      congrArg Fin.val he
    apply Prod.ext <;> apply Fin.ext
    · apply Nat.ModEq.eq_of_lt_of_lt _ a.isLt c.isLt
      apply Nat.ModEq.cancel_right_of_coprime h
      simpa only [Nat.add_mul_modulus_modEq_iff, Nat.modEq_add_mul_modulus_iff] using
        he'.of_dvd (dvd_mul_right n m)
    · apply Nat.ModEq.eq_of_lt_of_lt _ b.isLt d.isLt
      apply Nat.ModEq.cancel_right_of_coprime h.symm
      simpa only [Nat.mul_modulus_add_modEq_iff, Nat.modEq_mul_modulus_add_iff] using
        he'.of_dvd (dvd_mul_left m n)
  have bij := (Fintype.bijective_iff_injective_and_card e).2 ⟨inj, by simp⟩
  have hs := Fintype.sum_bijective e bij (fun x ↦ f (e x).val) (fun i ↦ f i.val) (fun _ ↦ rfl)
  simp only [← Fin.sum_univ_eq_sum_range]
  simpa only [Fintype.sum_prod_type, e] using hs

private noncomputable def carry (n m a b : ℕ) : ℝ :=
  if n * m ≤ a * m + b * n then 1 else 0

private lemma carry_swap (n m a b : ℕ) : carry n m a b = carry m n b a := by
  simp only [carry, mul_comm n m, add_comm (a * m)]

private lemma sum_carry {n m a : ℕ} (hn : 0 < n) (ha : a < n) :
    (∑ b ∈ range m, carry n m a b) = ↑(a * m / n) := by
  have hle : a * m / n ≤ m := by
    apply Nat.div_le_of_le_mul
    exact Nat.mul_le_mul_right m ha.le
  simp only [carry, sum_boole]
  have hs : (range m).filter (fun b ↦ n * m ≤ a * m + b * n) = Ico (m - a * m / n) m := by
    ext b
    simp only [mem_filter, mem_range, mem_Ico]
    by_cases hb : b < m
    · have he : n * m ≤ a * m + b * n ↔ m - b ≤ a * m / n := by
        rw [Nat.le_div_iff_mul_le hn, Nat.sub_mul, Nat.sub_le_iff_le_add]
        rw [Nat.mul_comm m n]
      omega
    · omega
  rw [hs, Nat.card_Ico, Nat.sub_sub_self hle]

private noncomputable def quad (x : ℝ) : ℝ := x ^ 2 - x

private lemma grid_quad {n m a b : ℕ} (hn : 0 < n) (hm : 0 < m) (ha : a < n) (hb : b < m) :
    quad (grid (n * m) ((a * m + b * n) % (n * m))) =
      quad (grid n a + grid m b) -
        2 * ((grid n a - 1 / 2) * carry n m a b + (grid m b - 1 / 2) * carry m n b a) := by
  rw [← carry_swap n m a b]
  have hlt : a * m + b * n < n * m + n * m := by
    have h₁ := Nat.mul_lt_mul_of_pos_right ha hm
    have h₂ := Nat.mul_lt_mul_of_pos_right hb hn
    rw [Nat.mul_comm m n] at h₂
    omega
  unfold quad grid carry
  split_ifs with h
  · have hmod : (a * m + b * n) % (n * m) = a * m + b * n - n * m := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    rw [hmod, Nat.cast_sub h]
    push_cast
    field_simp
    ring
  · rw [Nat.mod_eq_of_lt (by omega)]
    push_cast
    field_simp
    ring

private lemma sum_grid_quad {n : ℕ} (hn : 0 < n) :
    (∑ a ∈ range n, quad (grid n a)) = (1 - (n : ℝ) ^ 2) / (6 * n) := by
  simp only [quad, sum_sub_distrib, (grid_moments hn).1, (grid_moments hn).2]
  field_simp
  ring

private lemma sum_grid_quad_add {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    (∑ a ∈ range n, ∑ b ∈ range m, quad (grid n a + grid m b)) =
      m * ((1 - (n : ℝ) ^ 2) / (6 * n)) + n * ((1 - (m : ℝ) ^ 2) / (6 * m)) +
      2 * ((n - 1 : ℝ) / 2) * ((m - 1 : ℝ) / 2) := by
  have add (x y : ℝ) : quad (x + y) = quad x + quad y + x * (2 * y) := by unfold quad; ring
  simp only [add, sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_sum,
    ← sum_mul, sum_grid_quad hn, sum_grid_quad hm, (grid_moments hn).1, (grid_moments hm).1]
  ring

-- Sum the carries in a row. Removing its integer part changes m*a/n into its residue.
private lemma weighted_carries {n m : ℕ} (hn : 0 < n) :
    (∑ a ∈ range n, ∑ b ∈ range m, (grid n a - 1 / 2) * carry n m a b) =
      m * ((n - 1 : ℝ) * (2 * n - 1) / (6 * n)) -
        ((m + 1 : ℝ) / 2) * ((n - 1 : ℝ) / 2) + n / 4 - rawSum n m := by
  have row (a : ℕ) (ha : a ∈ range n) :
      (∑ b ∈ range m, (grid n a - 1 / 2) * carry n m a b) =
        (m * (grid n a) ^ 2 - ((m + 1 : ℝ) / 2) * grid n a + 1 / 4) -
        (grid n a - 1 / 2) * (grid n (a * m % n) - 1 / 2) := by
    rw [← mul_sum, sum_carry hn (mem_range.mp ha)]
    have hdiv : grid n (a * m % n) = m * grid n a - ↑(a * m / n) := by
      have he := congrArg (Nat.cast : ℕ → ℝ) (Nat.mod_add_div (a * m) n)
      push_cast at he
      unfold grid
      field_simp
      linarith
    rw [hdiv]
    ring
  rw [sum_congr rfl row]
  simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum, (grid_moments hn).1,
    (grid_moments hn).2, sum_const, card_range, nsmul_eq_mul, rawSum]
  ring

private lemma reciprocity {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (h : n.Coprime m) :
    rawSum n m + rawSum m n =
      ((n : ℝ) ^ 2 - 3 * m * n + m ^ 2 + 1) / (12 * m * n) + 1 / 2 := by
  have hs := grid_residues hn hm h (fun i ↦ quad (grid (n * m) i))
  have hr : (∑ a ∈ range n, ∑ b ∈ range m, quad (grid (n * m) ((a * m + b * n) % (n * m)))) =
      ∑ a ∈ range n, ∑ b ∈ range m, (quad (grid n a + grid m b) -
        2 * ((grid n a - 1 / 2) * carry n m a b + (grid m b - 1 / 2) * carry m n b a)) := by
    exact sum_congr rfl fun a ha ↦ sum_congr rfl fun b hb ↦
      grid_quad hn hm (mem_range.mp ha) (mem_range.mp hb)
  rw [hr] at hs
  simp only [sum_sub_distrib, ← mul_sum (a := (2 : ℝ)), sum_add_distrib] at hs
  rw [sum_grid_quad_add hn hm, sum_grid_quad (Nat.mul_pos hn hm), weighted_carries hn,
    sum_comm (s := range n) (t := range m) (f := fun _ b ↦ (grid m b - 1 / 2) * _),
    weighted_carries hm] at hs
  push_cast at hs
  field_simp at hs ⊢
  linarith

private lemma sum_zmod {A : Type*} [AddCommMonoid A] {n : ℕ} [NeZero n] (f : ZMod n → A) :
    ∑ j, f j = ∑ a ∈ range n, f (a : ZMod n) := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    rw [← Fin.sum_univ_eq_sum_range]
    exact sum_congr rfl fun j _ ↦ congrArg f (Fin.cast_val_eq_self j).symm

private noncomputable def saw (n a : ℕ) : ℝ :=
  if a = 0 then 0 else grid n a - 1 / 2

private noncomputable def wave {n : ℕ} [NeZero n] (j : ZMod n) : ℂ := saw n j.val

-- Each nontrivial root of unity gives a weighted geometric sum by telescoping.
private lemma geom_weight {n : ℕ} {z : ℂ} (hz : z ^ n = 1) (h : z ≠ 1) :
    (∑ a ∈ range n, (a : ℂ) * z ^ a) * (z - 1) = n := by
  have ht := sum_range_sub (fun a ↦ (a : ℂ) * z ^ a) n
  simp only [Nat.cast_zero, zero_mul, sub_zero, hz, mul_one] at ht
  have step (a : ℕ) : ((a + 1 : ℕ) : ℂ) * z ^ (a + 1) - a * z ^ a =
      (a * z ^ a) * (z - 1) + z * z ^ a := by push_cast; rw [pow_succ]; ring
  simp only [step, sum_add_distrib, ← sum_mul, ← mul_sum, geom_sum_eq h, hz,
    sub_self, zero_div, mul_zero, add_zero] at ht
  exact ht

private lemma wave_transform {n : ℕ} [NeZero n] (k : ℤ) :
    ZMod.dft (wave (n := n)) (-(k : ZMod n)) =
      -(Complex.I / 2) * (Real.cot (Real.pi * k / n) : ℂ) := by
  let z := ZMod.stdAddChar (k : ZMod n)
  have hn := NeZero.pos n
  have hpow (a : ℕ) : ZMod.stdAddChar ((a : ZMod n) * (k : ZMod n)) = z ^ a := by
    rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]
  have hz : z ^ n = 1 := by simpa using (hpow n).symm
  have hterm (a : ℕ) (ha : a ∈ range n) :
      ZMod.stdAddChar (-((a : ZMod n) * -(k : ZMod n))) • wave (a : ZMod n) =
        (if a = 0 then 1 / 2 else 0) +
          (a * z ^ a / n - z ^ a / 2) := by
    simp only [mul_neg, neg_neg, hpow, smul_eq_mul, wave,
      ZMod.val_natCast_of_lt (mem_range.mp ha), saw, grid]
    split_ifs with h
    · subst a
      norm_num
    · push_cast
      ring
  have he : Complex.exp (2 * Complex.I * ((Real.pi : ℂ) * k / n)) = z := by
    rw [show z = Complex.exp (2 * Real.pi * Complex.I * k / n) from ZMod.stdAddChar_coe k]
    congr 1
    ring
  rw [ZMod.dft_apply, sum_zmod, sum_congr rfl hterm, Complex.ofReal_cot]
  push_cast
  rw [Complex.cot_eq_exp_ratio, he]
  simp only [sum_add_distrib, sum_ite_eq', mem_range.mpr hn, ite_true, sum_sub_distrib, ← sum_div]
  by_cases h : z = 1
  · have first := congrArg (Complex.ofReal) (grid_moments hn).1
    simp only [grid, ← sum_div] at first
    push_cast at first
    simp [h, first]
    ring
  · rw [geom_sum_eq h, hz, sub_self, zero_div, zero_div, sub_zero]
    have hw := geom_weight hz h
    have h₁ : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    rw [(eq_div_iff (sub_ne_zero.mpr h)).2 hw]
    field_simp [NeZero.ne (n : ℂ), Complex.I_ne_zero, sub_ne_zero.mpr h]
    ring

private lemma range_split_zero {A : Type*} [AddCommMonoid A] {n : ℕ} (hn : 0 < n) (f : ℕ → A) :
    ∑ a ∈ range n, f a = f 0 + ∑ a ∈ Icc 1 (n - 1), f a := by
  have hi : Ico 1 n = Icc 1 (n - 1) := by ext a; simp; omega
  simpa only [hi, sum_range_one] using (sum_range_add_sum_Ico f hn).symm

private lemma residue_mem {n m a : ℕ} (hn : 0 < n) (h : n.Coprime m)
    (ha : a ∈ Icc 1 (n - 1)) : a * m % n ∈ Icc 1 (n - 1) := by
  obtain ⟨ha₀, ha₁⟩ := mem_Icc.mp ha
  have hne : a * m % n ≠ 0 := by
    intro hz
    have he : a * m ≡ 0 * m [MOD n] := by simpa [Nat.ModEq] using hz
    have := (he.cancel_right_of_coprime h).eq_of_lt_of_lt (by omega) hn
    omega
  have := Nat.mod_lt (a * m) hn
  exact mem_Icc.mpr ⟨by omega, by omega⟩

private lemma pair_sum {n m : ℕ} (hn : 0 < n) (h : n.Coprime m) :
    (∑ a ∈ Icc 1 (n - 1), ∑ b ∈ (Icc 1 (n - 1)).filter (fun b ↦ b ≡ a * m [MOD n]),
      (grid n a - 1 / 2) * (grid n b - 1 / 2)) = rawSum n m - 1 / 4 := by
  rw [rawSum, range_split_zero hn, add_sub_right_comm]
  rw [show (grid n 0 - 1 / 2) * (grid n (0 * m % n) - 1 / 2) - 1 / 4 = 0 by
    norm_num [grid], zero_add]
  refine sum_congr rfl fun a ha ↦ ?_
  have hf : (Icc 1 (n - 1)).filter (fun b ↦ b ≡ a * m [MOD n]) = {a * m % n} := by
    ext b
    rw [mem_filter, mem_singleton]
    constructor
    · intro ⟨hb, he⟩
      have := (mem_Icc.mp hb).2
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt (show b < n by omega)] using he
    · rintro rfl
      exact ⟨residue_mem hn h ha, Nat.mod_modEq _ _⟩
  rw [hf, sum_singleton]

-- Fourier inversion in one factor of the correlation.
private lemma fourier_correlation {n : ℕ} [NeZero n] (m : ZMod n) :
    ∑ k : ZMod n, ZMod.dft wave k * ZMod.dft wave (-(k * m)) =
      (n : ℂ) * ∑ j : ZMod n, wave j * wave (j * m) := by
  calc
    _ = ∑ k : ZMod n, ∑ j : ZMod n,
          wave j * (ZMod.stdAddChar (k * (j * m)) * ZMod.dft wave k) := by
      apply sum_congr rfl
      intro k _
      rw [ZMod.dft_apply wave (-(k * m)), mul_sum]
      apply sum_congr rfl
      intro j _
      rw [smul_eq_mul, show -(j * -(k * m)) = k * (j * m) by ring]
      ring
    _ = ∑ j : ZMod n, wave j * ZMod.dft (ZMod.dft wave) (-(j * m)) := by
      rw [sum_comm]
      simp only [ZMod.dft_apply (ZMod.dft wave), smul_eq_mul, mul_sum, mul_neg, neg_neg]
    _ = _ := by
      simp only [ZMod.dft_dft, neg_neg, smul_eq_mul, mul_sum]
      apply sum_congr rfl
      intro j _
      ring

private lemma cotangent_sum {n m : ℕ} (hn : 0 < n) (h : n.Coprime m) :
    rawSum n m - 1 / 4 = 1 / (4 * n) * ∑ a ∈ Icc 1 (n - 1),
      Real.cot (Real.pi * a / n) * Real.cot (Real.pi * a * m / n) := by
  have : NeZero n := ⟨hn.ne'⟩
  have ht (a : ℕ) :
      ZMod.dft (wave (n := n)) a * ZMod.dft wave (-((a : ZMod n) * (m : ZMod n))) =
        ((Real.cot (Real.pi * a / n) * Real.cot (Real.pi * a * m / n) : ℝ) : ℂ) / 4 := by
    have h₁ := wave_transform (n := n) (-(a : ℤ))
    have h₂ := wave_transform (n := n) ((a : ℤ) * m)
    push_cast at h₁ h₂
    simp only [neg_neg, mul_neg, neg_div] at h₁
    rw [h₁, h₂, ← mul_assoc (Real.pi : ℂ)]
    push_cast
    rw [show ∀ z : ℂ, Complex.cot (-z) = -Complex.cot z by simp [Complex.cot, div_neg]]
    linear_combination -(Complex.cot ((Real.pi : ℂ) * a / n) *
      Complex.cot ((Real.pi : ℂ) * a * m / n) / 4) * Complex.I_sq
  have hc := fourier_correlation (n := n) (m : ZMod n)
  rw [sum_zmod, sum_zmod (f := fun j ↦ wave j * wave (j * (m : ZMod n)))] at hc
  simp only [ht, ← sum_div] at hc
  rw [range_split_zero hn, range_split_zero hn
    (fun a ↦ wave (a : ZMod n) * wave ((a : ZMod n) * (m : ZMod n)))] at hc
  have hw (a : ℕ) (ha : a ∈ Icc 1 (n - 1)) :
      wave (a : ZMod n) * wave ((a : ZMod n) * (m : ZMod n)) =
        (((grid n a - 1 / 2) * (grid n (a * m % n) - 1 / 2) : ℝ) : ℂ) := by
    have ha' := mem_Icc.mp ha
    have hb := (mem_Icc.mp (residue_mem hn h ha)).1
    simp only [wave, ← Nat.cast_mul, ZMod.val_natCast, Nat.mod_eq_of_lt (show a < n by omega),
      saw, ite_eq_right (show a ≠ 0 by omega), ite_eq_right (show a * m % n ≠ 0 by omega),
      Complex.ofReal_mul]
  rw [sum_congr rfl hw] at hc
  have hzero : wave (0 : ZMod n) = 0 := by simp [wave, saw]
  have hcot : Real.cot 0 = 0 := by simp [Real.cot_eq_cos_div_sin]
  simp only [Nat.cast_zero, mul_zero, zero_div, hcot, zero_mul, Complex.ofReal_zero,
    hzero, zero_add] at hc
  have hr : (∑ a ∈ Icc 1 (n - 1), Real.cot (Real.pi * a / n) *
      Real.cot (Real.pi * a * m / n)) / 4 =
      n * ∑ a ∈ Icc 1 (n - 1), (grid n a - 1 / 2) * (grid n (a * m % n) - 1 / 2) := by
    exact_mod_cast hc
  rw [rawSum, range_split_zero hn, one_div (4 * (n : ℝ)), inv_mul_eq_div,
    eq_div_iff (by positivity)]
  simp only [zero_mul, Nat.zero_mod, show grid n 0 = 0 by simp [grid]]
  linarith only [hr]

end congruentPairQuadraticSum_eq_sub_dedekindSum

open congruentPairQuadraticSum_eq_sub_dedekindSum in
/-- **Mittou's evaluation of a quadratic sum over congruent pairs.** Let $p$ be a prime and $l$ a
positive integer with $\gcd(p, l) = 1$. Let $F(p, l)$ be the sum of
$\left(\frac{a}{p} - \frac{1}{2}\right)\left(\frac{b}{p} - \frac{1}{2}\right)$ over all pairs of
integers $a, b$ with $1 \le a, b \le p - 1$ and $b \equiv a l \pmod{p}$, and let
$$s(p, l) = \frac{1}{4l} \sum_{a=1}^{l-1} \cot\left(\frac{\pi a}{l}\right)
\cot\left(\frac{\pi a p}{l}\right)$$
be the Dedekind sum. Then
$$F(p, l) = \frac{p^2 - 3lp + l^2 + 1}{12 l p} - s(p, l).$$

Domain extension: the paper assumes $p \ge 3$; the identity also holds for $p = 2$ (then $l$ is
odd and both sides vanish), so that hypothesis is dropped. The paper's remark that $s(p, l)$
depends only on $p \bmod l$ is not restated.

Source: Brahim Mittou, *Explicit Evaluation of a Quadratic Sum Over Congruent Pairs Modulo a
Prime*, INTEGERS 25 (2025), Article A85, Theorem 1 (`integers-2025-A85-thm-1`). -/
public theorem congruentPairQuadraticSum_eq_sub_dedekindSum {p l : ℕ} (hp : p.Prime)
    (hl : 0 < l) (hpl : p.Coprime l) :
    (∑ a ∈ Finset.Icc 1 (p - 1),
        ∑ b ∈ (Finset.Icc 1 (p - 1)).filter (fun b => b ≡ a * l [MOD p]),
          ((a : ℝ) / p - 1 / 2) * ((b : ℝ) / p - 1 / 2)) =
      ((p : ℝ) ^ 2 - 3 * l * p + l ^ 2 + 1) / (12 * l * p) -
        1 / (4 * l) * ∑ a ∈ Finset.Icc 1 (l - 1),
          Real.cot (Real.pi * a / l) * Real.cot (Real.pi * a * p / l) := by
  have hs := pair_sum hp.pos hpl
  unfold grid at hs
  rw [hs, ← cotangent_sum hl hpl.symm]
  linarith [reciprocity hp.pos hl hpl]

end MetaMathlibExt
