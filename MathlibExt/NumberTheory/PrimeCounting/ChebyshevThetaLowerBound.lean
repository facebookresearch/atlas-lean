/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

open Real

/-- Building block: `x ^ (1/2) + x ^ (1/3) + x ^ (1/5)`. -/
private noncomputable def MetaChebyPf (x : ℝ) : ℝ :=
  x ^ (2:ℝ)⁻¹ + x ^ (3:ℝ)⁻¹ + x ^ (5:ℝ)⁻¹

/-- Building block: `½ x ^ (1/4) + ⅓ x ^ (1/6) + ⅕ x ^ (1/10)`. -/
private noncomputable def MetaChebyMf (x : ℝ) : ℝ :=
  (2:ℝ)⁻¹ * x ^ ((4:ℝ)⁻¹) + (3:ℝ)⁻¹ * x ^ ((6:ℝ)⁻¹) + (5:ℝ)⁻¹ * x ^ ((10:ℝ)⁻¹)

/-- Explicit lower bound for `Chebyshev.theta`, obtained from the Costa–Pereira
inequality together with `psi_ge'` and `psi_le`. -/
private noncomputable def MetaChebyLB (x : ℝ) : ℝ :=
  (x - 1) * Real.log 2 - Real.log (x + 2) - Real.log 4 * MetaChebyPf x
    - 2 * Real.log x * MetaChebyMf x

private noncomputable def MetaChebydPf (x : ℝ) : ℝ :=
  (2:ℝ)⁻¹ * x ^ ((2:ℝ)⁻¹ - 1) + (3:ℝ)⁻¹ * x ^ ((3:ℝ)⁻¹ - 1) + (5:ℝ)⁻¹ * x ^ ((5:ℝ)⁻¹ - 1)

private noncomputable def MetaChebydMf (x : ℝ) : ℝ :=
  (2:ℝ)⁻¹ * ((4:ℝ)⁻¹ * x ^ ((4:ℝ)⁻¹ - 1))
    + (3:ℝ)⁻¹ * ((6:ℝ)⁻¹ * x ^ ((6:ℝ)⁻¹ - 1))
    + (5:ℝ)⁻¹ * ((10:ℝ)⁻¹ * x ^ ((10:ℝ)⁻¹ - 1))

private noncomputable def MetaChebydLB (x : ℝ) : ℝ :=
  Real.log 2 - (x + 2)⁻¹ - Real.log 4 * MetaChebydPf x
    - 2 * (x⁻¹ * MetaChebyMf x + Real.log x * MetaChebydMf x)

private theorem meta_rpow_le_17 (x : ℝ) (hx : 300 ≤ x) (e : ℝ) (he : e ≤ -(1 / 2 : ℝ)) :
    x ^ e ≤ (1:ℝ)/17 := by
  have hx1 : (1:ℝ) ≤ x := by linarith
  have hx0 : (0:ℝ) ≤ x := by linarith
  have h1 : x ^ e ≤ x ^ (-(1/2):ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 he
  have s289 : Real.sqrt 289 = 17 := by
    rw [show (289:ℝ) = 17^2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hxh : (17:ℝ) ≤ x ^ (1/2:ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← s289]; exact Real.sqrt_le_sqrt (by linarith)
  have h2 : x ^ (-(1/2):ℝ) ≤ 1/17 := by
    rw [Real.rpow_neg hx0, show (1:ℝ)/17 = (17:ℝ)⁻¹ by norm_num]
    gcongr
  linarith

private theorem meta_logrpow_le (x : ℝ) (hx : 300 ≤ x) (e : ℝ) (he : e ≤ -(3 / 4 : ℝ)) :
    Real.log x * x ^ e ≤ 4/17 := by
  have hx0 : (0:ℝ) ≤ x := by linarith
  have hxe : (0:ℝ) ≤ x ^ e := by positivity
  have hlog : Real.log x ≤ 4 * x ^ ((4:ℝ)⁻¹) := by
    have := Real.log_le_rpow_div hx0 (by norm_num : (0:ℝ) < (4:ℝ)⁻¹)
    rw [div_eq_mul_inv, inv_inv] at this
    linarith [this]
  have step : Real.log x * x ^ e ≤ (4 * x ^ ((4:ℝ)⁻¹)) * x ^ e :=
    mul_le_mul_of_nonneg_right hlog hxe
  have comb : (4 * x ^ ((4:ℝ)⁻¹)) * x ^ e = 4 * x ^ ((4:ℝ)⁻¹ + e) := by
    rw [Real.rpow_add (by linarith)]; ring
  have hb : x ^ ((4:ℝ)⁻¹ + e) ≤ (1:ℝ)/17 := meta_rpow_le_17 x hx _ (by linarith)
  calc Real.log x * x ^ e ≤ (4 * x ^ ((4:ℝ)⁻¹)) * x ^ e := step
    _ = 4 * x ^ ((4:ℝ)⁻¹ + e) := comb
    _ ≤ 4 * ((1:ℝ)/17) := by linarith
    _ = 4/17 := by norm_num

private theorem meta_rpow_ub (c : ℝ) (hc : 0 ≤ c) (n : ℕ) (hn : n ≠ 0)
    (h : (300 : ℝ) ≤ c ^ n) : (300:ℝ) ^ ((n:ℝ)⁻¹) ≤ c := by
  have h300 : (300:ℝ) ≤ c ^ (n:ℝ) := by rw [Real.rpow_natCast]; exact h
  have hmono := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 300) h300 (by positivity : (0:ℝ) ≤ (n:ℝ)⁻¹)
  rwa [← Real.rpow_mul hc, mul_inv_cancel₀ (by exact_mod_cast hn), Real.rpow_one] at hmono

private theorem meta_hasDerivAt_LB (x : ℝ) (hx : 0 < x) :
    HasDerivAt MetaChebyLB (MetaChebydLB x) x := by
  have hne : x ≠ 0 := ne_of_gt hx
  have hx2 : x + 2 ≠ 0 := by positivity
  have hP : HasDerivAt MetaChebyPf (MetaChebydPf x) x := by
    have a2 := Real.hasDerivAt_rpow_const (x := x) (p := (2:ℝ)⁻¹) (Or.inl hne)
    have a3 := Real.hasDerivAt_rpow_const (x := x) (p := (3:ℝ)⁻¹) (Or.inl hne)
    have a5 := Real.hasDerivAt_rpow_const (x := x) (p := (5:ℝ)⁻¹) (Or.inl hne)
    exact (a2.add a3).add a5
  have hM : HasDerivAt MetaChebyMf (MetaChebydMf x) x := by
    have a4 := (Real.hasDerivAt_rpow_const (x := x) (p := (4:ℝ)⁻¹) (Or.inl hne)).const_mul (2:ℝ)⁻¹
    have a6 := (Real.hasDerivAt_rpow_const (x := x) (p := (6:ℝ)⁻¹) (Or.inl hne)).const_mul (3:ℝ)⁻¹
    have a10 := (Real.hasDerivAt_rpow_const (x := x) (p := (10:ℝ)⁻¹) (Or.inl hne)).const_mul (5:ℝ)⁻¹
    exact (a4.add a6).add a10
  have hA : HasDerivAt (fun x : ℝ => (x - 1) * Real.log 2) (Real.log 2) x := by
    simpa using ((hasDerivAt_id x).sub_const 1).mul_const (Real.log 2)
  have hB : HasDerivAt (fun x : ℝ => Real.log (x + 2)) ((x + 2)⁻¹) x := by
    have := ((hasDerivAt_id x).add_const 2).log hx2
    simpa using this
  have hC : HasDerivAt (fun x : ℝ => Real.log 4 * MetaChebyPf x) (Real.log 4 * MetaChebydPf x) x :=
    hP.const_mul _
  have hLog2 : HasDerivAt (fun x : ℝ => 2 * Real.log x) (2 * x⁻¹) x :=
    (Real.hasDerivAt_log hne).const_mul 2
  have hD : HasDerivAt (fun x : ℝ => 2 * Real.log x * MetaChebyMf x)
      (2 * (x⁻¹ * MetaChebyMf x + Real.log x * MetaChebydMf x)) x := by
    have := hLog2.mul hM
    convert this using 1
    ring
  exact ((hA.sub hB).sub hC).sub hD

private theorem meta_dLB_gt (x : ℝ) (hx : 300 ≤ x) : (1:ℝ)/3 < MetaChebydLB x := by
  have hx0 : 0 < x := by linarith
  have hl2 : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2' : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; ring
  have hinv : x⁻¹ = x ^ (-1:ℝ) := (Real.rpow_neg_one x).symm
  have e1 : x ^ ((2:ℝ)⁻¹ - 1) ≤ 1/17 := meta_rpow_le_17 x hx _ (by norm_num)
  have e2 : x ^ ((3:ℝ)⁻¹ - 1) ≤ 1/17 := meta_rpow_le_17 x hx _ (by norm_num)
  have e3 : x ^ ((5:ℝ)⁻¹ - 1) ≤ 1/17 := meta_rpow_le_17 x hx _ (by norm_num)
  have m1 : x⁻¹ * x ^ ((4:ℝ)⁻¹) ≤ 1/17 := by
    rw [hinv, ← Real.rpow_add hx0]; exact meta_rpow_le_17 x hx _ (by norm_num)
  have m2 : x⁻¹ * x ^ ((6:ℝ)⁻¹) ≤ 1/17 := by
    rw [hinv, ← Real.rpow_add hx0]; exact meta_rpow_le_17 x hx _ (by norm_num)
  have m3 : x⁻¹ * x ^ ((10:ℝ)⁻¹) ≤ 1/17 := by
    rw [hinv, ← Real.rpow_add hx0]; exact meta_rpow_le_17 x hx _ (by norm_num)
  have l1 : Real.log x * x ^ ((4:ℝ)⁻¹ - 1) ≤ 4/17 := meta_logrpow_le x hx _ (by norm_num)
  have l2 : Real.log x * x ^ ((6:ℝ)⁻¹ - 1) ≤ 4/17 := meta_logrpow_le x hx _ (by norm_num)
  have l3 : Real.log x * x ^ ((10:ℝ)⁻¹ - 1) ≤ 4/17 := meta_logrpow_le x hx _ (by norm_num)
  have keyM : x⁻¹ * MetaChebyMf x
      = (2:ℝ)⁻¹ * (x⁻¹ * x ^ ((4:ℝ)⁻¹)) + (3:ℝ)⁻¹ * (x⁻¹ * x ^ ((6:ℝ)⁻¹))
        + (5:ℝ)⁻¹ * (x⁻¹ * x ^ ((10:ℝ)⁻¹)) := by unfold MetaChebyMf; ring
  have keyD : Real.log x * MetaChebydMf x
      = (2:ℝ)⁻¹ * ((4:ℝ)⁻¹ * (Real.log x * x ^ ((4:ℝ)⁻¹ - 1)))
        + (3:ℝ)⁻¹ * ((6:ℝ)⁻¹ * (Real.log x * x ^ ((6:ℝ)⁻¹ - 1)))
        + (5:ℝ)⁻¹ * ((10:ℝ)⁻¹ * (Real.log x * x ^ ((10:ℝ)⁻¹ - 1))) := by unfold MetaChebydMf; ring
  have hdPf0 : 0 ≤ MetaChebydPf x := by unfold MetaChebydPf; positivity
  have hxinv : (x + 2)⁻¹ ≤ 1/302 := by
    rw [show (1:ℝ)/302 = (302:ℝ)⁻¹ by norm_num]; gcongr; linarith
  unfold MetaChebydLB
  rw [keyM, keyD, hl4]
  unfold MetaChebydPf
  nlinarith [e1, e2, e3, m1, m2, m3, l1, l2, l3, hl2, hl2', hxinv,
    mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (le_of_lt (lt_trans (by norm_num) hl2)))
      hdPf0]

private theorem meta_LB_300 : (100:ℝ) < MetaChebyLB 300 := by
  have b2 : (300:ℝ) ^ ((2:ℝ)⁻¹) ≤ 17.34 := by
    have := meta_rpow_ub 17.34 (by norm_num) 2 (by norm_num) (by norm_num); simpa using this
  have b3 : (300:ℝ) ^ ((3:ℝ)⁻¹) ≤ 6.7 := by
    have := meta_rpow_ub 6.7 (by norm_num) 3 (by norm_num) (by norm_num); simpa using this
  have b5 : (300:ℝ) ^ ((5:ℝ)⁻¹) ≤ 3.13 := by
    have := meta_rpow_ub 3.13 (by norm_num) 5 (by norm_num) (by norm_num); simpa using this
  have b4 : (300:ℝ) ^ ((4:ℝ)⁻¹) ≤ 4.2 := by
    have := meta_rpow_ub 4.2 (by norm_num) 4 (by norm_num) (by norm_num); simpa using this
  have b6 : (300:ℝ) ^ ((6:ℝ)⁻¹) ≤ 2.6 := by
    have := meta_rpow_ub 2.6 (by norm_num) 6 (by norm_num) (by norm_num); simpa using this
  have b10 : (300:ℝ) ^ ((10:ℝ)⁻¹) ≤ 1.8 := by
    have := meta_rpow_ub 1.8 (by norm_num) 10 (by norm_num) (by norm_num); simpa using this
  have hexp6 : (302:ℝ) < Real.exp 6 := by
    have he : (2.7182818283:ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have hpow : (2.7182818283:ℝ) ^ (6:ℕ) ≤ (Real.exp 1) ^ (6:ℕ) := by gcongr
    have heq : (Real.exp 1) ^ (6:ℕ) = Real.exp 6 := by rw [← Real.exp_nat_mul]; norm_num
    have hnum : (302:ℝ) < (2.7182818283:ℝ) ^ (6:ℕ) := by norm_num
    rw [← heq]; linarith
  have hlog300 : Real.log 300 < 6 := by rw [Real.log_lt_iff_lt_exp (by norm_num)]; linarith
  have hlog302 : Real.log 302 < 6 := by rw [Real.log_lt_iff_lt_exp (by norm_num)]; exact hexp6
  have hl2 : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2' : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; ring
  have hlog300pos : 0 ≤ Real.log 300 := Real.log_nonneg (by norm_num)
  unfold MetaChebyLB MetaChebyPf MetaChebyMf
  rw [hl4]
  nlinarith [b2, b3, b5, b4, b6, b10, hlog300, hlog302, hl2, hl2', hlog300pos,
    Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 300) ((2:ℝ)⁻¹),
    Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 300) ((4:ℝ)⁻¹),
    Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 300) ((6:ℝ)⁻¹),
    Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 300) ((10:ℝ)⁻¹)]

private theorem meta_LB_tail (x : ℝ) (hx : 300 ≤ x) : x / 3 < MetaChebyLB x := by
  set G : ℝ → ℝ := fun x => MetaChebyLB x - x / 3 with hG
  have hderivG : ∀ y : ℝ, 0 < y → HasDerivAt G (MetaChebydLB y - 1 / 3) y := by
    intro y hy
    have h1 := meta_hasDerivAt_LB y hy
    have h2 : HasDerivAt (fun x : ℝ => x / 3) (1 / 3) y := by
      simpa using (hasDerivAt_id y).div_const 3
    exact h1.sub h2
  have hcont : ContinuousOn G (Set.Ici 300) := by
    intro y hy
    have hy0 : 0 < y := by rw [Set.mem_Ici] at hy; linarith
    exact ((hderivG y hy0).continuousAt).continuousWithinAt
  have hmono : StrictMonoOn G (Set.Ici 300) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 300) hcont
    intro y hy
    rw [interior_Ici, Set.mem_Ioi] at hy
    have hy0 : 0 < y := by linarith
    rw [(hderivG y hy0).deriv]
    have := meta_dLB_gt y (le_of_lt hy)
    linarith
  have hG300 : 0 < G 300 := by simp only [hG]; have := meta_LB_300; norm_num; linarith
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h]; simp only [hG] at hG300; linarith
  · have hlt := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (le_of_lt h)) h
    simp only [hG] at hlt hG300; linarith

private theorem meta_psi_le_conv (x : ℝ) (hx : 1 ≤ x) (a : ℝ) (ha : 0 ≤ a) :
    Chebyshev.psi (x ^ a) ≤ Real.log 4 * x ^ a + 2 * x ^ (a / 2) * (a * Real.log x) := by
  have hx0 : 0 < x := by linarith
  have h1 : (1:ℝ) ≤ x ^ a := Real.one_le_rpow hx ha
  have := Chebyshev.psi_le h1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hx0), Real.log_rpow hx0] at this
  rw [show a * (1/2) = a / 2 by ring] at this
  exact this

private theorem meta_theta_ge_LB (x : ℝ) (hx : 1 ≤ x) : MetaChebyLB x ≤ Chebyshev.theta x := by
  have hx0 : 0 < x := by linarith
  have hx0' : (0:ℝ) ≤ x := by linarith
  have key : Chebyshev.theta x = Chebyshev.psi x - (Chebyshev.psi x - Chebyshev.theta x) := by ring
  have hsub : Chebyshev.psi x - Chebyshev.theta x
      ≤ Chebyshev.psi (x ^ (2:ℝ)⁻¹) + Chebyshev.psi (x ^ (3:ℝ)⁻¹) + Chebyshev.psi
          (x ^ (5:ℝ)⁻¹) := by
    have := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
    simpa using this
  have hpsi : (x - 1) * Real.log 2 - Real.log (x + 2) ≤ Chebyshev.psi x := Chebyshev.psi_ge' hx0'
  have p2 := meta_psi_le_conv x hx (2:ℝ)⁻¹ (by norm_num)
  have p3 := meta_psi_le_conv x hx (3:ℝ)⁻¹ (by norm_num)
  have p5 := meta_psi_le_conv x hx (5:ℝ)⁻¹ (by norm_num)
  rw [show (2:ℝ)⁻¹ / 2 = (4:ℝ)⁻¹ by norm_num] at p2
  rw [show (3:ℝ)⁻¹ / 2 = (6:ℝ)⁻¹ by norm_num] at p3
  rw [show (5:ℝ)⁻¹ / 2 = (10:ℝ)⁻¹ by norm_num] at p5
  rw [key]
  unfold MetaChebyLB MetaChebyPf MetaChebyMf
  nlinarith [hsub, hpsi, p2, p3, p5]

private theorem meta_ckpt (n k : ℕ) (h : 2 ^ k ≤ primorial n) :
    (k : ℝ) * 0.6931471803 ≤ Chebyshev.theta (n : ℝ) := by
  rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast]
  have h1 : (2:ℝ) ^ k ≤ (primorial n : ℝ) := by exact_mod_cast h
  have h2 : Real.log ((2:ℝ) ^ k) ≤ Real.log (primorial n : ℝ) :=
    Real.log_le_log (by positivity) h1
  rw [Real.log_pow] at h2
  have h3 : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
  nlinarith [h2, h3, Nat.cast_nonneg (α := ℝ) k]

private theorem meta_theta3 : (5:ℝ)/3 ≤ Chebyshev.theta (3:ℝ) := by
  rw [Chebyshev.theta_eq_log_primorial, show ⌊(3:ℝ)⌋₊ = 3 by norm_num]
  have hp3 : primorial 3 = 6 := by decide
  rw [hp3]
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h1 : Real.exp (5/3) ^ 3 = Real.exp 5 := by rw [← Real.exp_nat_mul]; norm_num
  have h2 : Real.exp 5 < 6 ^ 3 := by
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have heq : Real.exp 5 = (Real.exp 1) ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
    have hpow : (Real.exp 1) ^ 5 ≤ (2.7182818286:ℝ) ^ 5 := by gcongr
    rw [heq]; nlinarith [hpow]
  have h3 : Real.exp (5/3) ^ 3 < 6 ^ 3 := by rw [h1]; exact h2
  have := lt_of_pow_lt_pow_left₀ 3 (by norm_num : (0:ℝ) ≤ 6) h3
  push_cast at this ⊢
  linarith

private theorem meta_interval (a b v x : ℝ) (hv : v ≤ Chebyshev.theta a) (hcov : b ≤ 3 * v)
    (hx1 : a ≤ x) (hx2 : x < b) : x / 3 < Chebyshev.theta x := by
  have hmono : Chebyshev.theta a ≤ Chebyshev.theta x := Chebyshev.theta_mono hx1
  linarith

private theorem meta_finite (x : ℝ) (h3 : 3 ≤ x) (h300 : x < 300) :
    x / 3 < Chebyshev.theta x := by
  have c5 : (4:ℝ) * 0.6931471803 ≤ Chebyshev.theta (5:ℝ) := by
    have := meta_ckpt 5 4 (by norm_num [primorial, Finset.prod_filter, Finset.prod_range_succ])
    exact_mod_cast this
  have c8 : (7:ℝ) * 0.6931471803 ≤ Chebyshev.theta (8:ℝ) := by
    have := meta_ckpt 8 7 (by norm_num [primorial, Finset.prod_filter, Finset.prod_range_succ])
    exact_mod_cast this
  have c13 : (14:ℝ) * 0.6931471803 ≤ Chebyshev.theta (13:ℝ) := by
    have := meta_ckpt 13 14 (by norm_num [primorial, Finset.prod_filter, Finset.prod_range_succ])
    exact_mod_cast this
  have c29 : (32:ℝ) * 0.6931471803 ≤ Chebyshev.theta (29:ℝ) := by
    have := meta_ckpt 29 32 (by norm_num [primorial, Finset.prod_filter, Finset.prod_range_succ])
    exact_mod_cast this
  have c55 : (64:ℝ) * 0.6931471803 ≤ Chebyshev.theta (55:ℝ) := by
    have := meta_ckpt 55 64 (by norm_num [primorial, Finset.prod_filter, Finset.prod_range_succ])
    exact_mod_cast this
  have c97 : (120:ℝ) * 0.6931471803 ≤ Chebyshev.theta (97:ℝ) := by
    have := meta_ckpt 97 120 (by norm_num [primorial, Finset.prod_filter, Finset.prod_range_succ])
    exact_mod_cast this
  have c140 : (182:ℝ) * 0.6931471803 ≤ Chebyshev.theta (140:ℝ) := by
    have := meta_ckpt 140 182 (by norm_num [primorial, Finset.prod_filter, Finset.prod_range_succ])
    exact_mod_cast this
  rcases lt_or_ge x 5 with h | h5
  · exact meta_interval 3 5 (5/3) x meta_theta3 (by norm_num) h3 h
  rcases lt_or_ge x 8 with h | h8
  · exact meta_interval 5 8 _ x c5 (by norm_num) h5 h
  rcases lt_or_ge x 13 with h | h13
  · exact meta_interval 8 13 _ x c8 (by norm_num) h8 h
  rcases lt_or_ge x 29 with h | h29
  · exact meta_interval 13 29 _ x c13 (by norm_num) h13 h
  rcases lt_or_ge x 55 with h | h55
  · exact meta_interval 29 55 _ x c29 (by norm_num) h29 h
  rcases lt_or_ge x 97 with h | h97
  · exact meta_interval 55 97 _ x c55 (by norm_num) h55 h
  rcases lt_or_ge x 140 with h | h140
  · exact meta_interval 97 140 _ x c97 (by norm_num) h97 h
  · exact meta_interval 140 300 _ x c140 (by norm_num) h140 h300

section
namespace MetaMathlibExt

/-- **Chebyshev's lower bound for the theta function.** Let $\theta(x) = \sum_{p \le x} \log p$, the
sum running over primes, be the first Chebyshev function. Then $\theta(x) > x/3$ for every real
$x \ge 3$.

Source: Sadegh Nazardonyavi and Semyon Yakubovich, "Extremely Abundant
Numbers", Journal of Integer Sequences 17 (2014), Corollary
`chebyshev's-result`, lines 302--306,
<https://cs.uwaterloo.ca/journals/JIS/VOL17/Nazar/nazar4.tex>.

Proves `Wanted` entry `chebyshev_theta_gt_one_third`.
-/
theorem chebyshev_theta_gt_one_third
    (x : ℝ) (hx : 3 ≤ x) :
    x / 3 < Chebyshev.theta x := by
  rcases lt_or_ge x 300 with h | h
  · exact meta_finite x hx h
  · calc x / 3 < MetaChebyLB x := meta_LB_tail x h
      _ ≤ Chebyshev.theta x := meta_theta_ge_LB x (by linarith)

end MetaMathlibExt
