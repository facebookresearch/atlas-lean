/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.PSeries

@[expose] public section

namespace MathlibExt.Analysis.SpecialFunctions.CatalanSqrtTwo

open scoped Topology
open Finset Nat Filter Real

/-- Catalan's product term: `(4m+2)^2 / ((4m+1) * (4m+3))`. -/
private noncomputable def catalanTerm (m : ℕ) : ℝ :=
  (((4 * m + 2 : ℕ) : ℝ) ^ 2) /
    (((4 * m + 1 : ℕ) : ℝ) * ((4 * m + 3 : ℕ) : ℝ))

/-- Partial products equal an explicit factorial ratio. -/
private theorem catalan_partial_eq (N : ℕ) :
    ∏ m ∈ Finset.range N, catalanTerm m =
      2 ^ (2 * N) * ((2 * N) ! : ℝ) ^ 3 / (((N ! : ℝ) ^ 2 * (4 * N) !)) := by
  induction N with
  | zero => simp [catalanTerm]
  | succ N IH =>
    rw [Finset.prod_range_succ, IH]
    have e2 : (2 * (N + 1) : ℕ) = 2 * N + 2 := by ring
    have e4 : (4 * (N + 1) : ℕ) = 4 * N + 4 := by ring
    rw [e2, e4, pow_add]
    rw [show (2 * N + 2 : ℕ) = (2 * N + 1) + 1 from by ring,
      show (4 * N + 4 : ℕ) = (4 * N + 3) + 1 from by ring]
    simp only [Nat.factorial_succ]
    unfold catalanTerm
    have h41 : ((4 * N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have h43 : ((4 * N + 3 : ℕ) : ℝ) ≠ 0 := by positivity
    have hN : ((N ! : ℕ) : ℝ) ≠ 0 := by positivity
    have h2N : (((2 * N)! : ℕ) : ℝ) ≠ 0 := by positivity
    have h4N : (((4 * N)! : ℕ) : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-- Partial products via the Stirling sequence. -/
private theorem catalan_stirling_eq (N : ℕ) (hN : N ≠ 0) :
    Stirling.stirlingSeq (2 * N) ^ 3 /
        (Stirling.stirlingSeq N ^ 2 * Stirling.stirlingSeq (4 * N)) * √2 =
      ∏ m ∈ Finset.range N, catalanTerm m := by
  rw [catalan_partial_eq, Stirling.stirlingSeq, Stirling.stirlingSeq,
    Stirling.stirlingSeq]
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have h4 : (0 : ℝ) ≤ 4 := by norm_num
  have q4 : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have sqN : (√(N : ℝ)) ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg _)
  have sq2 : (√2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have sqN3 : (√(N : ℝ)) ^ 3 = N * √(N : ℝ) := by rw [pow_succ, sqN]
  have sq23 : (√2) ^ 3 = 2 * √2 := by rw [pow_succ, sq2]
  push_cast
  simp only [Real.sqrt_mul h2, Real.sqrt_mul h4, q4, div_pow, mul_pow, sqN3, sq23,
    sqN, sq2]
  have hfact : ∀ k : ℕ, (((k ! : ℕ)) : ℝ) ≠ 0 := fun k => by positivity
  have hsqrtN : √(N : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hN'
  have hsqrt2 : √2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have hexp : Real.exp 1 ≠ 0 := Real.exp_ne_zero _
  have h48 : (4 : ℝ) ^ (N * 4) = 2 ^ (N * 8) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    congr 1
    ring
  field_simp
  ring_nf
  rw [h48]

/-- Partial products tend to `√2`. -/
private theorem catalan_tendsto :
    Tendsto (fun N => ∏ m ∈ Finset.range N, catalanTerm m) atTop (𝓝 √2) := by
  have h2 : Tendsto (fun N => Stirling.stirlingSeq (2 * N)) atTop (𝓝 √π) :=
    Stirling.tendsto_stirlingSeq_sqrt_pi.comp
      (tendsto_id.const_mul_atTop' two_pos)
  have h1 : Tendsto (fun N => Stirling.stirlingSeq N) atTop (𝓝 √π) :=
    Stirling.tendsto_stirlingSeq_sqrt_pi.comp tendsto_id
  have h4 : Tendsto (fun N => Stirling.stirlingSeq (4 * N)) atTop (𝓝 √π) :=
    Stirling.tendsto_stirlingSeq_sqrt_pi.comp
      (tendsto_id.const_mul_atTop' (show (0 : ℕ) < 4 by norm_num))
  have hlim : (√π) ^ 3 / ((√π) ^ 2 * √π) = 1 := by
    have hpi : √π ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
    field_simp
  have hratio : Tendsto (fun N => Stirling.stirlingSeq (2 * N) ^ 3 /
      (Stirling.stirlingSeq N ^ 2 * Stirling.stirlingSeq (4 * N))) atTop
      (𝓝 1) := by
    have hpi : √π ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
    have hden : (√π) ^ 2 * √π ≠ 0 := mul_ne_zero (pow_ne_zero 2 hpi) hpi
    have h := (h2.pow 3).div ((h1.pow 2).mul h4) hden
    rw [hlim] at h
    exact h.congr (fun N => rfl)
  have heq : (fun N => ∏ m ∈ Finset.range N, catalanTerm m) =ᶠ[atTop]
      (fun N => Stirling.stirlingSeq (2 * N) ^ 3 /
        (Stirling.stirlingSeq N ^ 2 * Stirling.stirlingSeq (4 * N)) * √2) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [catalan_stirling_eq N (by omega : N ≠ 0)]
  have hmain : Tendsto (fun N => Stirling.stirlingSeq (2 * N) ^ 3 /
      (Stirling.stirlingSeq N ^ 2 * Stirling.stirlingSeq (4 * N)) * √2) atTop
      (𝓝 √2) := by
    have h := hratio.mul (tendsto_const_nhds (x := √2))
    rwa [one_mul] at h
  exact Tendsto.congr' heq.symm hmain

/-- The Catalan terms are multipliable. -/
private theorem catalan_multipliable : Multipliable catalanTerm := by
  have h1 : ∀ m : ℕ, catalanTerm m =
      1 + (1 / ((((4 * m + 1 : ℕ) : ℝ) * ((4 * m + 3 : ℕ) : ℝ)))) := by
    intro m
    unfold catalanTerm
    have h41 : ((4 * m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have h43 : ((4 * m + 3 : ℕ) : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  rw [multipliable_congr h1]
  apply multipliable_one_add_of_summable
  have hbase : Summable fun m : ℕ => (1 : ℝ) / ((((m + 1 : ℕ)) : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num))
  apply Summable.of_nonneg_of_le (fun m => norm_nonneg _) _ hbase
  intro m
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  push_cast
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have e1 : (m : ℝ) + 1 ≤ 4 * (m : ℝ) + 1 := by linarith
  have e2 : (4 : ℝ) * (m : ℝ) + 1 ≤ 4 * (m : ℝ) + 3 := by linarith
  have g1 : ((m : ℝ) + 1) ^ 2 ≤ (4 * (m : ℝ) + 1) ^ 2 :=
    sq_le_sq' (by linarith) e1
  have g2 : (4 * (m : ℝ) + 1) ^ 2 ≤ (4 * (m : ℝ) + 1) * (4 * (m : ℝ) + 3) := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left e2 (by positivity)
  exact one_div_le_one_div_of_le (by positivity) (le_trans g1 g2)

/-- **Catalan's product for $\sqrt{2}$.** The infinite product over all natural numbers $m \ge 0$
of $\frac{(4m+2)^2}{(4m+1)(4m+3)}$ converges unconditionally to $\sqrt{2}$; that is,
$\frac{2 \cdot 2}{1 \cdot 3} \cdot \frac{6 \cdot 6}{5 \cdot 7} \cdot \frac{10 \cdot 10}{9 \cdot 11}
\cdots = \sqrt{2}$.

Source: László Tóth, Journal of Integer Sequences 23, `toth46.tex`, lines 157-161.
URL: <https://cs.uwaterloo.ca/journals/JIS/VOL23/Toth/toth46.tex>.
Source SHA-256 `0501cfe88006efcee189af624a51343823bb18009d904b37ec97f9798696974e`. -/
public theorem catalan_hasProd_sqrt_two :
    HasProd (fun m : Nat =>
      (((4 * m + 2 : Nat) : Real) ^ 2) /
        (((4 * m + 1 : Nat) : Real) * ((4 * m + 3 : Nat) : Real)))
      (Real.sqrt 2) := by
  exact (Multipliable.hasProd_iff_tendsto_nat catalan_multipliable).mpr catalan_tendsto

end MathlibExt.Analysis.SpecialFunctions.CatalanSqrtTwo
