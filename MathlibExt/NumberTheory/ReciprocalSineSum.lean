/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import MathlibExt.NumberTheory.IncompleteExponentialSum
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Finset.Sort
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# A bound for a sum of reciprocal sines

We prove Cochrane's bound for a sum of reciprocal absolute sines modulo a prime. The proof
orders the distinct least absolute residues and applies the pointwise cosecant bound.
-/

namespace MetaMathlibExt

open Finset

namespace sum_one_div_abs_sin_lt

open Filter

/-- The harmonic number differs from `log n + γ` by at most `1 / (2 * n)` on the upper side. -/
private lemma harmonic_le_log_add_gamma (n : ℕ) (hn : 0 < n) :
    (harmonic n : ℝ) ≤ Real.log n + Real.eulerMascheroniConstant + 1 / (2 * n) := by
  let u (k : ℕ) : ℝ :=
    (harmonic (k + 1) : ℝ) - Real.log (↑(k + 1 : ℕ)) - 1 / (2 * ↑(k + 1 : ℕ))
  have hu : Monotone u := by
    apply monotone_nat_of_le_succ
    intro k
    let x : ℝ := (k : ℝ) + 1
    have hx : 0 < x := by dsimp [x]; positivity
    have hx₁ : 0 < x + 1 := by positivity
    have hratio : 1 ≤ (x + 1) / x := (le_div_iff₀ hx).2 (by linarith)
    have hlog := Real.self_le_sinh_iff.mpr (Real.log_nonneg hratio)
    rw [Real.sinh_log (by positivity), Real.log_div hx₁.ne' hx.ne'] at hlog
    have hidentity : ((x + 1) / x - ((x + 1) / x)⁻¹) / 2 =
        1 / (2 * x) + 1 / (2 * (x + 1)) := by
      field_simp
      ring
    rw [hidentity] at hlog
    have hhalf : 1 / (x + 1) = 1 / (2 * (x + 1)) + 1 / (2 * (x + 1)) := by
      field_simp
      ring
    dsimp only [u]
    rw [harmonic_succ (k + 1)]
    push_cast
    change (harmonic (k + 1) : ℝ) - Real.log x - 1 / (2 * x) ≤
      (harmonic (k + 1) : ℝ) + (x + 1)⁻¹ - Real.log (x + 1) - 1 / (2 * (x + 1))
    rw [← one_div, hhalf]
    linarith
  have hlim : Tendsto u atTop (nhds Real.eulerMascheroniConstant) := by
    have hmain := Real.tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)
    have hinv : Tendsto (fun k : ℕ ↦ (1 / (2 * ((k : ℝ) + 1)) : ℝ))
        atTop (nhds 0) := by
      simpa [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm] using
        (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)⁻¹)
    simpa [u, Function.comp_def, Nat.cast_add, Nat.cast_one] using hmain.sub hinv
  have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have h : (harmonic n : ℝ) - Real.log n - 1 / (2 * n) ≤ Real.eulerMascheroniConstant := by
    simpa only [u, hn'] using hu.ge_of_tendsto hlim (n - 1)
  linarith only [h]

/-- Absolute sine with argument `π x / p` only depends on the residue of the integer `x`. -/
private lemma abs_sin_eq_of_zmod_eq {p : ℕ} (hp : 0 < p) {x y : ℤ}
    (h : (x : ZMod p) = y) :
    |Real.sin (Real.pi * x / p)| = |Real.sin (Real.pi * y / p)| := by
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub x y p).mp h
  have hxy : (y : ℝ) - x = p * (k : ℝ) := by exact_mod_cast hk
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have harg : Real.pi * y / p = Real.pi * x / p + (k : ℝ) * Real.pi := by
    field_simp
    linear_combination hxy
  rw [harg, Real.sin_add_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul]

/-- Sorting the least absolute residues of `a h` bounds the sum by the case `a = 1`. -/
private lemma sum_le_unmultiplied (p : ℕ) (hp : p.Prime) (a : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) (B : ℕ) (hB : 2 * B < p) :
    ∑ h ∈ Icc 1 B, 1 / |Real.sin (Real.pi * a * h / p)| ≤
      ∑ j ∈ Icc 1 B, 1 / Real.sin (Real.pi * j / p) := by
  let : Fact p.Prime := ⟨hp⟩
  let z (h : ℕ) : ZMod p := (a : ZMod p) * (h : ZMod p)
  let r (h : ℕ) : ℕ := (z h).valMinAbs.natAbs
  have ha' : (a : ZMod p) ≠ 0 := fun h ↦ ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).1 h)
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpi := Real.pi_pos
  have hr (h : ℕ) (hh : h ∈ Icc 1 B) : 0 < r h ∧ r h ≤ p / 2 := by
    obtain ⟨hh₁, hhB⟩ := mem_Icc.mp hh
    refine ⟨Nat.pos_of_ne_zero ?_, (z h).natAbs_valMinAbs_le⟩
    intro hz
    have hhzero : (h : ZMod p) = 0 := (mul_eq_zero.mp
      ((z h).valMinAbs_eq_zero.mp (Int.natAbs_eq_zero.mp hz))).resolve_left ha'
    have hval := congrArg ZMod.val hhzero
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hval
    omega
  have hrinj : Set.InjOn r (↑(Icc 1 B) : Set ℕ) := by
    intro i hi j hj hij
    obtain ⟨hi₁, hiB⟩ := mem_Icc.mp (mem_coe.mp hi)
    obtain ⟨hj₁, hjB⟩ := mem_Icc.mp (mem_coe.mp hj)
    rcases ZMod.natAbs_valMinAbs_eq_natAbs_valMinAbs.mp hij with h | h
    · have hval := congrArg ZMod.val (mul_left_cancel₀ ha' h)
      simpa only [ZMod.val_natCast_of_lt (show i < p by omega),
        ZMod.val_natCast_of_lt (show j < p by omega)] using hval
    · have hneg : (i : ZMod p) = -(j : ZMod p) :=
        mul_left_cancel₀ ha' (by simpa only [mul_neg] using h)
      have hzero : ((i + j : ℕ) : ZMod p) = 0 := by simp [hneg]
      have hval := congrArg ZMod.val hzero
      rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hval
      omega
  let f (j : ℕ) := 1 / Real.sin (Real.pi * j / p)
  have harg (j : ℕ) (hj : j ≤ p / 2) : Real.pi * j / p ≤ Real.pi / 2 := by
    have hj' : (j : ℝ) * 2 ≤ p := by exact_mod_cast Nat.le_div_two_iff_mul_two_le.mp hj
    rw [div_le_iff₀ hp']
    nlinarith [mul_le_mul_of_nonneg_left hj' hpi.le]
  have hterm (h : ℕ) (hh : h ∈ Icc 1 B) :
      1 / |Real.sin (Real.pi * a * h / p)| = f (r h) := by
    have hcast : ((a * (h : ℤ) : ℤ) : ZMod p) = (z h).valMinAbs := by simp [z]
    have hsin := abs_sin_eq_of_zmod_eq hp.pos hcast
    push_cast at hsin
    rw [← mul_assoc] at hsin
    have habs : |Real.pi * ((z h).valMinAbs : ℝ) / p| = Real.pi * (r h : ℝ) / p := by
      rw [abs_div, abs_mul, abs_of_pos hpi, abs_of_pos hp', ← Int.cast_abs, Int.abs_eq_natAbs]
      rfl
    rw [hsin, Real.abs_sin_eq_sin_abs_of_abs_le_pi, habs]
    exact (habs.trans_le (harg _ (hr h hh).2)).trans (by linarith)
  have hf : AntitoneOn f (Set.Icc 1 (p / 2)) := by
    intro i hi j hj hij
    have hi₀ : (0 : ℝ) < i := by exact_mod_cast (show 0 < i from hi.1)
    have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
    apply one_div_le_one_div_of_le
    · exact Real.sin_pos_of_pos_of_lt_pi (by positivity) ((harg i hi.2).trans_lt (by linarith))
    · have hz : (0 : ℝ) ≤ Real.pi * i / p := by positivity
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (harg j hj.2) (by gcongr)
  let s := (Icc 1 B).image r
  have hs : s.card = B := by rw [card_image_of_injOn hrinj]; simp
  let e := s.orderEmbOfFin hs
  have he (i : Fin B) : 0 < e i ∧ e i ≤ p / 2 := by
    obtain ⟨h, hh, heq⟩ := mem_image.mp (s.orderEmbOfFin_mem hs i)
    simpa only [e, ← heq] using hr h hh
  have hindex (i : Fin B) : (i : ℕ) + 1 ≤ e i := by
    have hcard := card_le_card_of_injOn (s := Iic i) (t := Icc 1 (e i)) e
      (fun j hj ↦ mem_coe.mpr (mem_Icc.mpr
        ⟨(he j).1, e.monotone (mem_Iic.mp (mem_coe.mp hj))⟩)) e.injective.injOn
    simpa only [Fin.card_Iic, Nat.card_Icc, Nat.add_sub_cancel] using hcard
  have hIcc : (Icc 1 B).card = B := by simp
  have hshift : ((Icc 1 B).orderEmbOfFin hIcc : Fin B → ℕ) = fun (i : Fin B) ↦ (i : ℕ) + 1 :=
    (orderEmbOfFin_unique hIcc (fun i ↦ mem_Icc.mpr ⟨by omega, i.isLt⟩)
      (fun _ _ hij ↦ Nat.add_lt_add_right hij 1)).symm
  calc
    _ = ∑ j ∈ s, f j := by
      rw [sum_image hrinj]
      exact sum_congr rfl hterm
    _ = ∑ i : Fin B, f (e i) := by
      rw [← s.map_orderEmbOfFin_univ hs, sum_map]
      rfl
    _ ≤ ∑ i : Fin B, f ((i : ℕ) + 1) := by
      apply sum_le_sum
      intro i _
      exact hf ⟨by omega, (hindex i).trans (he i).2⟩ (he i) (hindex i)
    _ = ∑ j ∈ Icc 1 B, f j := by
      rw [← (Icc 1 B).map_orderEmbOfFin_univ hIcc, sum_map]
      exact sum_congr rfl fun i _ ↦ (congrArg f (congrFun hshift i)).symm

end sum_one_div_abs_sin_lt

/-- **Bound for a sum of reciprocal sines.** Let $p$ be a prime, let $a$ be an integer not
divisible by $p$, let $B$ be an integer with $1 \le B < p/2$, and let $\gamma$ be the
Euler–Mascheroni constant. Then
$$
\sum_{h=1}^{B} \frac{1}{|\sin(\pi a h / p)|} <
\frac{p}{\pi}\left(\log B + \gamma + \frac{1}{2B}\right) + \frac{pB(B+1)}{\pi(p^2 - B^2)}.
$$

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Lemma 3.2 (`integers-2025-A48-lem-3-2`). -/
public theorem sum_one_div_abs_sin_lt (p : ℕ) (hp : p.Prime) (a : ℤ)
    (ha : ¬ (p : ℤ) ∣ a) (B : ℕ) (hB₁ : 1 ≤ B) (hB : (B : ℝ) < p / 2) :
    ∑ h ∈ Icc 1 B, 1 / |Real.sin (Real.pi * a * h / p)| <
      (p / Real.pi) * (Real.log B + Real.eulerMascheroniConstant + 1 / (2 * B)) +
        p * B * (B + 1) / (Real.pi * ((p : ℝ) ^ 2 - (B : ℝ) ^ 2)) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpπ : 0 < (p : ℝ) / Real.pi := by positivity
  have hB' : (B : ℝ) < p := by linarith
  have hB₂ : 2 * B < p := by exact_mod_cast (show 2 * (B : ℝ) < p by linarith)
  have hBsq : 0 < (p : ℝ) ^ 2 - (B : ℝ) ^ 2 := by
    apply sub_pos.mpr
    gcongr
  have hpoint (j : ℕ) (hj : j ∈ Icc 1 B) :
      1 / Real.sin (Real.pi * j / p) <
        (p / Real.pi) * (j : ℝ)⁻¹ + (2 * p / (Real.pi * ((p : ℝ) ^ 2 - B ^ 2))) * j := by
    obtain ⟨hj₁, hjB⟩ := mem_Icc.mp hj
    have hj₀ : (0 : ℝ) < j := by exact_mod_cast (show 0 < j from hj₁)
    have hjB' : (j : ℝ) ≤ B := by exact_mod_cast hjB
    have hjp : (j : ℝ) < p := hjB'.trans_lt hB'
    have hjsq : 0 < (p : ℝ) ^ 2 - (j : ℝ) ^ 2 := by
      apply sub_pos.mpr
      gcongr
    calc
      _ < (1 / Real.pi) * (1 / ((j : ℝ) / p) +
          2 * ((j : ℝ) / p) / (1 - ((j : ℝ) / p) ^ 2)) := by
        rw [mul_div_assoc]
        exact one_div_sin_pi_lt _ (by positivity) ((div_lt_one hp').mpr hjp)
      _ = (p / Real.pi) * (j : ℝ)⁻¹ +
          (2 * p / (Real.pi * ((p : ℝ) ^ 2 - (j : ℝ) ^ 2))) * j := by
        have : 1 - ((j : ℝ) / p) ^ 2 ≠ 0 := by
          rw [div_pow, sub_ne_zero]
          exact ((div_lt_one (by positivity)).mpr (sub_pos.mp hjsq)).ne'
        field_simp
      _ ≤ _ := by gcongr
  have hsum (n : ℕ) : ∑ j ∈ Icc 1 n, (j : ℝ) = n * (n + 1) / 2 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_Icc_succ_top (by omega), ih]
      push_cast
      ring
  calc
    _ ≤ ∑ j ∈ Icc 1 B, 1 / Real.sin (Real.pi * j / p) :=
      sum_one_div_abs_sin_lt.sum_le_unmultiplied p hp a ha B hB₂
    _ < ∑ j ∈ Icc 1 B,
        ((p / Real.pi) * (j : ℝ)⁻¹ + (2 * p / (Real.pi * ((p : ℝ) ^ 2 - B ^ 2))) * j) :=
      sum_lt_sum_of_nonempty (nonempty_Icc.mpr hB₁) hpoint
    _ = (p / Real.pi) * (harmonic B : ℝ) +
        p * B * (B + 1) / (Real.pi * ((p : ℝ) ^ 2 - (B : ℝ) ^ 2)) := by
      simp only [sum_add_distrib, ← mul_sum, hsum, harmonic_eq_sum_Icc, Rat.cast_sum,
        Rat.cast_inv, Rat.cast_natCast]
      ring
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (sum_one_div_abs_sin_lt.harmonic_le_log_add_gamma B hB₁) hpπ.le)
      le_rfl

end MetaMathlibExt
